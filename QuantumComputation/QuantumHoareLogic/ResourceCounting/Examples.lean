/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import QuantumComputation.QuantumHoareLogic.ResourceCounting.CostBounds
import QuantumComputation.QuantumHoareLogic.ResourceCounting.Additivity
import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops

/-! # A short example file showing how to use the resource-counting framework. -/

@[expose] public section

open Operator QProg QProg.Notation
open scoped Matrix NNReal
open Store (Expr)

namespace ResourceCounting.Examples

variable {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]

/-- Example resource policy charging every kind of primitive operation. -/
def weightedModel (d : ℕ) : CostModel d where
  assignmentCost := 2
  resetCost := 3
  measurementCost := fun _ ↦ 5
  unitaryCost := fun _ ↦ 7

/-- A simple straight-line program combining reset, unitary application, and assignment. -/
def program (unitary : Unitary d) (x : Var) : QProg Var d :=
  .qSet ;; .qAssign unitary ;; .assign x (1 : Expr Var)

theorem program_bound (unitary : Unitary d) (x : Var) :
    CostBound (weightedModel d) (program unitary x) 12 := by
  have h :=
    (CostBound.qSet (Var := Var) (weightedModel d)).seq
      ((CostBound.qAssign (weightedModel d) unitary).seq
        (CostBound.assign (weightedModel d) x (1 : Expr Var)))
  norm_num [weightedModel] at h
  exact h

/-- Recover the same bound by combining the assignment bound of 2 with the quantum bound of 10. -/
theorem program_bound_from_parts (unitary : Unitary d) (x : Var) :
    CostBound (weightedModel d) (program unitary x) 12 := by
  let writes : CostModel d := { CostModel.zero d with assignmentCost := 2 }
  let quantum := { weightedModel d with assignmentCost := 0 }
  have bound (m : CostModel d) : CostBound m (program unitary x)
      ((m.resetCost : ℝ≥0) + ((m.unitaryCost unitary : ℝ≥0) + m.assignmentCost)) :=
    (CostBound.qSet m).seq ((CostBound.qAssign m unitary).seq (CostBound.assign m x 1))
  have hw : CostBound writes (program unitary x) 2 := by
    simpa [writes, CostModel.zero] using bound writes
  have hq : CostBound quantum (program unitary x) 10 := by
    convert bound quantum using 1
    norm_num [quantum, weightedModel]
  have hmodel : writes.addWeights quantum = weightedModel d := rfl
  have h := hw.addWeights hq
  rw [hmodel] at h
  norm_num at h
  exact h

/-- Under `oracleCalls`, a single oracle application has expected cost equal to the initial mass. -/
theorem selectedOracle_once (oracle : Unitary d) (initial : CQState (Store Var) d) :
    expectedCost (oracleCalls oracle) (.qAssign oracle : QProg Var d) initial =
      initial.trace := by
  simp

/-- Bundled total expected cost (trace conservation + `expectedCost` upper bound)
for `program`. -/
theorem program_totalExpectedCostLe (unitary : Unitary d) (x : Var)
    (initial : CQState (Store Var) d) :
    TotalExpectedCostLe (weightedModel d) (program unitary x) initial 12 := by
  refine ⟨Lossless.trace_eq ?_ initial, (program_bound unitary x).expectedCost_le initial⟩
  exact .seq .qSet (.seq (.qAssign unitary) (.assign x 1))

/-- Measurement-conditioned feedback: measure `x`, then either apply `unitary` (`cost 7`)
or reset (`cost 3`), bounded by `5 + max 7 3 = 12`. -/
def measureAndBranch (x : Var) (measurement : Measurement d 2) (unitary : Unitary d) :
    QProg Var d :=
  .qMeasure x measurement ;; .qIf (fun s ↦ s x ≠ 0) (.qAssign unitary) .qSet

theorem measureAndBranch_bound (x : Var) (measurement : Measurement d 2)
    (unitary : Unitary d) :
    CostBound (weightedModel d) (measureAndBranch x measurement unitary) 12 := by
  have h := (CostBound.qMeasure (weightedModel d) x measurement).seq
    (CostBound.qIf (fun s ↦ s x ≠ 0)
      (CostBound.qAssign (weightedModel d) unitary)
      (CostBound.qSet (weightedModel d)))
  norm_num [weightedModel] at h
  exact h

/-- A 4-outcome complete quantum measurement with uniform outcome probability `1 / 4`. -/
noncomputable def coin : CompleteMeasurement 1 4 :=
  ⟨fun _ ↦ !![(1 / 2 : ℂ)], by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]⟩

private theorem coin_wp (x : Var) :
    wp (.qMeasure x coin.toMeasurement : QProg Var 1)
      (fun σ ↦ ⌜σ x = 0⌝) = .ofProb (1 / 4) := by
  funext store
  apply Subtype.ext
  apply HermitianMat.ext
  rw [wp, CQAssertion.qMeasure_coe]
  simp only [coin, CompleteMeasurement.toMeasurement, Store.subst,
    CQAssertion.ofProb_apply_of_bounds (1 / 4) (by norm_num) (by norm_num),
    HermitianMat.mat_finset_sum, HermitianMat.conj_apply_mat]
  ext i j
  fin_cases i
  fin_cases j
  simp only [Fin.sum_univ_four]
  norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

/-- Repeat a `coin` measurement until it returns outcome `0`: each trial costs `5` and succeeds
with probability `1 / 4`, so the loop terminates almost surely with expected cost `20`. -/
theorem coin_retry_totalExpectedCostLe (result : Var) (initial : CQState (Store Var) 1) :
    TotalExpectedCostLe (weightedModel 1)
      (.qWhile (fun store ↦ store result ≠ 0) (.qMeasure result coin.toMeasurement))
      initial 20 := by
  have h := (CostBound.qMeasure (weightedModel 1) result coin.toMeasurement)
    |>.qWhile_totalExpectedCostLe (guard := fun store ↦ store result ≠ 0) (p := 4⁻¹)
      (by norm_num) (inv_le_one_of_one_le₀ (by norm_num))
      (Lossless.qMeasure result coin) (by simp only [not_not, coin_wp]; norm_num) initial
  norm_num [weightedModel] at h
  exact h

end ResourceCounting.Examples
