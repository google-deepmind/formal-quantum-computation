/-
SPDX-License-Identifier: Apache-2.0
-/
module

public import QuantumComputation.QuantumHoareLogic.ResourceCounting.CostBounds
import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops

/-!
# Additivity of expected cost

Adding two cost models lets bounds proved separately for the same program be reused together.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace ResourceCounting

/-- Add the two charges for each primitive operation. -/
def CostModel.addWeights {d : ℕ} (left right : CostModel d) : CostModel d where
  assignmentCost := left.assignmentCost + right.assignmentCost
  measurementCost m := left.measurementCost m + right.measurementCost m
  resetCost := left.resetCost + right.resetCost
  unitaryCost u := left.unitaryCost u + right.unitaryCost u

variable {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]

/-- Expected cost is additive in the primitive weights, including for unbounded loops. -/
theorem expectedCost_addWeights (left right : CostModel d)
    (program : QProg Var d) (state : CQState (Store Var) d) :
    expectedCost (left.addWeights right) program state =
      expectedCost left program state + expectedCost right program state := by
  induction program generalizing state with
  | skip | abort => simp
  | assign | qMeasure | qSet | qAssign => simp [CostModel.addWeights, Nat.cast_add, mul_add]
  | qSeq first second ihFirst ihSecond =>
    simp only [expectedCost_qSeq, ihFirst, ihSecond]
    ac_rfl
  | qIf guard yes no ihYes ihNo =>
    simp only [expectedCost_qIf, ihYes, ihNo]
    ac_rfl
  | qWhile guard body ih =>
    simp only [expectedCost_qWhile_eq_tsum, ih, ENNReal.tsum_add]

/-- Combine two uniform expected-cost bounds for the same program and input space. -/
theorem CostBound.addWeights {left right : CostModel d} {program : QProg Var d} {a b : ℝ≥0}
    (hl : CostBound left program a) (hr : CostBound right program b) :
    CostBound (left.addWeights right) program (a + b) := by
  intro state
  rw [expectedCost_addWeights, ENNReal.coe_add, mul_add]
  exact add_le_add (hl state) (hr state)

end ResourceCounting
