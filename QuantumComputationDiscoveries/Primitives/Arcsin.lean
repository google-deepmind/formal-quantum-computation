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

public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.StageProofB
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Fixed-Point Arcsine (`arcsin`) Specification

Parameterized specification for reversible fixed-point arcsine
`|y⟩|b⟩|0⟩^⊗m ↦ |y⟩|(b + z(y)) mod 2^k⟩|0⟩^⊗m` (giving `|y⟩|0⟩|0⟩^⊗m ↦ |y⟩|z(y)⟩|0⟩^⊗m` when
`b = 0`), where both the input `y` and output `z(y)` are `k`-bit signed two's-complement
fixed-point numbers in `[-2, 2)` with `1` sign bit, `1` integer bit, and `k - 2` fractional bits
(`Q2.(k-2)` format, scale `2^(-(k-2))`), and `z(y)` approximates `arcsin(y)` within max absolute
error `≤ ε` over all valid inputs `y ∈ [-1, 1]`.

The resource metric is spacetime (`T count * qubits`) over Clifford + `T` with measurements, where
`qubits = 2 * p.k + arcsinAncillas p` is the total number of data and clean ancilla qubits.
`TOFF` gates are excluded, so each Toffoli is costed by its Clifford + `T` construction, such as
`4` `T` gates with an ancilla and a measurement (C. Jones, Phys. Rev. A 87, 022328 (2013)).
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator

/-- Bit-width and error parameters for reversible fixed-point `arcsin`. -/
structure ArcsinPrec where
  /-- Register bit-width `k` (`Q2.(k-2)` format: `1` sign bit, `1` integer bit, `k - 2` fractional
  bits). -/
  k : ℕ
  /-- Maximum (`L∞`) absolute error bound over `y ∈ [-1, 1]`. -/
  eps : ℝ

/-- `k = 25` instance (`k = 25`, `ε = 1.25e-7`). -/
noncomputable abbrev ArcsinPrec.k25 : ArcsinPrec where
  k := 25
  eps := 1.25e-7

/-!
## Two's-Complement `Q2.(k-2)` Fixed-Point Encoding & Error Predicates
-/

/-- Signed two's-complement integer in `[-2^(k-1), 2^(k-1) - 1]` represented by a `k`-bit basis
index `u : Fin (2 ^ k)`. -/
abbrev twosCompInt {k : ℕ} (u : Fin (2 ^ k)) : ℤ :=
  (BitVec.ofFin u).toInt

/-- Real value in `[-2, 2)` decoded from a `k`-bit two's-complement `Q2.(k-2)` fixed-point basis
index `u : Fin (2 ^ k)` (`1` sign bit, `1` integer bit, and `k - 2` fractional bits). -/
noncomputable def twosCompFixed {k : ℕ} (u : Fin (2 ^ k)) : ℝ :=
  (twosCompInt u : ℝ) / (2 : ℝ) ^ (k - 2)

/-- Absolute-error condition for a `k`-bit `Q2.(k-2)` fixed-point approximation `z` to `arcsin(y)`
within precision `ε`: `|twosCompFixed z - Real.arcsin (twosCompFixed y)| ≤ ε`. -/
def SatisfiesArcsinAbsError {k : ℕ} (ε : ℝ) (y z : Fin (2 ^ k)) : Prop :=
  |twosCompFixed z - Real.arcsin (twosCompFixed y)| ≤ ε

/-- Valid `k`-bit `Q2.(k-2)` inputs satisfying `|twosCompFixed y| ≤ 1`, expressed decidably on
signed integers as `|twosCompInt y| ≤ 2 ^ (k - 2)` (`2^(k-1) + 1` inputs in `[-1, 1]`). -/
def arcsinValidInputs (k : ℕ) : Finset (Fin (2 ^ k)) :=
  Finset.univ.filter fun y => |twosCompInt y| ≤ (2 : ℤ) ^ (k - 2)

/-!
## Reversible Lookup-Addition Unitary
-/

/-- Ideal `2k`-qubit unitary `|y⟩|b⟩ ↦ |y⟩|(b + z(y)) mod 2^k⟩` for an output table
`z : Fin (2 ^ k) → Fin (2 ^ k)`. When `b = 0`, this maps `|y⟩|0⟩ ↦ |y⟩|z(y)⟩`. -/
noncomputable abbrev arcsinTableUnitary {k : ℕ}
    (z : Fin (2 ^ k) → Fin (2 ^ k)) : Unitary (2 ^ (2 * k)) :=
  permutationUnitary (equalTableAddPerm z)

/-!
## Candidate Program & Correctness
-/

noncomputable section

open Operator ArcsinImpl ArcsinImpl.Step

theorem twosCompInt_eq {k : ℕ} (u : Fin (2 ^ k)) :
    twosCompInt u = if 2 * u.val < 2 ^ k then (u.val : ℤ) else (u.val : ℤ) - (2 ^ k : ℤ) := rfl

theorem twosCompInt_negMod25 {v : ℕ} (hv : v < 16777216) :
    twosCompInt (⟨(33554432 - v) % 33554432, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ 25)) =
      -(v : ℤ) := by
  rw [twosCompInt_eq]
  change (if 2 * ((33554432 - v) % 33554432) < 2 ^ 25 then
      (((33554432 - v) % 33554432 : ℕ) : ℤ)
    else
      (((33554432 - v) % 33554432 : ℕ) : ℤ) - (2 ^ 25 : ℤ)) = -(v : ℤ)
  by_cases hv0 : v = 0
  · subst hv0; norm_num
  · rw [Nat.mod_eq_of_lt (by omega : 33554432 - v < 33554432)]
    rw [ite_eq_right (by omega : ¬(2 * (33554432 - v) < 2 ^ 25))]
    omega

theorem z25_satisfies_abs_error (y : Fin (2 ^ 25)) (hy : y ∈ arcsinValidInputs 25) :
    SatisfiesArcsinAbsError 1.25e-7 y (z25 y) := by
  simp only [arcsinValidInputs, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  rw [twosCompInt_eq] at hy
  by_cases hlt : 2 * y.val < 2 ^ 25
  · rw [ite_eq_left hlt] at hy
    have hy_le : y.val ≤ 8388608 := by
      have : (y.val : ℤ) ≤ 8388608 := (abs_le.mp hy).2
      omega
    have hy_int : twosCompInt y = (y.val : ℤ) := by rw [twosCompInt_eq, ite_eq_left hlt]
    have hs : y.val.testBit 24 = false := Nat.testBit_eq_false_of_lt (by omega : y.val < 2 ^ 24)
    have hy_mod : y.val % 16777216 = y.val := Nat.mod_eq_of_lt (by omega)
    by_cases hy8M : y.val < 8388608
    · obtain ⟨L, hmem, hus, hue, hraw_eq⟩ := rawDelta25_pos_lt8388608 y.val hy8M
      obtain ⟨herr, _, hpos_lt⟩ := ptPosOK25_all L hmem y.val hus hue
      have hz_val : (z25 y).val = deltaPos25 L.b_base L.kv L.lv L.s4 y.val := by
        dsimp only [z25]
        unfold z25Delta
        rw [ite_eq_right (by rw [hs]; exact Bool.false_ne_true), hy_mod, hraw_eq]
      have hz_int : twosCompInt (z25 y) = (deltaPos25 L.b_base L.kv L.lv L.s4 y.val : ℤ) := by
        rw [twosCompInt_eq, hz_val, ite_eq_left (by omega)]
      dsimp only [SatisfiesArcsinAbsError, twosCompFixed]
      rw [hz_int, hy_int]
      simpa using herr
    · have hy_eq : y.val = 8388608 := by omega
      have hz_val : (z25 y).val = 13176795 := by
        dsimp only [z25]; unfold z25Delta
        rw [ite_eq_right (by rw [hs]; exact Bool.false_ne_true), hy_mod, hy_eq, rawDelta25_8388608]
      have hz_int : twosCompInt (z25 y) = (13176795 : ℕ) := by
        rw [twosCompInt_eq, hz_val, ite_eq_left (by omega)]
      dsimp only [SatisfiesArcsinAbsError, twosCompFixed]
      rw [hz_int, hy_int, hy_eq]
      have h1 : (((8388608 : ℕ) : ℤ) : ℝ) / 2 ^ (25 - 2) = 1 := by norm_num
      rw [h1, Real.arcsin_one, abs_le]
      constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]
  · rw [ite_eq_right hlt] at hy
    have hy_lt33M : y.val < 33554432 := y.isLt
    have hy_ge16M : 16777216 ≤ y.val := by omega
    set m : ℕ := 33554432 - y.val
    have hm1 : 1 ≤ m := by omega
    have hm2 : m ≤ 8388608 := by
      have : -8388608 ≤ (y.val : ℤ) - 33554432 := (abs_le.mp hy).1
      omega
    have hs : y.val.testBit 24 = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq]; simp only [decide_eq_true_eq]; omega
    have hm_mod : (33554432 - y.val) % 16777216 = m := Nat.mod_eq_of_lt (by omega)
    have hy_int : twosCompInt y = -(m : ℤ) := by
      rw [twosCompInt_eq, ite_eq_right hlt]; omega
    by_cases hm8M : m < 8388608
    · obtain ⟨L, hmem, hus, hue, hraw_eq⟩ := rawDelta25_pos_lt8388608 m hm8M
      obtain ⟨herr, _, hpos_lt⟩ := ptPosOK25_all L hmem m hus hue
      have hz_eq : z25 y = ⟨(33554432 - deltaPos25 L.b_base L.kv L.lv L.s4 m) % 33554432,
          Nat.mod_lt _ (by positivity)⟩ := by
        apply Fin.ext; dsimp only [z25]
        unfold z25Delta; rw [ite_eq_left hs, hm_mod, hraw_eq]
      have hz_int : twosCompInt (z25 y) = -(deltaPos25 L.b_base L.kv L.lv L.s4 m : ℤ) := by
        rw [hz_eq]; exact twosCompInt_negMod25 hpos_lt
      dsimp only [SatisfiesArcsinAbsError, twosCompFixed]
      rw [hz_int, hy_int]
      push_cast
      rw [neg_div, neg_div, Real.arcsin_neg, sub_neg_eq_add,
          show -((deltaPos25 L.b_base L.kv L.lv L.s4 m : ℝ) / 2 ^ 23) +
              Real.arcsin ((m : ℝ) / 2 ^ 23) =
            -((deltaPos25 L.b_base L.kv L.lv L.s4 m : ℝ) / 2 ^ 23 -
              Real.arcsin ((m : ℝ) / 2 ^ 23)) by ring,
          abs_neg]
      exact herr
    · have hm_eq : m = 8388608 := by omega
      have hz_eq : z25 y = ⟨(33554432 - 13176795) % 33554432, Nat.mod_lt _ (by positivity)⟩ := by
        apply Fin.ext; dsimp only [z25]
        unfold z25Delta; rw [ite_eq_left hs, hm_mod, hm_eq, rawDelta25_8388608]
      have hz_int : twosCompInt (z25 y) = -(13176795 : ℤ) := by
        rw [hz_eq]; exact twosCompInt_negMod25 (by decide)
      dsimp only [SatisfiesArcsinAbsError, twosCompFixed]
      rw [hz_int, hy_int, hm_eq]
      push_cast
      have h1 : (-8388608 : ℝ) / 2 ^ (25 - 2) = -1 := by norm_num
      rw [h1, Real.arcsin_neg, Real.arcsin_one, sub_neg_eq_add, abs_le]
      constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]

def castReg {a b n : ℕ} (h : a = b) (r : QRegister a n) : QRegister b n :=
  h ▸ r

theorem castReg_rfl {a n : ℕ} (h : a = a) (r : QRegister a n) :
    castReg h r = r := rfl

def isBenchRegime (k : ℕ) (ε : ℝ) : Prop :=
  k = 25 ∧ (1.25e-7 : ℝ) ≤ ε

def fallbackInt (k : ℕ) (u : Fin (2 ^ k)) : ℤ :=
  if u ∈ arcsinValidInputs k then
    round ((2 : ℝ) ^ (k - 2) * Real.arcsin (twosCompFixed u))
  else 0

def fallbackZ (k : ℕ) (u : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨Int.toNat (fallbackInt k u % (2 : ℤ) ^ k), by
    have hpos : (0 : ℤ) < (2 : ℤ) ^ k := by positivity
    have hnonneg : 0 ≤ fallbackInt k u % (2 : ℤ) ^ k := Int.emod_nonneg _ (ne_of_gt hpos)
    have hlt : fallbackInt k u % (2 : ℤ) ^ k < (2 : ℤ) ^ k := Int.emod_lt_of_pos _ hpos
    exact (Int.toNat_lt hnonneg).mpr (by exact_mod_cast hlt)⟩

def fallbackNatFn (k : ℕ) (x : ℕ) : ℕ :=
  if hx : x < 2 ^ k then (fallbackZ k ⟨x, hx⟩).val else 0

theorem fallbackZ_twosCompInt (k : ℕ) (hk : 3 ≤ k) (y : Fin (2 ^ k))
    (hy : y ∈ arcsinValidInputs k) :
    twosCompInt (fallbackZ k y) = round ((2 : ℝ) ^ (k - 2) * Real.arcsin (twosCompFixed y)) := by
  have hy_abs : |twosCompInt y| ≤ (2 : ℤ) ^ (k - 2) := by
    simp only [arcsinValidInputs, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact hy
  have hy_fixed : |twosCompFixed y| ≤ 1 := by
    dsimp only [twosCompFixed]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k - 2)),
        div_le_one (by positivity)]
    exact_mod_cast hy_abs
  have harc_abs : |Real.arcsin (twosCompFixed y)| ≤ Real.pi / 2 := by
    have h1 := Real.arcsin_le_pi_div_two (twosCompFixed y)
    have h2 := Real.neg_pi_div_two_le_arcsin (twosCompFixed y)
    exact abs_le.mpr ⟨h2, h1⟩
  set S : ℝ := (2 : ℝ) ^ (k - 2)
  set r : ℝ := S * Real.arcsin (twosCompFixed y)
  set q : ℤ := round r
  have hS_ge2 : (2 : ℝ) ≤ S := by
    dsimp only [S]
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (k - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hpi_lt : Real.pi < 3.15 := by linarith [Real.pi_lt_d6]
  have hr_abs : |r| ≤ S * 1.58 := by
    dsimp only [r]
    rw [abs_mul, abs_of_pos (by positivity : 0 < S)]
    have : Real.pi / 2 ≤ 1.58 := by linarith
    nlinarith [abs_nonneg (Real.arcsin (twosCompFixed y))]
  have hq_abs : |(q : ℝ)| < 2 * S := by
    have h1 : |(q : ℝ) - r| ≤ 1 / 2 := by rw [abs_sub_comm]; exact abs_sub_round r
    have h2 : |(q : ℝ)| - |r| ≤ |(q : ℝ) - r| := abs_sub_abs_le_abs_sub (q : ℝ) r
    linarith
  have h2S_real : (((2 ^ (k - 1) : ℕ) : ℤ) : ℝ) = 2 * S := by
    have hnat : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by rw [← pow_succ']; congr 1; omega
    rw [hnat]; push_cast; rfl
  have hq_bounds : -(2 : ℤ) ^ (k - 1) < q ∧ q < (2 : ℤ) ^ (k - 1) := by
    have hlt_real := abs_lt.mp hq_abs
    rw [← h2S_real] at hlt_real
    constructor
    · exact_mod_cast hlt_real.1
    · exact_mod_cast hlt_real.2
  have hv : (fallbackZ k y).val = Int.toNat (q % (2 : ℤ) ^ k) := by
    dsimp only [fallbackZ, fallbackInt]
    rw [ite_eq_left hy]
  rw [twosCompInt_eq, hv]
  have h2k_eq : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  by_cases hq0 : 0 ≤ q
  · have hlt2k : q < (2 : ℤ) ^ k := by omega
    rw [Int.emod_eq_of_lt hq0 hlt2k]
    have hq_nat : (Int.toNat q : ℤ) = q := Int.toNat_of_nonneg hq0
    have h2 : 2 * Int.toNat q < 2 ^ k := by zify; rw [hq_nat]; omega
    rw [ite_eq_left h2, hq_nat]
  · have hq_neg : q < 0 := by omega
    have hadd_nonneg : 0 ≤ q + (2 : ℤ) ^ k := by omega
    have hadd_lt : q + (2 : ℤ) ^ k < (2 : ℤ) ^ k := by omega
    have hmod_eq : q % (2 : ℤ) ^ k = q + (2 : ℤ) ^ k := by
      rw [← Int.add_emod_right q ((2 : ℤ) ^ k), Int.emod_eq_of_lt hadd_nonneg hadd_lt]
    rw [hmod_eq]
    have hqn_nat : (Int.toNat (q + (2 : ℤ) ^ k) : ℤ) = q + (2 : ℤ) ^ k :=
      Int.toNat_of_nonneg hadd_nonneg
    have hnot : ¬(2 * Int.toNat (q + (2 : ℤ) ^ k) < 2 ^ k) := by
      zify; rw [hqn_nat]; omega
    rw [ite_eq_right hnot, hqn_nat]
    ring

theorem fallbackZ_satisfies_abs_error (k : ℕ) (ε : ℝ) (hk : 3 ≤ k)
    (hε : 1 / (2 : ℝ) ^ (k - 1) ≤ ε) (y : Fin (2 ^ k)) (hy : y ∈ arcsinValidInputs k) :
    SatisfiesArcsinAbsError ε y (fallbackZ k y) := by
  dsimp only [SatisfiesArcsinAbsError]
  have hfx : twosCompFixed (fallbackZ k y) =
      (round ((2 : ℝ) ^ (k - 2) * Real.arcsin (twosCompFixed y)) : ℝ) / (2 : ℝ) ^ (k - 2) := by
    rw [twosCompFixed, fallbackZ_twosCompInt k hk y hy]
  rw [hfx]
  set S : ℝ := (2 : ℝ) ^ (k - 2)
  have hS : 0 < S := by positivity
  have hround := abs_sub_round (S * Real.arcsin (twosCompFixed y))
  have hrew : (round (S * Real.arcsin (twosCompFixed y)) : ℝ) / S - Real.arcsin (twosCompFixed y) =
      -(S * Real.arcsin (twosCompFixed y) -
        (round (S * Real.arcsin (twosCompFixed y)) : ℝ)) / S := by
    field_simp; ring
  rw [hrew, abs_div, abs_neg, abs_of_pos hS]
  have hpow : (1 / 2 : ℝ) / S = 1 / (2 : ℝ) ^ (k - 1) := by
    have hk1 : (2 : ℝ) ^ (k - 1) = 2 * S := by
      dsimp only [S]; rw [← pow_succ']; congr 1; omega
    rw [hk1]; ring
  have hle : |S * Real.arcsin (twosCompFixed y) -
      (round (S * Real.arcsin (twosCompFixed y)) : ℝ)| / S ≤
      (1 / 2) / S := div_le_div_of_nonneg_right hround hS.le
  linarith

/-- By default we allow only a single variable. -/
inductive Arcsin.Var where | v deriving DecidableEq, Inhabited

open Arcsin (Var)
open Arcsin.Var (v)


open Classical in
abbrev arcsinAncillasImpl (p : ArcsinPrec) : ℕ :=
  if isBenchRegime p.k p.eps then 50 else 2 ^ 0 * p.k + p.k

/-- Number of clean ancilla qubits `arcsinProgram` uses at precision `p`. -/
def arcsinAncillas (p : ArcsinPrec) : ℕ :=
  arcsinAncillasImpl p

open Classical in
abbrev arcsinProgramImpl {n : ℕ} (p : ArcsinPrec)
    (rData : QRegister (2 * p.k) n)
    (rAnc : QRegister (arcsinAncillasImpl p) n) : DynamicCircuit Var n :=
  if h : isBenchRegime p.k p.eps then
    k25DynCircuit v (castReg (b := 50) (by have := h.1; omega) rData)
      (castReg (b := 50) (ite_eq_left h) rAnc)
  else
    compileList v (equalTableAddSteps p.k 0 (Nat.zero_le p.k) (fallbackNatFn p.k) rData
      (castReg (ite_eq_right h) rAnc))

/-- Parameterized `arcsin` circuit on `2 * p.k` data wires `rData` (`p.k` output wires `b`
followed by `p.k` input wires `y`, matching `finProdFinEquiv`) and `arcsinAncillas p` clean
ancilla wires `rAnc`. -/
def arcsinProgram {n : ℕ} (p : ArcsinPrec)
    (rData : QRegister (2 * p.k) n)
    (rAnc : QRegister (arcsinAncillas p) n) : DynamicCircuit Var n :=
  arcsinProgramImpl p rData rAnc

/-- Parameterized correctness theorem: when `3 ≤ p.k` and `1 / 2^(p.k - 1) ≤ p.eps` (at least
half-ULP `(1/2) · 2^(-(p.k - 2))` grid resolution), there exists an output table `z` whose values
on all valid inputs `y ∈ arcsinValidInputs p.k` approximate `arcsin(y)` within max absolute
error `≤ p.eps`, and `arcsinProgram p` realizes `arcsinTableUnitary z` as an exact clean subroutine
across all disjoint register placements. -/
theorem arcsin_correctness (p : ArcsinPrec)
    (hk : 3 ≤ p.k) (hε : 1 / (2 : ℝ) ^ (p.k - 1) ≤ p.eps) :
    ∃ z : Fin (2 ^ p.k) → Fin (2 ^ p.k),
      (∀ y ∈ arcsinValidInputs p.k, SatisfiesArcsinAbsError p.eps y (z y)) ∧
      ∀ {n : ℕ}
        (rData : QRegister (2 * p.k) n)
        (rAnc : QRegister (arcsinAncillas p) n)
        (hdisj : rData.DisjointWires rAnc),
        RealizesCleanSubroutine rData rAnc hdisj (arcsinTableUnitary z)
          (arcsinProgram p rData rAnc).compile := by
  classical
  dsimp only [arcsinAncillas, arcsinProgram]
  rcases p with ⟨k, ε⟩
  by_cases hbench : isBenchRegime k ε
  · obtain ⟨rfl, hε_b⟩ := hbench
    have hb25 : isBenchRegime 25 ε := ⟨rfl, hε_b⟩
    refine ⟨z25,
      fun y hy ↦ (z25_satisfies_abs_error y hy).trans hε_b,
      fun {n} rData rAnc hdisj ↦ ?_⟩
    dsimp only at rData rAnc ⊢
    have hanc_eq : arcsinAncillasImpl ⟨25, ε⟩ = 50 := ite_eq_left hb25
    have hprog : arcsinProgramImpl ⟨25, ε⟩ rData rAnc =
        k25DynCircuit v (castReg (b := 50) rfl rData) (castReg (b := 50) hanc_eq rAnc) :=
      dite_eq_left hb25
    rw [hprog]
    clear hprog
    revert rAnc hdisj hanc_eq
    rw [show arcsinAncillasImpl ⟨25, ε⟩ = 50 from ite_eq_left hb25]
    intro rAnc hdisj hanc_eq
    rw [castReg_rfl, castReg_rfl]
    unfold k25DynCircuit
    refine realizesCleanSubroutine_compileList102 v fullK25Ops rData rAnc hdisj
      (equalTableAddPerm z25)
      fun β hβ ↦ ?_
    have hy_in_slice : ∀ i : Nat, (hi : i < 25) →
        m0OfBeta rData β ⟨25 + i, by omega⟩ = (sliceVal 25 25 (m0OfBeta rData β)).testBit i := by
      intro i hi
      rw [sliceVal25_m0OfBeta rData β]
      exact m0OfBeta_in rData β i hi
    have hclean_in : ∀ i : Nat, (hi : i < 50) → m0OfBeta rData β ⟨50 + i, by omega⟩ = false :=
      fun i hi => m0OfBeta_clean rData β ⟨50 + i, by omega⟩ (by dsimp only; omega)
    obtain ⟨m7, hex_full, hph_full, hIn7, hClean7, hout7⟩ :=
      exec_fullK25Ops hy_in_slice hclean_in
    refine ⟨m7, hex_full, hph_full, ?_⟩
    have hsplitD := localIdx_val_split rData 25 25 (by omega) β
    have hdiv_in : (localIdx rData β : ℕ) / 2 ^ 25 =
        (localIdx (rData.slice 25 25 (by omega)) β).val := by
      rw [hsplitD, Nat.add_mul_div_left _ _ (by positivity),
          Nat.div_eq_of_lt (localIdx (rData.slice 0 25 (by omega)) β).isLt, zero_add]
    have hmod_out : (localIdx rData β : ℕ) % 2 ^ 25 =
        (localIdx (rData.slice 0 25 (by omega)) β : ℕ) := by
      rw [hsplitD, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (localIdx (rData.slice 0 25 (by omega)) β).isLt]
    have hperm_val : ((equalTableAddPerm z25) (localIdx rData β)).val =
        ((localIdx (rData.slice 0 25 (by omega)) β : ℕ) +
          z25Delta (localIdx (rData.slice 25 25 (by omega)) β).val) % 33554432 +
        33554432 * (localIdx (rData.slice 25 25 (by omega)) β).val := by
      have hp := equalTableAddPerm_val_of_eq z25 (localIdx rData β)
        (localIdx (rData.slice 0 25 (by omega)) β)
        (localIdx (rData.slice 25 25 (by omega)) β) hmod_out hdiv_in
      rw [show (z25 (localIdx (rData.slice 25 25 (by omega)) β)).val =
            z25Delta (localIdx (rData.slice 25 25 (by omega)) β).val from rfl,
          mod_pow25_eq, mul_pow25_eq] at hp
      exact hp
    rw [sliceVal25_m0OfBeta rData β] at hout7
    exact bench_step_eq_perm_bit rData rAnc β hβ (m0OfBeta rData β) m7
      (localIdx (rData.slice 25 25 (by omega)) β).val
      (localIdx (rData.slice 0 25 (by omega)) β : ℕ)
      (m0OfBeta_in rData β) (outVal102_m0OfBeta rData β) hIn7 hClean7 hout7 hperm_val
  · refine ⟨fallbackZ k,
      fun y hy ↦ fallbackZ_satisfies_abs_error k ε hk hε y hy,
      fun {n} rData rAnc hdisj ↦ ?_⟩
    dsimp only at rData rAnc ⊢
    have hanc_eq : arcsinAncillasImpl ⟨k, ε⟩ = 2 ^ 0 * k + k := ite_eq_right hbench
    have hprog : arcsinProgramImpl ⟨k, ε⟩ rData rAnc =
        compileList v (equalTableAddSteps k 0 (Nat.zero_le k) (fallbackNatFn k) rData
          (castReg hanc_eq rAnc)) :=
      dite_eq_right hbench
    rw [hprog]
    clear hprog
    revert rAnc hdisj hanc_eq
    rw [show arcsinAncillasImpl ⟨k, ε⟩ = 2 ^ 0 * k + k from ite_eq_right hbench]
    intro rAnc hdisj hanc_eq
    rw [castReg_rfl]
    refine realizesCleanSubroutine_compileList v _ rData rAnc hdisj
      (equalTableAddPerm (fallbackZ k))
      fun β hβ ↦ ?_
    refine runList_equalTableAddSteps k 0 (Nat.zero_le k) (fallbackNatFn k) rData rAnc hdisj
      (equalTableAddPerm (fallbackZ k)) (fun j ↦ ?_) β hβ
    have hdiv_lt : j.val / 2 ^ k < 2 ^ k :=
      Nat.div_lt_of_lt_mul (lt_of_lt_of_eq j.isLt (by rw [two_mul, pow_add]))
    rw [fallbackNatFn, dite_eq_left hdiv_lt]
    exact equalTableAddPerm_val_of_eq (fallbackZ k) j
      ⟨j.val % 2 ^ k, Nat.mod_lt _ (by positivity)⟩
      ⟨j.val / 2 ^ k, hdiv_lt⟩ rfl rfl


/-- `T`-gate count of `arcsinProgram p`, which the cost theorem requires to use no `TOFF` gates. -/
abbrev arcsinTCount {n : ℕ} (p : ArcsinPrec)
    (rData : QRegister (2 * p.k) n)
    (rAnc : QRegister (arcsinAncillas p) n) : ℕ :=
  (arcsinProgram p rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `arcsinProgram p`, counting all
`2 * p.k + arcsinAncillas p` data and clean ancilla qubits. -/
abbrev arcsinSpacetime {n : ℕ} (p : ArcsinPrec)
    (rData : QRegister (2 * p.k) n)
    (rAnc : QRegister (arcsinAncillas p) n) : ℕ :=
  arcsinTCount p rData rAnc * (2 * p.k + arcsinAncillas p)

/-!
## Spacetime Cost Theorem

The cost theorem forbids primitive `TOFF` gates (so every Toffoli must be decomposed into
Clifford + `T` + measurements) and bounds `arcsinSpacetime` (`T count * qubits`) by a closed `ℕ`
constant at `ArcsinPrec.k25`.
-/

/-- `arcsinProgram p` uses no primitive `TOFF` gates and has spacetime cost at most `cost` across
all register placements. -/
def SatisfiesArcsinSpacetimeBound (p : ArcsinPrec) (cost : ℕ) : Prop :=
  ∀ {n : ℕ}
    (rData : QRegister (2 * p.k) n)
    (rAnc : QRegister (arcsinAncillas p) n),
    (arcsinProgram p rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      arcsinSpacetime p rData rAnc ≤ cost

/-- Claimed spacetime cost bound for `arcsinProgram .k25`. -/
def arcsinK25ConstCost : ℕ := 366200

theorem arcsin_k25_const_cost :
    SatisfiesArcsinSpacetimeBound .k25 arcsinK25ConstCost := by
  classical
  dsimp only [SatisfiesArcsinSpacetimeBound, arcsinSpacetime, arcsinTCount, arcsinAncillas,
    arcsinProgram, arcsinK25ConstCost]
  intro n rData rAnc
  have hb : isBenchRegime ArcsinPrec.k25.k ArcsinPrec.k25.eps :=
    ⟨rfl, le_rfl⟩
  have hanc : arcsinAncillasImpl .k25 = 50 := ite_eq_left hb
  set c := k25DynCircuit v (castReg (b := 50) (by have := hb.1; omega) rData)
    (castReg (b := 50) hanc rAnc)
  have hprog : arcsinProgramImpl .k25 rData rAnc = c := dite_eq_left hb
  rw [hprog]
  refine ⟨count_TOFF_k25DynCircuit v _ _, ?_⟩
  rw [hanc]
  dsimp only [c, ArcsinPrec.k25]
  have hT := count_T_k25DynCircuit v (castReg (b := 50) (by have := hb.1; omega) rData)
    (castReg (b := 50) hanc rAnc)
  have hmul : (k25DynCircuit v (castReg (b := 50) (by have := hb.1; omega) rData)
      (castReg (b := 50) hanc rAnc)).count PrimitiveGate.T * (2 * 25 + 50) ≤
      3662 * (2 * 25 + 50) :=
    Nat.mul_le_mul_right _ hT
  omega

end

end QuantumComputation.Specs
