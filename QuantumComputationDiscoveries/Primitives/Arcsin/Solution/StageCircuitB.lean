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

public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.StageCircuitA

@[expose] public section

namespace QuantumComputation.Specs.ArcsinImpl

open Function Operator

-- ============================================================================
-- Stage Execution Theorems (exec_s4_1Ops, exec_s4_3Ops, exec_s4_4Ops, exec_s5_3Ops)
-- ============================================================================

theorem bagDisjoint_wWide_take4 :
    bagDisjoint
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
       22, 23, 24, 49, 47, 50, 51, 52, 53, 54, 55, 56, 57, 59, 60, 61, 62, 63, 64, 65,
       66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 87, 88, 89, 90, 91, 92,
       93, 94, 95, 96, 97, 98, 99]
      (wWideBag53.take 4) = true := by
  decide +kernel

theorem exec_s4_1Ops {m0 : Fin 100 → Bool}
    (hclean : ∀ w : Fin 100, w.val ∈ clean_4_1 → m0 w = false) :
    ∃ m1 : Fin 100 → Bool,
      execList102 s4_1Ops m0 = some m1 ∧
      (∀ w : Fin 100, w.val ∉ b_lo4_w → m1 w = m0 w) ∧
      m1 ⟨47, by decide⟩ = evalSymMask 120 (buildSymEnv 120 m0 defs_4_1) mask47_s41 ∧
      targVal b_lo4_w m1 =
        (evalMasksVal 120 (buildSymEnv 120 m0 defs_4_1) b_lo4_init +
          evalBag 120 (buildSymEnv 120 m0 defs_4_1) (wWideBag53.take 4)) % 16 := by
  obtain ⟨m1, hex, hnon, hext, hmod⟩ := checkStageSymModExtra_sound s4_1_cert hclean
  have hnon' : ∀ w : Fin 100, w.val ∉ b_lo4_w → m1 w = m0 w := by
    intro w hw
    apply hnon w
    intro hmem
    rcases List.mem_append.mp hmem with h1 | h2
    · exact hw h1
    · dsimp only [extra_4_1, List.map] at h2
      have h47 : w.val = 47 := List.mem_singleton.mp h2
      rw [h47] at hw
      exact hw (by decide)
  have h47 : m1 ⟨47, by decide⟩ = evalSymMask 120 (buildSymEnv 120 m0 defs_4_1) mask47_s41 :=
    hext (47, mask47_s41) (by decide) (by decide)
  rw [bag_4_1_eq, evalBag_addMasksAt,
      show out_4_1.length = 4 from rfl,
      show (2 : Nat) ^ 4 = 16 from rfl,
      show (2 : Nat) ^ 0 = 1 from rfl,
      Nat.one_mul] at hmod
  change targVal b_lo4_w m1 = _ at hmod
  exact ⟨m1, hex, hnon', h47, by rw [hmod, Nat.add_comm]⟩

theorem targVal2_out_4_3 (m : Fin 100 → Bool) :
    targVal2 out_4_3 m = targVal b_lo4_w m + 16 * targVal2 hi_qs_w m := by
  rw [show out_4_3 = [47, 69, 70, 71, 56, 52, 54, 53, 61, 55, 59, 60] from rfl,
      show b_lo4_w = [47, 69, 70, 71] from rfl,
      show hi_qs_w = [56, 52, 54, 53, 61, 55, 59, 60] from rfl]
  dsimp only [targVal2, targVal]
  omega

theorem targVal2_hi_qs_w (m : Fin 100 → Bool) :
    targVal2 hi_qs_w m = targVal (hi_qs_w.take 7) m + 64 * targVal [60] m := by
  rw [show hi_qs_w.take 7 = [56, 52, 54, 53, 61, 55, 59] from rfl,
      show hi_qs_w = [56, 52, 54, 53, 61, 55, 59, 60] from rfl]
  dsimp only [targVal2, targVal]
  omega

theorem exec_s4_3Ops {m0 : Fin 100 → Bool}
    (hclean : ∀ w : Fin 100, w.val ∈ clean_4_3 → m0 w = false) :
    ∃ m1 : Fin 100 → Bool,
      execList102 s4_3Ops m0 = some m1 ∧
      (∀ w : Fin 100, w.val ∉ out_4_3 → m1 w = m0 w) ∧
      targVal b_lo4_w m1 =
        (targVal b_lo4_w m0 + evalBag 210 (buildSymEnv 210 m0 defs_4_3) nNarrowBag43) % 16 ∧
      targVal2 hi_qs_w m1 =
        (targVal b_lo4_w m0 + evalBag 210 (buildSymEnv 210 m0 defs_4_3) nNarrowBag43) / 16 := by
  obtain ⟨m1, hex, hnon, hexact⟩ := checkStageSymExact_sound s4_3_cert hclean
  have hsp := targVal2_out_4_3 m1
  have hlt : targVal b_lo4_w m1 < 16 := targVal_lt b_lo4_w m1
  have hb_all : ∀ w ∈ b_lo4_w, w < 100 := by decide
  rw [bag_4_3_eq, evalBag_addMasksAt, evalMasksVal_wireMasks (by decide) b_lo4_w hb_all,
      show (2 : Nat) ^ 0 = 1 from rfl, Nat.one_mul] at hexact
  refine ⟨m1, hex, hnon, ?_, ?_⟩
  · omega
  · omega

theorem exec_s4_4Ops {m0 : Fin 100 → Bool}
    (hclean : ∀ w : Fin 100, w.val ∈ clean_4_4 → m0 w = false) :
    ∃ m1 : Fin 100 → Bool,
      execList102 s4_4Ops m0 = some m1 ∧
      (∀ w : Fin 100, 25 ≤ w.val → m1 w = m0 w) ∧
      targVal z_w m1 =
        (targVal z_w m0 + targVal2 hi_qs_w m0 +
          evalBag 135 (buildSymEnv 135 m0 defs_4_4) nNarrowBag44) % 33554432 := by
  obtain ⟨m1, hex, hnon, hmod⟩ := checkStageSymMod_sound s4_4_cert hclean
  have hge25 : ∀ w : Fin 100, 25 ≤ w.val → m1 w = m0 w := by
    intro w hw
    apply hnon w
    intro hmem
    have := mem_rangeList_iff.mp hmem
    omega
  have hz_all : ∀ w ∈ z_w, w < 100 := by
    intro w hw; have := mem_rangeList_iff.mp hw; omega
  have hhi7_all : ∀ w ∈ hi_qs_w.take 7, w < 100 := by decide
  have h60_all : ∀ w ∈ ([60] : List Nat), w < 100 := by decide
  have hhi_eq := targVal2_hi_qs_w m0
  rw [bag_4_4_eq, evalBag_addMasksAt, evalBag_addMasksAt, evalBag_addMasksAt,
      evalBag_append, evalBag_replicate_nil,
      evalMasksVal_wireMasks (by decide) z_w hz_all,
      evalMasksVal_wireMasks (by decide) (hi_qs_w.take 7) hhi7_all,
      show ([wMask 60] : List Nat) = wireMasks [60] from rfl,
      evalMasksVal_wireMasks (by decide) [60] h60_all,
      show out_4_4.length = 25 by decide,
      show (2 : Nat) ^ 25 = 33554432 by decide,
      show (2 : Nat) ^ 6 = 64 from rfl,
      show (2 : Nat) ^ 0 = 1 from rfl,
      Nat.one_mul, Nat.mul_zero, Nat.add_zero] at hmod
  change targVal z_w m1 = _ at hmod
  exact ⟨m1, hex, hge25, by rw [hmod]; omega⟩

theorem execList102_append_eq {s1 s2 : List Op102} {m0 m1 m2 : Fin 100 → Bool}
    (h1 : execList102 s1 m0 = some m1) (h2 : execList102 s2 m1 = some m2) :
    execList102 (s1 ++ s2) m0 = some m2 := by
  rw [execList102_append, h1, Option.bind_some, h2]

theorem targVal_congr {ws : List Nat} {m1 m2 : Fin 100 → Bool}
    (h : ∀ w : Fin 100, w.val ∈ ws → m1 w = m2 w) :
    targVal ws m1 = targVal ws m2 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    dsimp only [targVal]
    by_cases hw : w < 100
    · rw [dite_eq_left hw, dite_eq_left hw, h ⟨w, hw⟩ (List.mem_cons.mpr (Or.inl rfl)),
          ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    · rw [dite_eq_right hw, dite_eq_right hw, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem exec_s5_3Ops {m0 : Fin 100 → Bool} {b_lo4 : Nat}
    (hb : b_lo4 < 16)
    (hclean : ∀ w : Fin 100, w.val ∈ clean_5_3 → m0 w = false)
    (hx_eq : targVal b_lo4_w m0 =
      (b_lo4 + evalBag 274 (buildSymEnv 274 m0 defs_5_3) (wWideBag53.take 4)) % 16) :
    let env := buildSymEnv 274 m0 defs_5_3
    ∃ m2 : Fin 100 → Bool,
      execList102 s5_3Ops m0 = some m2 ∧
      (∀ w : Fin 100, w.val ∉ out_5_3 ++ extra_5_3.map Prod.fst → m2 w = m0 w) ∧
      (∀ p ∈ extra_5_3, ∀ hw : p.1 < 100, m2 ⟨p.1, hw⟩ = evalSymMask 274 env p.2) ∧
      targVal b_lo4_w m2 = b_lo4 ∧
      targVal z_w m2 = (targVal z_w m0 + (b_lo4 + evalBag 274 env wWideBag53) / 16) % 33554432 := by
  dsimp only
  set env := buildSymEnv 274 m0 defs_5_3
  obtain ⟨m1, hex1, hnon1, hext1, hmod1⟩ := checkStageSymModExtra_sound s5_3_cert hclean
  set m2 : Fin 100 → Bool := fun w => if b_lo4_w.elem w.val then !(m1 w) else m1 w
  have hex2 : execList102 (b_lo4_w.map mkX) m1 = some m2 :=
    execList102_flipList b_lo4_w m1 (by decide) (by decide)
  have hnon2 : ∀ w : Fin 100, w.val ∉ b_lo4_w → m2 w = m1 w := by
    intro w hw; dsimp only [m2]
    rw [ite_eq_right (fun h => hw (List.mem_of_elem_eq_true h))]
  have hval2 : targVal b_lo4_w m2 = 2 ^ b_lo4_w.length - 1 - targVal b_lo4_w m1 := by
    change (bif !m1 ⟨47, by decide⟩ then 1 else 0) +
      2 * ((bif !m1 ⟨69, by decide⟩ then 1 else 0) +
        2 * ((bif !m1 ⟨70, by decide⟩ then 1 else 0) +
          2 * ((bif !m1 ⟨71, by decide⟩ then 1 else 0) + 2 * 0))) =
      15 - ((bif m1 ⟨47, by decide⟩ then 1 else 0) +
        2 * ((bif m1 ⟨69, by decide⟩ then 1 else 0) +
          2 * ((bif m1 ⟨70, by decide⟩ then 1 else 0) +
            2 * ((bif m1 ⟨71, by decide⟩ then 1 else 0) + 2 * 0))))
    cases m1 ⟨47, by decide⟩ <;> cases m1 ⟨69, by decide⟩ <;>
      cases m1 ⟨70, by decide⟩ <;> cases m1 ⟨71, by decide⟩ <;> rfl
  have hex_all : execList102 s5_3Ops m0 = some m2 := by
    unfold s5_3Ops
    exact execList102_append_eq hex1 hex2
  have hnon_all : ∀ w : Fin 100, w.val ∉ out_5_3 ++ extra_5_3.map Prod.fst → m2 w = m0 w := by
    intro w hw
    have hw_not_b : w.val ∉ b_lo4_w := fun hb_mem =>
      hw (List.mem_append_left _ (List.mem_append_left _ hb_mem))
    rw [hnon2 w hw_not_b, hnon1 w hw]
  have hext_all : ∀ p ∈ extra_5_3, ∀ hw : p.1 < 100, m2 ⟨p.1, hw⟩ = evalSymMask 274 env p.2 := by
    intro p hp hw
    have hp_not_b : p.1 ∉ b_lo4_w := by
      revert p hp; decide +kernel
    rw [hnon2 ⟨p.1, hw⟩ hp_not_b, hext1 p hp hw]
  have hz_eq : targVal z_w m2 = targVal z_w m1 := by
    have hdisj : ∀ w ∈ z_w, w ∉ b_lo4_w := by decide +kernel
    exact targVal_congr (fun w hw => hnon2 w (hdisj w.val hw))
  have hsp1 := targVal_append b_lo4_w z_w m1
  change targVal out_5_3 m1 = targVal b_lo4_w m1 + 2 ^ b_lo4_w.length * targVal z_w m1 at hsp1
  have hlt_b1 : targVal b_lo4_w m1 < 16 := targVal_lt b_lo4_w m1
  have hb_all : ∀ w ∈ b_lo4_w, w < 100 := by decide
  have hz_all : ∀ w ∈ z_w, w < 100 := by
    intro w hw; have := mem_rangeList_iff.mp hw; omega
  rw [show b_lo4_w.length = 4 from rfl, show (2 : Nat) ^ 4 = 16 from rfl] at hsp1 hval2
  rw [bag_5_3_eq, evalBag_addMasksAt, evalBag_addMasksAt,
      evalMasksVal_xorMasks (by decide) 1 b_lo4_w hb_all,
      evalSymMask_one (by decide),
      evalMasksVal_wireMasks (by decide) z_w hz_all,
      show out_5_3.length = 29 by decide,
      show (2 : Nat) ^ 29 = 536870912 by decide,
      show b_lo4_w.length = 4 from rfl,
      show (2 : Nat) ^ 4 = 16 from rfl,
      show (2 : Nat) ^ 0 = 1 from rfl,
      Nat.one_mul] at hmod1
  change targVal out_5_3 m1 =
    (evalBag 274 env wWideBag53 + 16 * targVal z_w m0 +
      (15 - targVal b_lo4_w m0)) % 536870912 at hmod1
  have htake4 := evalBag_take_four 274 env wWideBag53 (by decide)
  have hx_eq' : targVal b_lo4_w m0 = (b_lo4 + evalBag 274 env wWideBag53) % 16 := by
    rw [htake4]; omega
  rw [hx_eq'] at hmod1
  have ⟨hmod16, hdiv16⟩ :=
    wWide_carry_split (Z := targVal z_w m0) (W_val := evalBag 274 env wWideBag53) hb
  refine ⟨m2, hex_all, hnon_all, hext_all, ?_, ?_⟩
  · omega
  · rw [hz_eq]; omega

-- ============================================================================
-- U18, l8_0, and b_lo4_init Mask Evaluation Lemmas
-- ============================================================================

theorem evalSymMask_aMask {N : Nat} {env : Nat → Bool} {defs : List (Nat × Nat)}
    (hDefs : DefsOK N env defs) {k u v : Nat} (hk : defs[k]? = some (u, v)) :
    evalSymMask N env (aMask k) = (evalSymMask N env u && evalSymMask N env v) := by
  have hlt : k < defs.length := (List.getElem?_eq_some_iff.mp hk).1
  unfold aMask
  rw [evalSymMask_shiftLeft_one _ (by have := hDefs.1; omega)]
  exact hDefs.2 k (u, v) hk

theorem checkDefsWF_defs_4_3 : checkDefsWF 103 defs_4_3 = true := by decide +kernel
theorem checkDefsWF_defs_5_3 : checkDefsWF 103 defs_5_3 = true := by decide +kernel

theorem evalSymMask_l8_0_m (m0 : Fin 100 → Bool) :
    evalSymMask 210 (buildSymEnv 210 m0 defs_4_3) l8_0_m =
      xor (xor (xor (xor (m0 ⟨44, by decide⟩ && xor (m0 ⟨46, by decide⟩) (m0 ⟨41, by decide⟩))
        (m0 ⟨41, by decide⟩)) (m0 ⟨48, by decide⟩)) (m0 ⟨58, by decide⟩)) true := by
  have hDefs := defsOK_buildSymEnv 210 m0 defs_4_3 (by decide) checkDefsWF_defs_4_3
  have ha0 := evalSymMask_aMask hDefs (k := 0) (u := wMask 44) (v := wMask 46 ^^^ wMask 41) rfl
  have hl8 : l8_0_m = aMask 0 ^^^ wMask 41 ^^^ wMask 48 ^^^ wMask 58 ^^^ 1 := rfl
  have hN : 103 ≤ 210 := by decide
  rw [hl8, evalSymMask_xor, evalSymMask_xor, evalSymMask_xor, evalSymMask_xor,
      ha0, evalSymMask_xor,
      evalSymMask_wMask hN (by decide : 44 < 100),
      evalSymMask_wMask hN (by decide : 46 < 100),
      evalSymMask_wMask hN (by decide : 41 < 100),
      evalSymMask_wMask hN (by decide : 48 < 100),
      evalSymMask_wMask hN (by decide : 58 < 100),
      evalSymMask_one (by decide)]

def rest47_mask : Nat := mask47_s41 ^^^ wMask 47

def badW_41_53 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
   22, 23, 24, 49, 47, 50, 51, 52, 53, 54, 55, 56, 57, 59, 60, 61, 62, 63, 64, 65,
   66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 87, 88, 89, 90, 91, 92,
   93, 94, 95, 96, 97, 98, 99]

theorem maskDisjoint_rest47 : maskDisjoint badW_41_53 rest47_mask = true := by decide +kernel

theorem evalSymMask_mask47_s41 {m_s3b m_s52 : Fin 100 → Bool}
    (h47 : m_s52 ⟨47, by decide⟩ = evalSymMask 120 (buildSymEnv 120 m_s3b defs_4_1) mask47_s41)
    (hkeep : ∀ w : Fin 100, w.val ∉ badW_41_53 → m_s52 w = m_s3b w) :
    evalSymMask 274 (buildSymEnv 274 m_s52 defs_5_3) mask47_s41 = m_s3b ⟨47, by decide⟩ := by
  have hsp : mask47_s41 = rest47_mask ^^^ wMask 47 := rfl
  rw [hsp, evalSymMask_xor, evalSymMask_wMask (by decide) (by decide : 47 < 100),
      h47, hsp, evalSymMask_xor, evalSymMask_wMask (by decide) (by decide : 47 < 100),
      evalSymMask_congr_disjoint (by decide : 103 ≤ 274) (by decide : 103 ≤ 120)
        maskDisjoint_rest47 hkeep]
  cases evalSymMask 120 (buildSymEnv 120 m_s3b defs_4_1) rest47_mask <;>
    cases m_s3b ⟨47, by decide⟩ <;> rfl

def u18_a78 (b46 b58 h5 : Bool) : Bool := xor b46 b58 && xor h5 b58
def u18_a79 (b48 b58 h5 : Bool) : Bool := b48 && xor h5 b58
def u18_a80 (b44 b48 b58 h5 : Bool) : Bool := b44 && u18_a79 b48 b58 h5
def u18_a122 (b58 h5 : Bool) : Bool := b58 && h5
def u18_a123 (b46 b58 : Bool) : Bool := b46 && b58
def u18_a124 (b48 b58 : Bool) : Bool := b48 && b58
def u18_a125 (b46 b58 h5 : Bool) : Bool := b46 && u18_a122 b58 h5
def u18_a126 (b45 b46 b58 h5 : Bool) : Bool := b45 && xor (u18_a122 b58 h5) (u18_a125 b46 b58 h5)
def u18_a127 (b45 b46 b48 b58 h5 : Bool) : Bool :=
  b45 && xor (xor (xor (xor (xor (xor h5 true) b46) b48) b58)
    (u18_a78 b46 b58 h5)) (u18_a79 b48 b58 h5)

def u18_cin0 (b44 b46 b48 b58 h5 : Bool) : Bool :=
  xor (xor (xor (xor h5 b46) b58) (u18_a78 b46 b58 h5)) (u18_a80 b44 b48 b58 h5)
def u18_q0 (b45 b46 b48 b58 h5 : Bool) : Bool :=
  xor (xor (xor (xor (xor b58 (u18_a78 b46 b58 h5)) (u18_a79 b48 b58 h5))
    (u18_a123 b46 b58)) (u18_a124 b48 b58)) (u18_a127 b45 b46 b48 b58 h5)
def u18_q19_0 (b46 b48 b58 h5 : Bool) : Bool :=
  xor (xor (xor (xor (xor true b48) b58) (u18_a122 b58 h5)) (u18_a123 b46 b58)) (u18_a124 b48 b58)
def u18_q19_1 (b45 b46 b48 b58 h5 : Bool) : Bool :=
  xor (xor (xor (xor true b48) (u18_a122 b58 h5)) (u18_a125 b46 b58 h5)) (u18_a126 b45 b46 b58 h5)
def u18_q19_2 (b45 b46 b48 b58 h5 : Bool) : Bool :=
  xor (xor (xor (xor true b48) b58) (u18_a125 b46 b58 h5)) (u18_a126 b45 b46 b58 h5)
def u18_q19_3 (b48 b58 h5 : Bool) : Bool :=
  xor (xor (xor (xor (xor h5 true) b48) b58) (u18_a122 b58 h5)) (u18_a124 b48 b58)
def u18_q19_4 (b48 b58 h5 : Bool) : Bool :=
  xor (xor (xor (xor (xor h5 true) b48) b58) (u18_a79 b48 b58 h5)) (u18_a122 b58 h5)

def u18_val (b44 b45 b46 b48 b58 h5 : Bool) : Nat :=
  (cond (u18_cin0 b44 b46 b48 b58 h5) 1 0) +
  (cond (u18_q0 b45 b46 b48 b58 h5) 1 0) +
  2 * ((cond (u18_q19_0 b46 b48 b58 h5) 1 0) +
  2 * ((cond (u18_q19_1 b45 b46 b48 b58 h5) 1 0) +
  2 * ((cond (u18_q19_2 b45 b46 b48 b58 h5) 1 0) +
  2 * ((cond (u18_q19_3 b48 b58 h5) 1 0) +
  2 * ((cond (u18_q19_4 b48 b58 h5) 1 0) +
  2 * (cond (u18_q19_4 b48 b58 h5) 1 0))))))

theorem evalSymMask_u18 (m0 : Fin 100 → Bool) {h5 : Bool}
    (hm47 : evalSymMask 274 (buildSymEnv 274 m0 defs_5_3) mask47_s41 = h5) :
    let env := buildSymEnv 274 m0 defs_5_3
    let b44 := m0 ⟨44, by decide⟩
    let b45 := m0 ⟨45, by decide⟩
    let b46 := m0 ⟨46, by decide⟩
    let b48 := m0 ⟨48, by decide⟩
    let b58 := m0 ⟨58, by decide⟩
    evalSymMask 274 env cin0_m = u18_cin0 b44 b46 b48 b58 h5 ∧
    evalSymMask 274 env q0_m = u18_q0 b45 b46 b48 b58 h5 ∧
    evalSymMask 274 env q19_0_m = u18_q19_0 b46 b48 b58 h5 ∧
    evalSymMask 274 env q19_1_m = u18_q19_1 b45 b46 b48 b58 h5 ∧
    evalSymMask 274 env q19_2_m = u18_q19_2 b45 b46 b48 b58 h5 ∧
    evalSymMask 274 env q19_3_m = u18_q19_3 b48 b58 h5 ∧
    evalSymMask 274 env q19_4_m = u18_q19_4 b48 b58 h5 ∧
    u18SymVal env = u18_val b44 b45 b46 b48 b58 h5 := by
  dsimp only
  set env := buildSymEnv 274 m0 defs_5_3
  have hDefs := defsOK_buildSymEnv 274 m0 defs_5_3 (by decide +kernel) checkDefsWF_defs_5_3
  have hN : 103 ≤ 274 := by decide
  have hw44 := evalSymMask_wMask (m0 := m0) (defs := defs_5_3) hN (by decide : 44 < 100)
  have hw45 := evalSymMask_wMask (m0 := m0) (defs := defs_5_3) hN (by decide : 45 < 100)
  have hw46 := evalSymMask_wMask (m0 := m0) (defs := defs_5_3) hN (by decide : 46 < 100)
  have hw48 := evalSymMask_wMask (m0 := m0) (defs := defs_5_3) hN (by decide : 48 < 100)
  have hw58 := evalSymMask_wMask (m0 := m0) (defs := defs_5_3) hN (by decide : 58 < 100)
  have hone := evalSymMask_one (m0 := m0) (defs := defs_5_3) (by decide : 1 ≤ 274)
  have h_p1 : evalSymMask 274 env (aMask 82) =
      ((xor ((m0 ⟨46, by decide⟩)) (m0 ⟨58, by decide⟩)) &&
        (xor (h5) (m0 ⟨58, by decide⟩))) := by
    rw [evalSymMask_aMask hDefs (k := 82) (u := wMask 46 ^^^ wMask 58)
          (v := mask47_s41 ^^^ wMask 58) rfl,
        evalSymMask_xor, evalSymMask_xor, hw46, hw58, hm47]
  have h_p0 : evalSymMask 274 env (aMask 83) =
      (((m0 ⟨48, by decide⟩)) && (xor (h5) (m0 ⟨58, by decide⟩))) := by
    rw [evalSymMask_aMask hDefs (k := 83) (u := wMask 48)
          (v := mask47_s41 ^^^ wMask 58) rfl,
        evalSymMask_xor, hw48, hm47, hw58]
  have h_a80 : evalSymMask 274 env (aMask 84) =
      (((m0 ⟨44, by decide⟩)) &&
        ((((m0 ⟨48, by decide⟩)) && (xor (h5) (m0 ⟨58, by decide⟩))))) := by
    rw [evalSymMask_aMask hDefs (k := 84) (u := wMask 44) (v := aMask 83) rfl, hw44, h_p0]
  have h_g0 : evalSymMask 274 env (aMask 123) =
      (((m0 ⟨46, by decide⟩)) && ((m0 ⟨58, by decide⟩))) := by
    rw [evalSymMask_aMask hDefs (k := 123) (u := wMask 46) (v := wMask 58) rfl, hw46, hw58]
  have h_g2 : evalSymMask 274 env (aMask 124) =
      (((m0 ⟨48, by decide⟩)) && ((m0 ⟨58, by decide⟩))) := by
    rw [evalSymMask_aMask hDefs (k := 124) (u := wMask 48) (v := wMask 58) rfl, hw48, hw58]
  have h_g4 : evalSymMask 274 env (aMask 125) = (((m0 ⟨58, by decide⟩)) && (h5)) := by
    rw [evalSymMask_aMask hDefs (k := 125) (u := wMask 58) (v := mask47_s41) rfl, hw58, hm47]
  have h_g5 : evalSymMask 274 env (aMask 126) =
      (((m0 ⟨45, by decide⟩)) &&
        (xor (xor (xor (xor (xor (h5) (m0 ⟨46, by decide⟩)) (m0 ⟨48, by decide⟩))
            (m0 ⟨58, by decide⟩))
          ((xor ((m0 ⟨46, by decide⟩)) (m0 ⟨58, by decide⟩)) &&
            (xor (h5) (m0 ⟨58, by decide⟩))))
          (((m0 ⟨48, by decide⟩)) && (xor (h5) (m0 ⟨58, by decide⟩))))) := by
    rw [evalSymMask_aMask hDefs (k := 126) (u := wMask 45)
          (v := mask47_s41 ^^^ wMask 46 ^^^ wMask 48 ^^^ wMask 58 ^^^ aMask 82 ^^^ aMask 83) rfl,
        evalSymMask_xor, evalSymMask_xor, evalSymMask_xor, evalSymMask_xor, evalSymMask_xor,
        hw45, hm47, hw46, hw48, hw58, h_p1, h_p0]
  have h_g6 : evalSymMask 274 env (aMask 127) =
      ((xor (xor (xor ((m0 ⟨45, by decide⟩)) (m0 ⟨58, by decide⟩))
            ((xor ((m0 ⟨46, by decide⟩)) (m0 ⟨58, by decide⟩)) &&
              (xor (h5) (m0 ⟨58, by decide⟩))))
          (((m0 ⟨58, by decide⟩)) && (h5))) &&
        (xor (xor (xor ((m0 ⟨58, by decide⟩))
              ((xor ((m0 ⟨46, by decide⟩)) (m0 ⟨58, by decide⟩)) &&
                (xor (h5) (m0 ⟨58, by decide⟩))))
            (((m0 ⟨46, by decide⟩)) && ((m0 ⟨58, by decide⟩))))
          (((m0 ⟨45, by decide⟩)) &&
            (xor (xor (xor (xor (xor (h5) (m0 ⟨46, by decide⟩)) (m0 ⟨48, by decide⟩))
                  (m0 ⟨58, by decide⟩))
                ((xor ((m0 ⟨46, by decide⟩)) (m0 ⟨58, by decide⟩)) &&
                  (xor (h5) (m0 ⟨58, by decide⟩))))
              (((m0 ⟨48, by decide⟩)) && (xor (h5) (m0 ⟨58, by decide⟩))))))) := by
    rw [evalSymMask_aMask hDefs (k := 127)
          (u := wMask 45 ^^^ wMask 58 ^^^ aMask 82 ^^^ aMask 125)
          (v := wMask 58 ^^^ aMask 82 ^^^ aMask 123 ^^^ aMask 126) rfl,
        evalSymMask_xor, evalSymMask_xor, evalSymMask_xor, evalSymMask_xor,
        evalSymMask_xor, evalSymMask_xor, hw45, hw58, h_p1, h_g4, h_g0, h_g5]
  have hcin0 : evalSymMask 274 env cin0_m =
      u18_cin0 (m0 ⟨44, by decide⟩) (m0 ⟨46, by decide⟩) (m0 ⟨48, by decide⟩)
        (m0 ⟨58, by decide⟩) h5 := by
    rw [show cin0_m = mask47_s41 ^^^ wMask 46 ^^^ wMask 58 ^^^ aMask 82 ^^^ aMask 84 from rfl,
        evalSymMask_xor, evalSymMask_xor, evalSymMask_xor, evalSymMask_xor,
        hm47, hw46, hw58, h_p1, h_a80]
    generalize (m0 ⟨44, by decide⟩) = x44, (m0 ⟨45, by decide⟩) = x45,
      (m0 ⟨46, by decide⟩) = x46, (m0 ⟨48, by decide⟩) = x48,
      (m0 ⟨58, by decide⟩) = x58, h5 = xh5
    cases x44 <;> cases x45 <;> cases x46 <;> cases x48 <;> cases x58 <;> cases xh5 <;> rfl
  have hq0 : evalSymMask 274 env q0_m =
      u18_q0 (m0 ⟨45, by decide⟩) (m0 ⟨46, by decide⟩) (m0 ⟨48, by decide⟩)
        (m0 ⟨58, by decide⟩) h5 := by
    rw [show q0_m = wMask 45 ^^^ wMask 58 ^^^ aMask 82 ^^^ aMask 83 ^^^
          aMask 123 ^^^ aMask 124 ^^^ aMask 126 from rfl,
        evalSymMask_xor, evalSymMask_xor, evalSymMask_xor, evalSymMask_xor,
        evalSymMask_xor, evalSymMask_xor, hw45, hw58, h_p1, h_p0, h_g0, h_g2, h_g5]
    generalize (m0 ⟨44, by decide⟩) = x44, (m0 ⟨45, by decide⟩) = x45,
      (m0 ⟨46, by decide⟩) = x46, (m0 ⟨48, by decide⟩) = x48,
      (m0 ⟨58, by decide⟩) = x58, h5 = xh5
    cases x44 <;> cases x45 <;> cases x46 <;> cases x48 <;> cases x58 <;> cases xh5 <;> rfl
  have hq19_0 : evalSymMask 274 env q19_0_m =
      u18_q19_0 (m0 ⟨46, by decide⟩) (m0 ⟨48, by decide⟩) (m0 ⟨58, by decide⟩) h5 := by
    rw [show q19_0_m = 1 ^^^ wMask 48 ^^^ wMask 58 ^^^ aMask 123 ^^^ aMask 124 ^^^ aMask 125
          from rfl,
        evalSymMask_xor, evalSymMask_xor, evalSymMask_xor, evalSymMask_xor,
        evalSymMask_xor, hone, hw48, hw58, h_g0, h_g2, h_g4]
    generalize (m0 ⟨44, by decide⟩) = x44, (m0 ⟨45, by decide⟩) = x45,
      (m0 ⟨46, by decide⟩) = x46, (m0 ⟨48, by decide⟩) = x48,
      (m0 ⟨58, by decide⟩) = x58, h5 = xh5
    cases x44 <;> cases x45 <;> cases x46 <;> cases x48 <;> cases x58 <;> cases xh5 <;> rfl
  have hq19_1 : evalSymMask 274 env q19_1_m =
      u18_q19_1 (m0 ⟨45, by decide⟩) (m0 ⟨46, by decide⟩) (m0 ⟨48, by decide⟩)
        (m0 ⟨58, by decide⟩) h5 := by
    rw [show q19_1_m = 1 ^^^ wMask 48 ^^^ wMask 58 ^^^ aMask 82 ^^^
          aMask 123 ^^^ aMask 126 ^^^ aMask 127 from rfl,
        evalSymMask_xor, evalSymMask_xor, evalSymMask_xor, evalSymMask_xor,
        evalSymMask_xor, evalSymMask_xor, hone, hw48, hw58, h_p1, h_g0, h_g5, h_g6]
    generalize (m0 ⟨44, by decide⟩) = x44, (m0 ⟨45, by decide⟩) = x45,
      (m0 ⟨46, by decide⟩) = x46, (m0 ⟨48, by decide⟩) = x48,
      (m0 ⟨58, by decide⟩) = x58, h5 = xh5
    cases x44 <;> cases x45 <;> cases x46 <;> cases x48 <;> cases x58 <;> cases xh5 <;> rfl
  have hq19_2 : evalSymMask 274 env q19_2_m =
      u18_q19_2 (m0 ⟨45, by decide⟩) (m0 ⟨46, by decide⟩) (m0 ⟨48, by decide⟩)
        (m0 ⟨58, by decide⟩) h5 := by
    rw [show q19_2_m = 1 ^^^ wMask 48 ^^^ aMask 82 ^^^ aMask 123 ^^^
          aMask 125 ^^^ aMask 126 ^^^ aMask 127 from rfl,
        evalSymMask_xor, evalSymMask_xor, evalSymMask_xor, evalSymMask_xor,
        evalSymMask_xor, evalSymMask_xor, hone, hw48, h_p1, h_g0, h_g4, h_g5, h_g6]
    generalize (m0 ⟨44, by decide⟩) = x44, (m0 ⟨45, by decide⟩) = x45,
      (m0 ⟨46, by decide⟩) = x46, (m0 ⟨48, by decide⟩) = x48,
      (m0 ⟨58, by decide⟩) = x58, h5 = xh5
    cases x44 <;> cases x45 <;> cases x46 <;> cases x48 <;> cases x58 <;> cases xh5 <;> rfl
  have hq19_3 : evalSymMask 274 env q19_3_m =
      u18_q19_3 (m0 ⟨48, by decide⟩) (m0 ⟨58, by decide⟩) h5 := by
    rw [show q19_3_m = mask47_s41 ^^^ 1 ^^^ wMask 48 ^^^ wMask 58 ^^^ aMask 124 ^^^ aMask 125
          from rfl,
        evalSymMask_xor, evalSymMask_xor, evalSymMask_xor, evalSymMask_xor,
        evalSymMask_xor, hm47, hone, hw48, hw58, h_g2, h_g4]
    generalize (m0 ⟨44, by decide⟩) = x44, (m0 ⟨45, by decide⟩) = x45,
      (m0 ⟨46, by decide⟩) = x46, (m0 ⟨48, by decide⟩) = x48,
      (m0 ⟨58, by decide⟩) = x58, h5 = xh5
    cases x44 <;> cases x45 <;> cases x46 <;> cases x48 <;> cases x58 <;> cases xh5 <;> rfl
  have hq19_4 : evalSymMask 274 env q19_4_m =
      u18_q19_4 (m0 ⟨48, by decide⟩) (m0 ⟨58, by decide⟩) h5 := by
    rw [show q19_4_m = mask47_s41 ^^^ 1 ^^^ wMask 48 ^^^ wMask 58 ^^^ aMask 83 ^^^ aMask 125
          from rfl,
        evalSymMask_xor, evalSymMask_xor, evalSymMask_xor, evalSymMask_xor,
        evalSymMask_xor, hm47, hone, hw48, hw58, h_p0, h_g4]
    generalize (m0 ⟨44, by decide⟩) = x44, (m0 ⟨45, by decide⟩) = x45,
      (m0 ⟨46, by decide⟩) = x46, (m0 ⟨48, by decide⟩) = x48,
      (m0 ⟨58, by decide⟩) = x58, h5 = xh5
    cases x44 <;> cases x45 <;> cases x46 <;> cases x48 <;> cases x58 <;> cases xh5 <;> rfl
  refine ⟨hcin0, hq0, hq19_0, hq19_1, hq19_2, hq19_3, hq19_4, ?_⟩
  unfold u18SymVal u18_val
  dsimp only [evalMasksVal]
  rw [hcin0, hq0, hq19_0, hq19_1, hq19_2, hq19_3, hq19_4]
  omega

def bLo4InitBit0 (m : Fin 100 → Bool) : Bool :=
  xor (xor (m ⟨46, by decide⟩) (m ⟨48, by decide⟩)) (m ⟨47, by decide⟩)

def bLo4InitBit1 (m : Fin 100 → Bool) : Bool :=
  xor (xor (xor (xor (xor (xor (xor (xor (xor (xor (m ⟨46, by decide⟩) (m ⟨47, by decide⟩))
    (m ⟨41, by decide⟩)) (m ⟨45, by decide⟩)) (m ⟨72, by decide⟩)) (m ⟨75, by decide⟩))
    (m ⟨77, by decide⟩)) (m ⟨78, by decide⟩)) (m ⟨86, by decide⟩)) (m ⟨89, by decide⟩))
    (m ⟨93, by decide⟩)

def bLo4InitVal (m : Fin 100 → Bool) : Nat :=
  (cond (bLo4InitBit0 m) 1 0) +
  2 * ((cond (bLo4InitBit1 m) 1 0) +
  2 * ((cond (m ⟨70, by decide⟩) 1 0) +
  2 * (cond (m ⟨71, by decide⟩) 1 0)))

theorem bLo4InitVal_lt (m : Fin 100 → Bool) : bLo4InitVal m < 16 := by
  unfold bLo4InitVal
  cases bLo4InitBit0 m <;> cases bLo4InitBit1 m <;>
    cases m ⟨70, by decide⟩ <;> cases m ⟨71, by decide⟩ <;> decide

theorem evalMasksVal_b_lo4_init (m0 : Fin 100 → Bool) :
    evalMasksVal 120 (buildSymEnv 120 m0 defs_4_1) b_lo4_init = bLo4InitVal m0 := by
  have hN : 103 ≤ 120 := by decide
  have hb0 : evalSymMask 120 (buildSymEnv 120 m0 defs_4_1) (wMask 46 ^^^ wMask 48 ^^^ wMask 47) =
      bLo4InitBit0 m0 := by
    rw [evalSymMask_xor, evalSymMask_xor,
        evalSymMask_wMask hN (by decide : 46 < 100),
        evalSymMask_wMask hN (by decide : 48 < 100),
        evalSymMask_wMask hN (by decide : 47 < 100)]; rfl
  have hb1 : evalSymMask 120 (buildSymEnv 120 m0 defs_4_1)
      (wMask 46 ^^^ wMask 47 ^^^ wMask 41 ^^^ wMask 45 ^^^ wMask 72 ^^^ wMask 75 ^^^
        wMask 77 ^^^ wMask 78 ^^^ wMask 86 ^^^ wMask 89 ^^^ wMask 93) =
      bLo4InitBit1 m0 := by
    repeat rw [evalSymMask_xor]
    rw [evalSymMask_wMask hN (by decide : 46 < 100),
        evalSymMask_wMask hN (by decide : 47 < 100),
        evalSymMask_wMask hN (by decide : 41 < 100),
        evalSymMask_wMask hN (by decide : 45 < 100),
        evalSymMask_wMask hN (by decide : 72 < 100),
        evalSymMask_wMask hN (by decide : 75 < 100),
        evalSymMask_wMask hN (by decide : 77 < 100),
        evalSymMask_wMask hN (by decide : 78 < 100),
        evalSymMask_wMask hN (by decide : 86 < 100),
        evalSymMask_wMask hN (by decide : 89 < 100),
        evalSymMask_wMask hN (by decide : 93 < 100)]; rfl
  have hb2 := evalSymMask_wMask (m0 := m0) (defs := defs_4_1) hN (by decide : 70 < 100)
  have hb3 := evalSymMask_wMask (m0 := m0) (defs := defs_4_1) hN (by decide : 71 < 100)
  rw [show b_lo4_init = [
        wMask 46 ^^^ wMask 48 ^^^ wMask 47,
        wMask 46 ^^^ wMask 47 ^^^ wMask 41 ^^^ wMask 45 ^^^ wMask 72 ^^^ wMask 75 ^^^
          wMask 77 ^^^ wMask 78 ^^^ wMask 86 ^^^ wMask 89 ^^^ wMask 93,
        wMask 70,
        wMask 71] from rfl]
  dsimp only [evalMasksVal, bLo4InitVal]
  rw [hb0, hb1, hb2, hb3]
  omega

theorem four_bits_of_val_eq {a0 a1 a2 a3 b0 b1 b2 b3 : Bool}
    (h : (cond a0 1 0) + 2 * ((cond a1 1 0) + 2 * ((cond a2 1 0) + 2 * ((cond a3 1 0) + 2 * 0))) =
         (cond b0 1 0) + 2 * ((cond b1 1 0) + 2 * ((cond b2 1 0) + 2 * (cond b3 1 0)))) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  revert a0 a1 a2 a3 b0 b1 b2 b3; decide +kernel

theorem b_lo4_bits_of_targVal_eq {m2 m0 : Fin 100 → Bool}
    (h : targVal b_lo4_w m2 = bLo4InitVal m0) :
    m2 ⟨47, by decide⟩ = bLo4InitBit0 m0 ∧
    m2 ⟨69, by decide⟩ = bLo4InitBit1 m0 ∧
    m2 ⟨70, by decide⟩ = m0 ⟨70, by decide⟩ ∧
    m2 ⟨71, by decide⟩ = m0 ⟨71, by decide⟩ := by
  dsimp only [b_lo4_w, targVal, bLo4InitVal] at h
  rw [dite_eq_left (by decide : 47 < 100), dite_eq_left (by decide : 69 < 100),
      dite_eq_left (by decide : 70 < 100), dite_eq_left (by decide : 71 < 100)] at h
  exact four_bits_of_val_eq h

def clean3bOut : List Nat :=
  [50, 51, 53, 54, 55, 56, 57, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 94, 95, 96, 97, 98, 99]

def clean41pOut : List Nat :=
  52 :: 85 :: 86 ::
    [50, 51, 53, 54, 55, 56, 57, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68,
     94, 95, 96, 97, 98, 99]

def stages4_2_to_5_2Core : List Op102 :=
  s4_2Ops ++ s4_3Ops ++ s4_4Ops ++ s5_1Ops ++ s5_2CoreOps

theorem exec_s4_1Ops_init {m_s3b : Fin 100 → Bool}
    (hcl3b : ∀ w : Fin 100, w.val ∈ clean3bOut → m_s3b w = false) :
    ∃ m_s4_1 : Fin 100 → Bool,
      execList102 s4_1Ops m_s3b = some m_s4_1 ∧
      (∀ w : Fin 100, w.val ∉ b_lo4_w → m_s4_1 w = m_s3b w) ∧
      m_s4_1 ⟨47, by decide⟩ = evalSymMask 120 (buildSymEnv 120 m_s3b defs_4_1) mask47_s41 ∧
      targVal b_lo4_w m_s4_1 =
        (bLo4InitVal m_s3b +
          evalBag 120 (buildSymEnv 120 m_s3b defs_4_1) (wWideBag53.take 4)) % 16 := by
  have hcl41 : ∀ w : Fin 100, w.val ∈ clean_4_1 → m_s3b w = false := by
    intro w hw
    have hsub : ∀ x ∈ clean_4_1, x ∈ clean3bOut := by decide +kernel
    exact hcl3b w (hsub w.val hw)
  obtain ⟨m_s4_1, hex41, hnon41, h47_41, hval41⟩ := exec_s4_1Ops hcl41
  rw [evalMasksVal_b_lo4_init] at hval41
  exact ⟨m_s4_1, hex41, hnon41, h47_41, hval41⟩

theorem exec_stages4_2_to_5_2Core {m_s3b m_s4_1 m_s4_1p : Fin 100 → Bool} {kv lv s4 u : Nat}
    (hcl3b : ∀ w : Fin 100, w.val ∈ clean3bOut → m_s3b w = false)
    (hnon41 : ∀ w : Fin 100, w.val ∉ b_lo4_w → m_s4_1 w = m_s3b w)
    (hm41p_52 : m_s4_1p ⟨52, by decide⟩ = false)
    (hm41p_85 : m_s4_1p ⟨85, by decide⟩ = false)
    (hm41p_86 : m_s4_1p ⟨86, by decide⟩ = false)
    (hm41p_ne86 : ∀ w : Fin 100, w.val ∉ [52, 81, 85, 86] → m_s4_1p w = m_s4_1 w)
    (hu : ∀ (k : Nat) (hk : k < 16), m_s3b ⟨25 + k, by omega⟩ = uRotBit u s4 k)
    (hkv : ∀ (b : Nat) (hb : b < 8), m_s3b ⟨72 + b, by omega⟩ = kv.testBit b)
    (hlv0 : xor (xor (xor (xor
        (m_s3b ⟨44, by decide⟩ && xor (m_s3b ⟨46, by decide⟩) (m_s3b ⟨41, by decide⟩))
        (m_s3b ⟨41, by decide⟩)) (m_s3b ⟨48, by decide⟩)) (m_s3b ⟨58, by decide⟩)) true =
      lv.testBit 0)
    (hlv : ∀ (j : Nat) (hj : j < 7), m_s3b ⟨87 + j, by omega⟩ = lv.testBit (1 + j)) :
    ∃ m_s5_2c : Fin 100 → Bool,
      execList102 stages4_2_to_5_2Core m_s4_1p = some m_s5_2c ∧
      (∀ w : Fin 100, 25 ≤ w.val → m_s5_2c w = m_s4_1p w) ∧
      ∃ N_val : Nat,
        N_val + negSlopeNarrow kv s4 u =
          curvVal27 lv (d9Val u s4) + posSlopeNarrow kv s4 u + slopeConstNarrow kv +
          2 * (cond (xor (xor (m_s3b ⟨31, by decide⟩) (m_s3b ⟨80, by decide⟩)) true) 1 0) +
          2 * (cond (xor (xor (m_s3b ⟨29, by decide⟩) (m_s3b ⟨82, by decide⟩)) true) 1 0) +
          4 * (cond (xor (xor (m_s3b ⟨32, by decide⟩) (m_s3b ⟨80, by decide⟩)) true) 1 0) +
          4 * (cond (xor (xor (m_s3b ⟨30, by decide⟩) (m_s3b ⟨82, by decide⟩)) true) 1 0) +
          16 * (cond (xor (xor (m_s3b ⟨34, by decide⟩) (m_s3b ⟨80, by decide⟩)) true) 1 0) ∧
        targVal z_w m_s5_2c =
          (targVal z_w m_s3b + (targVal b_lo4_w m_s4_1 + N_val) / 16) % 33554432 := by
  have h41p_3b :
      ∀ w : Fin 100, w.val ∉ b_lo4_w → w.val ∉ [52, 81, 85, 86] → m_s4_1p w = m_s3b w := by
    intro w h1 h2; rw [hm41p_ne86 w h2, hnon41 w h1]
  have hcl41p : ∀ w : Fin 100, w.val ∈ clean41pOut → m_s4_1p w = false := by
    intro w hw
    rcases List.mem_cons.mp hw with h52 | hw1
    · have hfin : w = ⟨52, by decide⟩ := Fin.ext h52
      rwa [hfin]
    · rcases List.mem_cons.mp hw1 with h85 | hw2
      · have hfin : w = ⟨85, by decide⟩ := Fin.ext h85
        rwa [hfin]
      · rcases List.mem_cons.mp hw2 with h86 | hmem
        · have hfin : w = ⟨86, by decide⟩ := Fin.ext h86
          rwa [hfin]
        · have hnot_b : ∀ x ∈ [50, 51, 53, 54, 55, 56, 57, 59, 60, 61, 62, 63, 64, 65,
              66, 67, 68, 94, 95, 96, 97, 98, 99],
              x ∉ b_lo4_w ∧ x ∉ [52, 81, 85, 86] ∧ x ∈ clean3bOut := by decide +kernel
          obtain ⟨h1, h2, h3⟩ := hnot_b w.val hmem
          rw [h41p_3b w h1 h2]
          exact hcl3b w h3
  have hu41 : ∀ (k : Nat) (hk : k < 10), m_s4_1p ⟨31 + k, by omega⟩ = uRotBit u s4 (6 + k) := by
    intro k hk
    have hnot : 31 + k ∉ b_lo4_w ∧ 31 + k ∉ [52, 81, 85, 86] := by revert k hk; decide +kernel
    have hfin : (⟨31 + k, by omega⟩ : Fin 100) = ⟨25 + (6 + k), by omega⟩ :=
      Fin.ext (by dsimp; omega)
    rw [h41p_3b ⟨31 + k, by omega⟩ hnot.1 hnot.2, hfin, hu (6 + k) (by omega)]
  have hcl42 : ∀ w : Fin 100, w.val ∈ clean_4_2 → m_s4_1p w = false := by
    intro w hw
    have hsub : ∀ x ∈ clean_4_2, x ∈ clean41pOut := by decide +kernel
    exact hcl41p w (hsub w.val hw)
  obtain ⟨m_s4_2, hex42, hnon42, _, hsq9_42⟩ := exec_s4_2Ops hu41 hcl42
  have h42_eq_41p : ∀ w : Fin 100, w.val ∉ sq9_w → m_s4_2 w = m_s4_1p w :=
    fun w h2 => hnon42 w h2
  have h42_eq_3b : ∀ w : Fin 100,
      w.val ∉ b_lo4_w → w.val ∉ sq9_w → w.val ∉ [52, 81, 85, 86] → m_s4_2 w = m_s3b w := by
    intro w h1 h2 h3; rw [hnon42 w h2, h41p_3b w h1 h3]
  have hcl43 : ∀ w : Fin 100, w.val ∈ clean_4_3 → m_s4_2 w = false := by
    intro w hw
    have hnot2 : ∀ x ∈ clean_4_3, x ∉ sq9_w := by decide +kernel
    have hsub : ∀ x ∈ clean_4_3, x ∈ clean41pOut := by decide +kernel
    rw [h42_eq_41p w (hnot2 w.val hw)]
    exact hcl41p w (hsub w.val hw)
  obtain ⟨m_s4_3, hex43, hnon43, _, hhi43⟩ := exec_s4_3Ops hcl43
  have hcl44 : ∀ w : Fin 100, w.val ∈ clean_4_4 → m_s4_3 w = false := by
    intro w hw
    have hnot3 : ∀ x ∈ clean_4_4, x ∉ out_4_3 := by decide +kernel
    have hnot2 : ∀ x ∈ clean_4_4, x ∉ sq9_w := by decide +kernel
    have hsub : ∀ x ∈ clean_4_4, x ∈ clean41pOut := by decide +kernel
    rw [hnon43 w (hnot3 w.val hw), h42_eq_41p w (hnot2 w.val hw)]
    exact hcl41p w (hsub w.val hw)
  obtain ⟨m_s4_4, hex44, hge25_44, hz44⟩ := exec_s4_4Ops hcl44
  obtain ⟨m_s5_1, hex51, hlt25_51, hge25_51⟩ := exec_s5_1Ops hcl43 hex43 hge25_44
  obtain ⟨m_s5_2c, hex52c, hlt25_52c, hge25_52c⟩ := exec_s5_2CoreOps hu41 hcl42 hex42 hge25_51
  have hex_all : execList102 stages4_2_to_5_2Core m_s4_1p = some m_s5_2c := by
    unfold stages4_2_to_5_2Core
    rw [List.append_assoc, List.append_assoc, List.append_assoc]
    exact execList102_append_eq hex42
      (execList102_append_eq hex43 (execList102_append_eq hex44
        (execList102_append_eq hex51 hex52c)))
  have hb_42_eq_41 : targVal b_lo4_w m_s4_2 = targVal b_lo4_w m_s4_1 := by
    refine targVal_congr (fun w hw => ?_)
    have hdisj : ∀ x ∈ b_lo4_w, x ∉ sq9_w ∧ x ∉ [52, 81, 85, 86] := by decide +kernel
    obtain ⟨h1, h2⟩ := hdisj w.val hw
    rw [hnon42 w h1, hm41p_ne86 w h2]
  have hz_43_eq_3b : targVal z_w m_s4_3 = targVal z_w m_s3b := by
    refine targVal_congr (fun w hw => ?_)
    have hlt25 : w.val < 25 := (mem_rangeList_iff.mp hw).2
    have hnot3 : w.val ∉ out_4_3 := by revert w hlt25; decide +kernel
    have hnot2 : w.val ∉ sq9_w := by revert w hlt25; decide +kernel
    have hnot1 : w.val ∉ b_lo4_w := by revert w hlt25; decide +kernel
    have hne86 : w.val ∉ [52, 81, 85, 86] := by simp; omega
    rw [hnon43 w hnot3, h42_eq_3b w hnot1 hnot2 hne86]
  have hz_52c_eq_44 : targVal z_w m_s5_2c = targVal z_w m_s4_4 := by
    refine targVal_congr (fun w hw => ?_)
    have hlt25 : w.val < 25 := (mem_rangeList_iff.mp hw).2
    rw [hlt25_52c w hlt25, hlt25_51 w hlt25]
  have hu42 : ∀ (k : Nat) (hk : k < 16), m_s4_2 ⟨25 + k, by omega⟩ = uRotBit u s4 k := by
    intro k hk
    have hnot1 : 25 + k ∉ b_lo4_w := by revert k hk; decide +kernel
    have hnot2 : 25 + k ∉ sq9_w := by revert k hk; decide +kernel
    have hne86 : 25 + k ∉ [52, 81, 85, 86] := by simp; omega
    rw [h42_eq_3b ⟨25 + k, by omega⟩ hnot1 hnot2 hne86, hu k hk]
  have hkv42 : ∀ (b : Nat) (hb : b < 8), m_s4_2 ⟨72 + b, by omega⟩ = kv.testBit b := by
    intro b hb
    have hnot1 : 72 + b ∉ b_lo4_w := by revert b hb; decide +kernel
    have hnot2 : 72 + b ∉ sq9_w := by revert b hb; decide +kernel
    have hne86 : 72 + b ∉ [52, 81, 85, 86] := by simp; omega
    rw [h42_eq_3b ⟨72 + b, by omega⟩ hnot1 hnot2 hne86, hkv b hb]
  have hlv42 : ∀ (j : Nat) (hj : j < 7), m_s4_2 ⟨87 + j, by omega⟩ = lv.testBit (1 + j) := by
    intro j hj
    have hnot1 : 87 + j ∉ b_lo4_w := by revert j hj; decide +kernel
    have hnot2 : 87 + j ∉ sq9_w := by revert j hj; decide +kernel
    have hne86 : 87 + j ∉ [52, 81, 85, 86] := by simp; omega
    rw [h42_eq_3b ⟨87 + j, by omega⟩ hnot1 hnot2 hne86, hlv j hj]
  have hlv0_42 : evalSymMask 210 (buildSymEnv 210 m_s4_2 defs_4_3) l8_0_m = lv.testBit 0 := by
    rw [evalSymMask_l8_0_m,
        h42_eq_3b ⟨44, by decide⟩ (by decide) (by decide) (by decide),
        h42_eq_3b ⟨46, by decide⟩ (by decide) (by decide) (by decide),
        h42_eq_3b ⟨41, by decide⟩ (by decide) (by decide) (by decide),
        h42_eq_3b ⟨48, by decide⟩ (by decide) (by decide) (by decide),
        h42_eq_3b ⟨58, by decide⟩ (by decide) (by decide) (by decide),
        hlv0]
  have hdisj44 : bagDisjoint out_4_3 nNarrowBag44 = true := by decide +kernel
  have hN44_eq : evalBag 135 (buildSymEnv 135 m_s4_3 defs_4_4) nNarrowBag44 =
      evalBag 210 (buildSymEnv 210 m_s4_2 defs_4_3) nNarrowBag44 :=
    evalBag_congr_disjoint (by decide) (by decide) hnon43 nNarrowBag44 hdisj44
  have hN_sp := evalBag_nNarrowBag_split 210 (buildSymEnv 210 m_s4_2 defs_4_3)
  have hN_narrow := evalBag_nNarrowBag (N := 210) (defs := defs_4_3) (by decide)
    hu42 hkv42 hlv0_42 hlv42 hsq9_42
  have hm_c1_0 : evalSymMask 210 (buildSymEnv 210 m_s4_2 defs_4_3) movedMask_c1_0 =
      xor (xor (m_s3b ⟨31, by decide⟩) (m_s3b ⟨80, by decide⟩)) true := by
    unfold movedMask_c1_0
    rw [evalSymMask_xor, evalSymMask_xor,
        evalSymMask_wMask (N := 210) (by decide) (by decide : 31 < 100),
        evalSymMask_wMask (N := 210) (by decide) (by decide : 80 < 100),
        evalSymMask_one (N := 210) (by decide),
        h42_eq_3b ⟨31, by decide⟩ (by decide) (by decide) (by decide),
        h42_eq_3b ⟨80, by decide⟩ (by decide) (by decide) (by decide)]
  have hm_c1_2 : evalSymMask 210 (buildSymEnv 210 m_s4_2 defs_4_3) movedMask_c1_2 =
      xor (xor (m_s3b ⟨29, by decide⟩) (m_s3b ⟨82, by decide⟩)) true := by
    unfold movedMask_c1_2
    rw [evalSymMask_xor, evalSymMask_xor,
        evalSymMask_wMask (N := 210) (by decide) (by decide : 29 < 100),
        evalSymMask_wMask (N := 210) (by decide) (by decide : 82 < 100),
        evalSymMask_one (N := 210) (by decide),
        h42_eq_3b ⟨29, by decide⟩ (by decide) (by decide) (by decide),
        h42_eq_3b ⟨82, by decide⟩ (by decide) (by decide) (by decide)]
  have hm_c2_0 : evalSymMask 210 (buildSymEnv 210 m_s4_2 defs_4_3) movedMask_c2_0 =
      xor (xor (m_s3b ⟨32, by decide⟩) (m_s3b ⟨80, by decide⟩)) true := by
    unfold movedMask_c2_0
    rw [evalSymMask_xor, evalSymMask_xor,
        evalSymMask_wMask (N := 210) (by decide) (by decide : 32 < 100),
        evalSymMask_wMask (N := 210) (by decide) (by decide : 80 < 100),
        evalSymMask_one (N := 210) (by decide),
        h42_eq_3b ⟨32, by decide⟩ (by decide) (by decide) (by decide),
        h42_eq_3b ⟨80, by decide⟩ (by decide) (by decide) (by decide)]
  have hm_c2_2 : evalSymMask 210 (buildSymEnv 210 m_s4_2 defs_4_3) movedMask_c2_2 =
      xor (xor (m_s3b ⟨30, by decide⟩) (m_s3b ⟨82, by decide⟩)) true := by
    unfold movedMask_c2_2
    rw [evalSymMask_xor, evalSymMask_xor,
        evalSymMask_wMask (N := 210) (by decide) (by decide : 30 < 100),
        evalSymMask_wMask (N := 210) (by decide) (by decide : 82 < 100),
        evalSymMask_one (N := 210) (by decide),
        h42_eq_3b ⟨30, by decide⟩ (by decide) (by decide) (by decide),
        h42_eq_3b ⟨82, by decide⟩ (by decide) (by decide) (by decide)]
  have hm_c4 : evalSymMask 210 (buildSymEnv 210 m_s4_2 defs_4_3) movedMask_c4 =
      xor (xor (m_s3b ⟨34, by decide⟩) (m_s3b ⟨80, by decide⟩)) true := by
    unfold movedMask_c4
    rw [evalSymMask_xor, evalSymMask_xor,
        evalSymMask_wMask (N := 210) (by decide) (by decide : 34 < 100),
        evalSymMask_wMask (N := 210) (by decide) (by decide : 80 < 100),
        evalSymMask_one (N := 210) (by decide),
        h42_eq_3b ⟨34, by decide⟩ (by decide) (by decide) (by decide),
        h42_eq_3b ⟨80, by decide⟩ (by decide) (by decide) (by decide)]
  rw [hm_c1_0, hm_c1_2, hm_c2_0, hm_c2_2, hm_c4] at hN_sp
  refine ⟨m_s5_2c, hex_all, hge25_52c,
    16 * evalBag 210 (buildSymEnv 210 m_s4_2 defs_4_3) nNarrowBag44 +
      evalBag 210 (buildSymEnv 210 m_s4_2 defs_4_3) nNarrowBag43, by omega, ?_⟩
  rw [hz_52c_eq_44, hz44, hz_43_eq_3b, hhi43, hN44_eq, hb_42_eq_41]
  omega

theorem exec_stage5_3_combine {m_s3b m_s4_1 m_s5_2f : Fin 100 → Bool}
    {Z_init b_base kv lv s4 u b_res19 N_val : Nat}
    (hz_le : zNeg27 kv s4 u ≤ zPos27 b_base kv lv s4 u)
    (hd_lt : deltaPos25 b_base kv lv s4 u < 16777216)
    (hu : ∀ (k : Nat) (hk : k < 16), m_s3b ⟨25 + k, by omega⟩ = uRotBit u s4 k)
    (hkv_hi : ∀ (b : Nat) (hb1 : 8 ≤ b) (hb2 : b < 15), m_s3b ⟨72 + b, by omega⟩ = kv.testBit b)
    (hN_narrow : N_val + negSlopeNarrow kv s4 u =
      curvVal27 lv (d9Val u s4) + posSlopeNarrow kv s4 u + slopeConstNarrow kv +
      2 * (cond (xor (xor (m_s3b ⟨31, by decide⟩) (m_s3b ⟨80, by decide⟩)) true) 1 0) +
      2 * (cond (xor (xor (m_s3b ⟨29, by decide⟩) (m_s3b ⟨82, by decide⟩)) true) 1 0) +
      4 * (cond (xor (xor (m_s3b ⟨32, by decide⟩) (m_s3b ⟨80, by decide⟩)) true) 1 0) +
      4 * (cond (xor (xor (m_s3b ⟨30, by decide⟩) (m_s3b ⟨82, by decide⟩)) true) 1 0) +
      16 * (cond (xor (xor (m_s3b ⟨34, by decide⟩) (m_s3b ⟨80, by decide⟩)) true) 1 0))
    (hbase_eq : 16 * b_res19 +
        4194304 * u18_val (m_s3b ⟨44, by decide⟩) (m_s3b ⟨45, by decide⟩)
          (m_s3b ⟨46, by decide⟩) (m_s3b ⟨48, by decide⟩)
          (m_s3b ⟨58, by decide⟩) (m_s3b ⟨47, by decide⟩) +
        bLo4InitVal m_s3b + slopeConst27 kv + 1024 =
      b_base + 536870912 * (cond (u18_q19_4 (m_s3b ⟨48, by decide⟩) (m_s3b ⟨58, by decide⟩)
        (m_s3b ⟨47, by decide⟩)) 1 0))
    (h47_41 : m_s4_1 ⟨47, by decide⟩ = evalSymMask 120 (buildSymEnv 120 m_s3b defs_4_1) mask47_s41)
    (hval41 : targVal b_lo4_w m_s4_1 =
      (bLo4InitVal m_s3b + evalBag 120 (buildSymEnv 120 m_s3b defs_4_1) (wWideBag53.take 4)) % 16)
    (hz3b : targVal z_w m_s3b = (Z_init + u + b_res19) % 33554432)
    (hz52f : targVal z_w m_s5_2f =
      (targVal z_w m_s3b + (targVal b_lo4_w m_s4_1 + N_val) / 16) % 33554432)
    (hb52f : ∀ w : Fin 100, w.val ∈ b_lo4_w → m_s5_2f w = m_s4_1 w)
    (hkeep52f : ∀ w : Fin 100, w.val ∉ badW_41_53 → m_s5_2f w = m_s3b w)
    (hcl53 : ∀ w : Fin 100, w.val ∈ clean_5_3 → m_s5_2f w = false) :
    ∃ m_s5_3 : Fin 100 → Bool,
      execList102 s5_3Ops m_s5_2f = some m_s5_3 ∧
      (∀ w : Fin 100, w.val ∉ out_5_3 ++ extra_5_3.map Prod.fst → m_s5_3 w = m_s5_2f w) ∧
      m_s5_3 ⟨47, by decide⟩ = bLo4InitBit0 m_s3b ∧
      m_s5_3 ⟨69, by decide⟩ = bLo4InitBit1 m_s3b ∧
      m_s5_3 ⟨70, by decide⟩ = m_s3b ⟨70, by decide⟩ ∧
      m_s5_3 ⟨71, by decide⟩ = m_s3b ⟨71, by decide⟩ ∧
      m_s5_3 ⟨52, by decide⟩ = u18_q0 (m_s3b ⟨45, by decide⟩) (m_s3b ⟨46, by decide⟩)
        (m_s3b ⟨48, by decide⟩) (m_s3b ⟨58, by decide⟩) (m_s3b ⟨47, by decide⟩) ∧
      m_s5_3 ⟨97, by decide⟩ = u18_q19_0 (m_s3b ⟨46, by decide⟩) (m_s3b ⟨48, by decide⟩)
        (m_s3b ⟨58, by decide⟩) (m_s3b ⟨47, by decide⟩) ∧
      m_s5_3 ⟨72, by decide⟩ = u18_q19_1 (m_s3b ⟨45, by decide⟩) (m_s3b ⟨46, by decide⟩)
        (m_s3b ⟨48, by decide⟩) (m_s3b ⟨58, by decide⟩) (m_s3b ⟨47, by decide⟩) ∧
      m_s5_3 ⟨56, by decide⟩ = u18_q19_2 (m_s3b ⟨45, by decide⟩) (m_s3b ⟨46, by decide⟩)
        (m_s3b ⟨48, by decide⟩) (m_s3b ⟨58, by decide⟩) (m_s3b ⟨47, by decide⟩) ∧
      m_s5_3 ⟨98, by decide⟩ = u18_q19_3 (m_s3b ⟨48, by decide⟩) (m_s3b ⟨58, by decide⟩)
        (m_s3b ⟨47, by decide⟩) ∧
      m_s5_3 ⟨99, by decide⟩ = u18_q19_4 (m_s3b ⟨48, by decide⟩) (m_s3b ⟨58, by decide⟩)
        (m_s3b ⟨47, by decide⟩) ∧
      targVal z_w m_s5_3 = (Z_init + deltaPos25 b_base kv lv s4 u) % 33554432 := by
  have hkeep_sym : ∀ w : Fin 100, w.val ∉ badW_41_53 → m_s3b w = m_s5_2f w :=
    fun w hw => (hkeep52f w hw).symm
  have hbag_eq := evalBag_congr_disjoint (m1 := m_s3b) (m2 := m_s5_2f)
    (defs1 := defs_4_1) (defs2 := defs_5_3) (by decide : 103 ≤ 120) (by decide : 103 ≤ 274)
    hkeep_sym (wWideBag53.take 4) bagDisjoint_wWide_take4
  have hb_eq : targVal b_lo4_w m_s5_2f =
      (bLo4InitVal m_s3b +
        evalBag 274 (buildSymEnv 274 m_s5_2f defs_5_3) (wWideBag53.take 4)) % 16 := by
    rw [targVal_congr hb52f, hval41, hbag_eq]
  obtain ⟨m_s5_3, hex53, hnon53, hext53, hb_out, hz_out⟩ :=
    exec_s5_3Ops (bLo4InitVal_lt m_s3b) hcl53 hb_eq
  obtain ⟨hbit47, hbit69, hbit70, hbit71⟩ := b_lo4_bits_of_targVal_eq hb_out
  have h47_52f :
      m_s5_2f ⟨47, by decide⟩ = evalSymMask 120 (buildSymEnv 120 m_s3b defs_4_1) mask47_s41 := by
    rw [hb52f ⟨47, by decide⟩ (by decide), h47_41]
  have hm47_53 := evalSymMask_mask47_s41 h47_52f hkeep52f
  obtain ⟨hcin0, hq0, hq19_0, hq19_1, hq19_2, hq19_3, hq19_4, hu18_val⟩ :=
    evalSymMask_u18 m_s5_2f hm47_53
  have hw44 : m_s5_2f ⟨44, by decide⟩ = m_s3b ⟨44, by decide⟩ :=
    hkeep52f ⟨44, by decide⟩ (by decide)
  have hw45 : m_s5_2f ⟨45, by decide⟩ = m_s3b ⟨45, by decide⟩ :=
    hkeep52f ⟨45, by decide⟩ (by decide)
  have hw46 : m_s5_2f ⟨46, by decide⟩ = m_s3b ⟨46, by decide⟩ :=
    hkeep52f ⟨46, by decide⟩ (by decide)
  have hw48 : m_s5_2f ⟨48, by decide⟩ = m_s3b ⟨48, by decide⟩ :=
    hkeep52f ⟨48, by decide⟩ (by decide)
  have hw58 : m_s5_2f ⟨58, by decide⟩ = m_s3b ⟨58, by decide⟩ :=
    hkeep52f ⟨58, by decide⟩ (by decide)
  simp only [hw44, hw45, hw46, hw48, hw58] at hcin0 hq0 hq19_0 hq19_1 hq19_2 hq19_3 hq19_4 hu18_val
  have hm52 := (hext53 (52, q0_m) (by decide) (by decide)).trans hq0
  have hm97 := (hext53 (97, q19_0_m) (by decide) (by decide)).trans hq19_0
  have hm72 := (hext53 (72, q19_1_m) (by decide) (by decide)).trans hq19_1
  have hm56 := (hext53 (56, q19_2_m) (by decide) (by decide)).trans hq19_2
  have hm98 := (hext53 (98, q19_3_m) (by decide) (by decide)).trans hq19_3
  have hm99 := (hext53 (99, q19_4_m) (by decide) (by decide)).trans hq19_4
  have hu52f : ∀ (k : Nat) (hk : k < 16), m_s5_2f ⟨25 + k, by omega⟩ = uRotBit u s4 k := by
    intro k hk
    have hnot : 25 + k ∉ badW_41_53 := by revert k hk; decide +kernel
    rw [hkeep52f ⟨25 + k, by omega⟩ hnot, hu k hk]
  have hkv52f :
      ∀ (b : Nat) (hb1 : 8 ≤ b) (hb2 : b < 15), m_s5_2f ⟨72 + b, by omega⟩ = kv.testBit b := by
    intro b hb1 hb2
    have hnot : 72 + b ∉ badW_41_53 := by revert b hb1 hb2; decide +kernel
    rw [hkeep52f ⟨72 + b, by omega⟩ hnot, hkv_hi b hb1 hb2]
  have hW_wide := evalBag_wWideBag hu52f hkv52f
  dsimp only at hW_wide
  rw [hu18_val] at hW_wide
  have hW_sp := evalBag_wWideBag_split 274 (buildSymEnv 274 m_s5_2f defs_5_3)
  have hm53_c1_0 : evalSymMask 274 (buildSymEnv 274 m_s5_2f defs_5_3) movedMask_c1_0 =
      xor (xor (m_s3b ⟨31, by decide⟩) (m_s3b ⟨80, by decide⟩)) true := by
    unfold movedMask_c1_0
    rw [evalSymMask_xor, evalSymMask_xor,
        evalSymMask_wMask (N := 274) (by decide) (by decide : 31 < 100),
        evalSymMask_wMask (N := 274) (by decide) (by decide : 80 < 100),
        evalSymMask_one (N := 274) (by decide),
        hkeep52f ⟨31, by decide⟩ (by decide),
        hkeep52f ⟨80, by decide⟩ (by decide)]
  have hm53_c1_2 : evalSymMask 274 (buildSymEnv 274 m_s5_2f defs_5_3) movedMask_c1_2 =
      xor (xor (m_s3b ⟨29, by decide⟩) (m_s3b ⟨82, by decide⟩)) true := by
    unfold movedMask_c1_2
    rw [evalSymMask_xor, evalSymMask_xor,
        evalSymMask_wMask (N := 274) (by decide) (by decide : 29 < 100),
        evalSymMask_wMask (N := 274) (by decide) (by decide : 82 < 100),
        evalSymMask_one (N := 274) (by decide),
        hkeep52f ⟨29, by decide⟩ (by decide),
        hkeep52f ⟨82, by decide⟩ (by decide)]
  have hm53_c2_0 : evalSymMask 274 (buildSymEnv 274 m_s5_2f defs_5_3) movedMask_c2_0 =
      xor (xor (m_s3b ⟨32, by decide⟩) (m_s3b ⟨80, by decide⟩)) true := by
    unfold movedMask_c2_0
    rw [evalSymMask_xor, evalSymMask_xor,
        evalSymMask_wMask (N := 274) (by decide) (by decide : 32 < 100),
        evalSymMask_wMask (N := 274) (by decide) (by decide : 80 < 100),
        evalSymMask_one (N := 274) (by decide),
        hkeep52f ⟨32, by decide⟩ (by decide),
        hkeep52f ⟨80, by decide⟩ (by decide)]
  have hm53_c2_2 : evalSymMask 274 (buildSymEnv 274 m_s5_2f defs_5_3) movedMask_c2_2 =
      xor (xor (m_s3b ⟨30, by decide⟩) (m_s3b ⟨82, by decide⟩)) true := by
    unfold movedMask_c2_2
    rw [evalSymMask_xor, evalSymMask_xor,
        evalSymMask_wMask (N := 274) (by decide) (by decide : 30 < 100),
        evalSymMask_wMask (N := 274) (by decide) (by decide : 82 < 100),
        evalSymMask_one (N := 274) (by decide),
        hkeep52f ⟨30, by decide⟩ (by decide),
        hkeep52f ⟨82, by decide⟩ (by decide)]
  have hm53_c4 : evalSymMask 274 (buildSymEnv 274 m_s5_2f defs_5_3) movedMask_c4 =
      xor (xor (m_s3b ⟨34, by decide⟩) (m_s3b ⟨80, by decide⟩)) true := by
    unfold movedMask_c4
    rw [evalSymMask_xor, evalSymMask_xor,
        evalSymMask_wMask (N := 274) (by decide) (by decide : 34 < 100),
        evalSymMask_wMask (N := 274) (by decide) (by decide : 80 < 100),
        evalSymMask_one (N := 274) (by decide),
        hkeep52f ⟨34, by decide⟩ (by decide),
        hkeep52f ⟨80, by decide⟩ (by decide)]
  rw [hm53_c1_0, hm53_c1_2, hm53_c2_0, hm53_c2_2, hm53_c4] at hW_sp
  have hNW_eq :
      N_val + evalBag 274 (buildSymEnv 274 m_s5_2f defs_5_3) wWideBag53 + negSlope27 kv s4 u =
      curvVal27 lv (d9Val u s4) + posSlope27 kv s4 u + slopeConst27 kv +
      4194304 * u18_val (m_s3b ⟨44, by decide⟩) (m_s3b ⟨45, by decide⟩)
        (m_s3b ⟨46, by decide⟩) (m_s3b ⟨48, by decide⟩)
        (m_s3b ⟨58, by decide⟩) (m_s3b ⟨47, by decide⟩) := by
    unfold negSlope27 posSlope27 slopeConst27
    unfold negSlopeNarrow posSlopeNarrow slopeConstNarrow at hN_narrow
    unfold negSlopeWide posSlopeWide slopeConstWide at hW_wide
    omega
  have hcomb := stages45_arith_combine hz_le hd_lt hbase_eq hNW_eq
  dsimp only at hcomb
  have hx_52f : targVal b_lo4_w m_s4_1 =
      (bLo4InitVal m_s3b + evalBag 274 (buildSymEnv 274 m_s5_2f defs_5_3) wWideBag53) % 16 := by
    rw [hval41, hbag_eq,
        evalBag_take_four 274 (buildSymEnv 274 m_s5_2f defs_5_3) wWideBag53 (by decide)]
    omega
  refine ⟨m_s5_3, hex53, hnon53, hbit47, hbit69, hbit70, hbit71,
    hm52, hm97, hm72, hm56, hm98, hm99, ?_⟩
  rw [hz_out, hz52f, hz3b, hx_52f]
  have hmod_assoc :
      (((Z_init + u + b_res19) % 33554432 +
        ((bLo4InitVal m_s3b +
          evalBag 274 (buildSymEnv 274 m_s5_2f defs_5_3) wWideBag53) % 16 + N_val) / 16) %
          33554432 +
        (bLo4InitVal m_s3b +
          evalBag 274 (buildSymEnv 274 m_s5_2f defs_5_3) wWideBag53) / 16) % 33554432 =
      (Z_init + ((u + b_res19 +
        ((bLo4InitVal m_s3b +
          evalBag 274 (buildSymEnv 274 m_s5_2f defs_5_3) wWideBag53) % 16 + N_val) / 16 +
        (bLo4InitVal m_s3b +
          evalBag 274 (buildSymEnv 274 m_s5_2f defs_5_3) wWideBag53) / 16) %
          33554432)) % 33554432 := by
    omega
  rw [hmod_assoc, hcomb]

theorem execList102_revOps_congr_sub (p : Nat → Bool) {ops : List Op102}
    (hnq : (ops.all Op102.noUnquad) = true)
    (hp : ((revOps ops).all (Op102.inSub p)) = true)
    {m0 m1 m2 : Fin 100 → Bool}
    (hfwd : execList102 ops m0 = some m1)
    (hin : ∀ w : Fin 100, p w.val = true → m2 w = m1 w) :
    ∃ m2', execList102 (revOps ops) m2 = some m2' ∧
      (∀ w : Fin 100, p w.val = false → m2' w = m2 w) ∧
      (∀ w : Fin 100, p w.val = true → m2' w = m0 w) :=
  execList102_congr_sub p (revOps ops) hp (execList102_revOps ops hnq hfwd) hin

def Op102.andCount : Op102 → Nat
  | .and4t _ _ _ => 1
  | .rccx0 _ _ _ => 1
  | .rccx1 _ _ _ => 1
  | _ => 0

def Op102.tCount : Op102 → Nat
  | .and4t _ _ _ => 4
  | .rccx0 _ _ _ => 4
  | .rccx1 _ _ _ => 4
  | .hGadget _ pos neg _ _ => pos.length + neg.length
  | _ => 0

theorem map_andCount_append (l1 l2 : List Op102) :
    ((l1 ++ l2).map Op102.andCount).sum =
      (l1.map Op102.andCount).sum + (l2.map Op102.andCount).sum := by
  rw [List.map_append, List.sum_append]

theorem map_tCount_append (l1 l2 : List Op102) :
    ((l1 ++ l2).map Op102.tCount).sum = (l1.map Op102.tCount).sum + (l2.map Op102.tCount).sum := by
  rw [List.map_append, List.sum_append]

def seqAndCount (seq : List (List Op102)) : Nat :=
  (seq.map (fun l => (l.map Op102.andCount).sum)).sum

def seqTCount (seq : List (List Op102)) : Nat :=
  (seq.map (fun l => (l.map Op102.tCount).sum)).sum

theorem map_andCount_flatten : ∀ (seq : List (List Op102)),
    ((seq.flatten).map Op102.andCount).sum = seqAndCount seq
  | [] => rfl
  | l :: seq => by
    simp only [List.flatten_cons, map_andCount_append, seqAndCount, List.map_cons, List.sum_cons,
      map_andCount_flatten seq]

theorem map_tCount_flatten : ∀ (seq : List (List Op102)),
    ((seq.flatten).map Op102.tCount).sum = seqTCount seq
  | [] => rfl
  | l :: seq => by
    simp only [List.flatten_cons, map_tCount_append, seqTCount, List.map_cons, List.sum_cons,
      map_tCount_flatten seq]

def isParWire (q : Nat) : Bool :=
  (Nat.ble 25 q && Nat.blt q 49) || (Nat.ble 50 q && Nat.blt q 100)

theorem isParWire_bounds {q : Nat} (h : isParWire q = true) :
    25 ≤ q ∧ q < 100 ∧ q ≠ 49 ∧ (q < 49 ∨ 50 ≤ q) := by
  unfold isParWire at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

def getFMask (fMask : Nat → Nat) (q : Nat) : Nat :=
  if q < 49 then fMask (q - 25) else 0

structure ParInv (bit allM : Nat) (fMask : Nat → Nat) (m1 : Fin 100 → Bool)
    (tr : WTree) (m : Fin 100 → Bool) : Prop where
  wf : WTreeWF 7 tr
  hAll : allM.testBit bit = true
  hFree : ∀ w : Fin 100,
    (25 ≤ w.val ∧ w.val < 49 ∧ (fMask (w.val - 25)).testBit bit = true) ∨ w.val = 49 →
    m w = m1 w
  hTracked : ∀ w : Fin 100,
    isParWire w.val = true → (getFMask fMask w.val).testBit bit = false →
    m w = (wGet tr w.val).testBit bit

theorem ParInv.congr_ge25 {bit allM : Nat} {fMask : Nat → Nat} {m1 : Fin 100 → Bool}
    {tr : WTree} {m m' : Fin 100 → Bool}
    (hI : ParInv bit allM fMask m1 tr m)
    (hhigh : ∀ w : Fin 100, 25 ≤ w.val → m' w = m w) :
    ParInv bit allM fMask m1 tr m' :=
  ⟨hI.wf, hI.hAll,
   fun w hw => (hhigh w (by rcases hw with ⟨h, _, _⟩ | h <;> omega)).trans (hI.hFree w hw),
   fun w hpw hfm => (hhigh w (isParWire_bounds hpw).1).trans (hI.hTracked w hpw hfm)⟩

theorem ParInv.eval_wire {bit allM : Nat} {fMask : Nat → Nat} {m1 : Fin 100 → Bool}
    {tr : WTree} {m : Fin 100 → Bool}
    (hI : ParInv bit allM fMask m1 tr m)
    {c : Nat} (hc : isParWire c = true)
    (hfm : (getFMask fMask c).testBit bit = false) :
    m ⟨c, (isParWire_bounds hc).2.1⟩ = (wGet tr c).testBit bit :=
  hI.hTracked ⟨c, (isParWire_bounds hc).2.1⟩ hc hfm

theorem ParInv.update_wire {bit allM : Nat} {fMask : Nat → Nat} {m1 : Fin 100 → Bool}
    {tr : WTree} {m : Fin 100 → Bool}
    (hI : ParInv bit allM fMask m1 tr m)
    {t v : Nat} (ht : isParWire t = true)
    (hfmt : (getFMask fMask t).testBit bit = false)
    (hb : Bool) (hvb : v.testBit bit = hb) :
    ParInv bit allM fMask m1 (wSet tr t v)
      (Function.update m ⟨t, (isParWire_bounds ht).2.1⟩ hb) := by
  obtain ⟨ht1, ht2, ht_ne49, _⟩ := isParWire_bounds ht
  refine ⟨wSet_wf hI.wf t v, hI.hAll, ?_, ?_⟩
  · intro w hw
    have hw_ne : w ≠ ⟨t, ht2⟩ := by
      intro e
      have hval : w.val = t := congrArg Fin.val e
      subst hval
      rcases hw with ⟨_, hlt49, hfm_true⟩ | h49
      · unfold getFMask at hfmt
        rw [ite_eq_left hlt49, hfm_true] at hfmt
        cases hfmt
      · exact ht_ne49 h49
    rw [Function.update_of_ne hw_ne]
    exact hI.hFree w hw
  · intro w hpw hfmw
    by_cases hwt : w = ⟨t, ht2⟩
    · subst hwt
      simp [Function.update_self, wGet_wSet hI.wf ht1 ht2 ht1 ht2, hvb]
    · have hne : w.val ≠ t := fun e => hwt (Fin.ext e)
      simp [Function.update_of_ne hwt,
            wGet_wSet hI.wf ht1 ht2 (isParWire_bounds hpw).1 w.isLt,
            hne, hI.hTracked w hpw hfmw]

theorem isParWire_of_anc {fMask : Nat → Nat} {t : Nat} (ht1 : 50 ≤ t) (ht2 : t < 100) :
    isParWire t = true ∧ getFMask fMask t = 0 := by
  constructor
  · unfold isParWire
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
    exact Or.inr ⟨ht1, ht2⟩
  · unfold getFMask
    exact ite_eq_right (by omega)

def evalQuadParOpt (fMask : Nat → Nat) (tr : WTree) (t : Nat) : List (Nat × Nat) → Option Nat
  | [] => some 0
  | (a, b) :: rest =>
      cond ((!Nat.beq a b) && (!Nat.beq a t) && (!Nat.beq b t) &&
            isParWire a && isParWire b &&
            Nat.beq (getFMask fMask a) 0 &&
            Nat.beq (wGet tr a &&& getFMask fMask b) 0)
        (match evalQuadParOpt fMask tr t rest with
         | some acc => someNat (fastLandXor (wGet tr a) (wGet tr b) acc)
         | none => none)
        none

def evalLinParOpt (fMask : Nat → Nat) (tr : WTree) (t : Nat) : List Nat → Option Nat
  | [] => some 0
  | c :: rest =>
      cond ((!Nat.beq c t) && isParWire c && Nat.beq (getFMask fMask c) 0)
        (match evalLinParOpt fMask tr t rest with
         | some acc => someNat (fastXor (wGet tr c) acc)
         | none => none)
        none

def stepParOpt (allM : Nat) (fMask : Nat → Nat) (tr : WTree) : Op102 → Option WTree
  | .x q =>
      cond (isParWire q && Nat.beq (getFMask fMask q) 0)
        (someWTree (wSet tr q (wGet tr q ^^^ allM))) none
  | .cx c t =>
      cond ((!Nat.beq c t) && isParWire c && isParWire t &&
            Nat.beq (getFMask fMask c) 0 &&
            Nat.beq (getFMask fMask t) 0)
        (let vc := wGet tr c
         cond (Nat.beq vc 0)
           (someWTree tr)
           (someWTree (wSet tr t (wGet tr t ^^^ vc)))) none
  | .and4t c1 c2 t =>
      let v1 := wGet tr c1
      let v2 := wGet tr c2
      let vt := wGet tr t
      cond ((!Nat.beq c1 c2) && (!Nat.beq c1 t) && (!Nat.beq c2 t) &&
            isParWire t && Nat.beq (getFMask fMask t) 0 &&
            isParWire c1 && isParWire c2 &&
            Nat.beq vt 0 &&
            Nat.beq (getFMask fMask c1) 0 &&
            Nat.beq (v1 &&& getFMask fMask c2) 0)
        (someWTree (wSet tr t (v1 &&& v2))) none
  | .rccx0 _ _ _ => none
  | .rccx1 _ _ _ => none
  | .unand c1 c2 t =>
      let v1 := wGet tr c1
      let v2 := wGet tr c2
      let vt := wGet tr t
      cond ((!Nat.beq c1 c2) && (!Nat.beq c1 t) && (!Nat.beq c2 t) &&
            isParWire t && Nat.beq (getFMask fMask t) 0 &&
            isParWire c1 && isParWire c2 &&
            Nat.beq (getFMask fMask c1) 0 &&
            Nat.beq (v1 &&& getFMask fMask c2) 0 &&
            Nat.beq vt (v1 &&& v2))
        (someWTree (wSet tr t 0)) none
  | .unquad qs ls t =>
      cond (Nat.ble 50 t && Nat.blt t 100)
        (match evalQuadParOpt fMask tr t qs, evalLinParOpt fMask tr t ls with
         | some vq, some vl =>
             cond (Nat.beq (wGet tr t) (vq ^^^ vl))
               (someWTree (wSet tr t 0)) none
         | _, _ => none)
        none
  | .z _ => none
  | .cz _ _ => none
  | .hGadget _ _ _ _ _ => none

theorem evalQuadParOpt_sound {bit allM : Nat} {fMask : Nat → Nat} {m1 m : Fin 100 → Bool}
    {tr : WTree} (hI : ParInv bit allM fMask m1 tr m) (t : Nat) :
    ∀ (qs : List (Nat × Nat)) {vq : Nat},
      evalQuadParOpt fMask tr t qs = some vq →
      (∀ p ∈ qs, p.1 < 100 ∧ p.2 < 100 ∧ p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧
      vq.testBit bit = evalQuadBool102 m qs
  | [], vq, h => by
    injection h with hvq; subst hvq
    exact ⟨fun _ hp => (by cases hp), Nat.zero_testBit bit⟩
  | (a, b) :: rest, vq, h => by
    dsimp only [evalQuadParOpt] at h
    cases hc : ((!Nat.beq a b) && (!Nat.beq a t) && (!Nat.beq b t) &&
                isParWire a && isParWire b &&
                Nat.beq (getFMask fMask a) 0 &&
                Nat.beq (wGet tr a &&& getFMask fMask b) 0)
    · rw [hc, Bool.cond_false] at h; cases h
    rw [hc, Bool.cond_true] at h
    cases hrest : evalQuadParOpt fMask tr t rest with
    | none => rw [hrest] at h; cases h
    | some acc =>
      rw [hrest] at h; dsimp only at h
      rw [someNat_eq, fastLandXor_eq] at h
      injection h with hvq; subst hvq
      obtain ⟨hrest_v, hrest_ev⟩ := evalQuadParOpt_sound hI t rest hrest
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_false_iff, Nat.beq_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨hab, hat⟩, hbt⟩, hpa⟩, hpb⟩, hfma⟩, hland⟩ := hc
      have ha_hi : a < 100 := (isParWire_bounds hpa).2.1
      have hb_hi : b < 100 := (isParWire_bounds hpb).2.1
      have hma : m ⟨a, ha_hi⟩ = (wGet tr a).testBit bit :=
        hI.eval_wire hpa (by rw [hfma, Nat.zero_testBit])
      have hprod : (wGet tr a &&& wGet tr b).testBit bit = (m ⟨a, ha_hi⟩ && m ⟨b, hb_hi⟩) := by
        rw [Nat.testBit_and, hma]
        cases hfmb : (getFMask fMask b).testBit bit
        · rw [hI.eval_wire hpb hfmb]
        · have h0 : ((wGet tr a).testBit bit && (getFMask fMask b).testBit bit) = false := by
            refine (Nat.testBit_and (wGet tr a) (getFMask fMask b) bit).symm.trans ?_
            exact (congrArg (fun x => x.testBit bit) hland).trans (Nat.zero_testBit bit)
          rw [hfmb, Bool.and_true] at h0
          rw [h0]; rfl
      refine ⟨fun p hp => ?_, ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hmem
        · exact ⟨ha_hi, hb_hi, hab, hat, hbt⟩
        · exact hrest_v p hmem
      · dsimp only [evalQuadBool102]
        rw [dite_eq_left ⟨ha_hi, hb_hi⟩, Nat.testBit_xor, hprod, hrest_ev]

theorem evalLinParOpt_sound {bit allM : Nat} {fMask : Nat → Nat} {m1 m : Fin 100 → Bool}
    {tr : WTree} (hI : ParInv bit allM fMask m1 tr m) (t : Nat) :
    ∀ (ls : List Nat) {vl : Nat},
      evalLinParOpt fMask tr t ls = some vl →
      (∀ c ∈ ls, c < 100 ∧ c ≠ t) ∧
      vl.testBit bit = evalLinBool102 m ls
  | [], vl, h => by
    injection h with hvl; subst hvl
    exact ⟨fun _ hc => (by cases hc), Nat.zero_testBit bit⟩
  | c :: rest, vl, h => by
    dsimp only [evalLinParOpt] at h
    cases hc : ((!Nat.beq c t) && isParWire c && Nat.beq (getFMask fMask c) 0)
    · rw [hc, Bool.cond_false] at h; cases h
    rw [hc, Bool.cond_true] at h
    cases hrest : evalLinParOpt fMask tr t rest with
    | none => rw [hrest] at h; cases h
    | some acc =>
      rw [hrest] at h; dsimp only at h
      rw [someNat_eq, fastXor_eq] at h
      injection h with hvl; subst hvl
      obtain ⟨hrest_v, hrest_ev⟩ := evalLinParOpt_sound hI t rest hrest
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_false_iff, Nat.beq_eq] at hc
      obtain ⟨⟨hct, hpc⟩, hfmc⟩ := hc
      have hc_hi : c < 100 := (isParWire_bounds hpc).2.1
      have hmc : m ⟨c, hc_hi⟩ = (wGet tr c).testBit bit :=
        hI.eval_wire hpc (by rw [hfmc, Nat.zero_testBit])
      refine ⟨fun x hx => ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hmem
        · exact ⟨hc_hi, hct⟩
        · exact hrest_v x hmem
      · dsimp only [evalLinBool102]
        rw [dite_eq_left hc_hi, Nat.testBit_xor, hmc, hrest_ev]

theorem stepParOpt_sound {bit allM : Nat} {fMask : Nat → Nat} {m1 : Fin 100 → Bool}
    {tr tr' : WTree} {m : Fin 100 → Bool}
    (hI : ParInv bit allM fMask m1 tr m)
    {op : Op102}
    (hok : stepParOpt allM fMask tr op = some tr') :
    ∃ m', execOp102 m op = some m' ∧
      (∀ w : Fin 100, w.val < 25 → m' w = m w) ∧
      ParInv bit allM fMask m1 tr' m' := by
  cases op with
  | x q =>
    dsimp only [stepParOpt] at hok
    cases hc : (isParWire q && Nat.beq (getFMask fMask q) 0)
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true, someWTree_eq] at hok
    injection hok with htr'; subst htr'
    simp only [Bool.and_eq_true, Nat.beq_eq] at hc
    obtain ⟨hpq, hfmq⟩ := hc
    obtain ⟨hq1, hq2, _, _⟩ := isParWire_bounds hpq
    have hfmq_bit : (getFMask fMask q).testBit bit = false := by rw [hfmq, Nat.zero_testBit]
    have hbit : (wGet tr q ^^^ allM).testBit bit = !m ⟨q, hq2⟩ := by
      rw [Nat.testBit_xor, ← hI.eval_wire hpq hfmq_bit, hI.hAll]
      cases m ⟨q, hq2⟩ <;> rfl
    refine ⟨_, by dsimp only [execOp102]; rw [dite_eq_left hq2], fun w hw => ?_,
      hI.update_wire hpq hfmq_bit _ hbit⟩
    exact Function.update_of_ne
      (fun e => by have := congrArg Fin.val e; dsimp only at this; omega) _ _
  | cx c t =>
    dsimp only [stepParOpt] at hok
    cases hc : ((!Nat.beq c t) && isParWire c && isParWire t &&
                Nat.beq (getFMask fMask c) 0 &&
                Nat.beq (getFMask fMask t) 0)
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_false_iff, Nat.beq_eq] at hc
    obtain ⟨⟨⟨⟨hct, hpc⟩, hpt⟩, hfmc⟩, hfmt⟩ := hc
    have hc2 : c < 100 := (isParWire_bounds hpc).2.1
    have ht1 : 25 ≤ t := (isParWire_bounds hpt).1
    have ht2 : t < 100 := (isParWire_bounds hpt).2.1
    have hfmc_bit : (getFMask fMask c).testBit bit = false := by rw [hfmc, Nat.zero_testBit]
    have hfmt_bit : (getFMask fMask t).testBit bit = false := by rw [hfmt, Nat.zero_testBit]
    have hmc : m ⟨c, hc2⟩ = (wGet tr c).testBit bit := hI.eval_wire hpc hfmc_bit
    have hmt : m ⟨t, ht2⟩ = (wGet tr t).testBit bit := hI.eval_wire hpt hfmt_bit
    cases hvc0 : Nat.beq (wGet tr c) 0
    · rw [hvc0, Bool.cond_false, someWTree_eq] at hok
      injection hok with htr'; subst htr'
      have hbit : (wGet tr t ^^^ wGet tr c).testBit bit = xor (m ⟨t, ht2⟩) (m ⟨c, hc2⟩) := by
        rw [Nat.testBit_xor, hmt, hmc]
      refine ⟨_, by dsimp only [execOp102]; rw [dite_eq_left ⟨hc2, ht2, hct⟩], fun w hw => ?_,
        hI.update_wire hpt hfmt_bit _ hbit⟩
      exact Function.update_of_ne
        (fun e => by have := congrArg Fin.val e; dsimp only at this; omega) _ _
    · rw [hvc0, Bool.cond_true, someWTree_eq] at hok
      injection hok with htr'; subst htr'
      have hmc0 : m ⟨c, hc2⟩ = false := by rw [hmc, Nat.beq_eq.mp hvc0, Nat.zero_testBit]
      have hup : Function.update m ⟨t, ht2⟩ (xor (m ⟨t, ht2⟩) (m ⟨c, hc2⟩)) = m := by
        rw [hmc0, Bool.xor_false, Function.update_eq_self]
      exact ⟨m, (by dsimp only [execOp102]; rw [dite_eq_left ⟨hc2, ht2, hct⟩, hup]),
        fun _ _ => rfl, hI⟩
  | and4t c1 c2 t =>
    dsimp only [stepParOpt] at hok
    cases hc : ((!Nat.beq c1 c2) && (!Nat.beq c1 t) && (!Nat.beq c2 t) &&
                isParWire t && Nat.beq (getFMask fMask t) 0 &&
                isParWire c1 && isParWire c2 &&
                Nat.beq (wGet tr t) 0 &&
                Nat.beq (getFMask fMask c1) 0 &&
                Nat.beq (wGet tr c1 &&& getFMask fMask c2) 0)
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true, someWTree_eq] at hok
    injection hok with htr'; subst htr'
    simp only [Bool.and_eq_true, Bool.not_eq_true',
      beq_false_iff, Nat.beq_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hc12, hc1t⟩, hc2t⟩, hpt⟩, hfmt0⟩, hpc1⟩, hpc2⟩, hvt0⟩, hfm1⟩, hland⟩ := hc
    have hc1_hi : c1 < 100 := (isParWire_bounds hpc1).2.1
    have hc2_hi : c2 < 100 := (isParWire_bounds hpc2).2.1
    have ht1 : 25 ≤ t := (isParWire_bounds hpt).1
    have ht2 : t < 100 := (isParWire_bounds hpt).2.1
    have hfmt_bit : (getFMask fMask t).testBit bit = false := by rw [hfmt0, Nat.zero_testBit]
    have hmt : m ⟨t, ht2⟩ = false := by
      rw [hI.eval_wire hpt hfmt_bit, hvt0, Nat.zero_testBit]
    have hmc1 : m ⟨c1, hc1_hi⟩ = (wGet tr c1).testBit bit :=
      hI.eval_wire hpc1 (by rw [hfm1, Nat.zero_testBit])
    have hprod : (wGet tr c1 &&& wGet tr c2).testBit bit =
        (m ⟨c1, hc1_hi⟩ && m ⟨c2, hc2_hi⟩) := by
      rw [Nat.testBit_and, hmc1]
      cases hfm2 : (getFMask fMask c2).testBit bit
      · rw [hI.eval_wire hpc2 hfm2]
      · have h0 : ((wGet tr c1).testBit bit && (getFMask fMask c2).testBit bit) = false := by
          refine (Nat.testBit_and (wGet tr c1) (getFMask fMask c2) bit).symm.trans ?_
          exact (congrArg (fun x => x.testBit bit) hland).trans (Nat.zero_testBit bit)
        rw [hfm2, Bool.and_true] at h0
        rw [h0]; rfl
    refine ⟨_, (by
        dsimp only [execOp102]
        rw [dite_eq_left ⟨hc1_hi, hc2_hi, ht2, hc12, hc1t, hc2t⟩, ite_eq_left hmt]),
      fun w hw => ?_,
      hI.update_wire hpt hfmt_bit _ hprod⟩
    exact Function.update_of_ne
      (fun e => by have := congrArg Fin.val e; dsimp only at this; omega) _ _
  | rccx0 _ _ _ => cases hok
  | rccx1 _ _ _ => cases hok
  | unand c1 c2 t =>
    dsimp only [stepParOpt] at hok
    cases hc : ((!Nat.beq c1 c2) && (!Nat.beq c1 t) && (!Nat.beq c2 t) &&
                isParWire t && Nat.beq (getFMask fMask t) 0 &&
                isParWire c1 && isParWire c2 &&
                Nat.beq (getFMask fMask c1) 0 &&
                Nat.beq (wGet tr c1 &&& getFMask fMask c2) 0 &&
                Nat.beq (wGet tr t) (wGet tr c1 &&& wGet tr c2))
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true, someWTree_eq] at hok
    injection hok with htr'; subst htr'
    simp only [Bool.and_eq_true, Bool.not_eq_true',
      beq_false_iff, Nat.beq_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hc12, hc1t⟩, hc2t⟩, hpt⟩, hfmt0⟩, hpc1⟩, hpc2⟩, hfm1⟩, hland⟩, hvt⟩ := hc
    have hc1_hi : c1 < 100 := (isParWire_bounds hpc1).2.1
    have hc2_hi : c2 < 100 := (isParWire_bounds hpc2).2.1
    have ht1 : 25 ≤ t := (isParWire_bounds hpt).1
    have ht2 : t < 100 := (isParWire_bounds hpt).2.1
    have hfmt_bit : (getFMask fMask t).testBit bit = false := by rw [hfmt0, Nat.zero_testBit]
    have hmc1 : m ⟨c1, hc1_hi⟩ = (wGet tr c1).testBit bit :=
      hI.eval_wire hpc1 (by rw [hfm1, Nat.zero_testBit])
    have hmt : m ⟨t, ht2⟩ = (m ⟨c1, hc1_hi⟩ && m ⟨c2, hc2_hi⟩) := by
      rw [hI.eval_wire hpt hfmt_bit, hvt, Nat.testBit_and, hmc1]
      cases hfm2 : (getFMask fMask c2).testBit bit
      · rw [hI.eval_wire hpc2 hfm2]
      · have h0 : ((wGet tr c1).testBit bit && (getFMask fMask c2).testBit bit) = false := by
          refine (Nat.testBit_and (wGet tr c1) (getFMask fMask c2) bit).symm.trans ?_
          exact (congrArg (fun x => x.testBit bit) hland).trans (Nat.zero_testBit bit)
        rw [hfm2, Bool.and_true] at h0
        rw [h0]; rfl
    refine ⟨_, (by
        dsimp only [execOp102]
        rw [dite_eq_left ⟨hc1_hi, hc2_hi, ht2, hc12, hc1t, hc2t⟩, ite_eq_left hmt]),
      fun w hw => ?_,
      hI.update_wire hpt hfmt_bit false (Nat.zero_testBit bit)⟩
    exact Function.update_of_ne
      (fun e => by have := congrArg Fin.val e; dsimp only at this; omega) _ _
  | unquad qs ls t =>
    dsimp only [stepParOpt] at hok
    cases htb : (Nat.ble 50 t && Nat.blt t 100)
    · rw [htb, Bool.cond_false] at hok; cases hok
    rw [htb, Bool.cond_true] at hok
    cases hq : evalQuadParOpt fMask tr t qs with
    | none => rw [hq] at hok; cases hok
    | some vq =>
      rw [hq] at hok
      cases hl : evalLinParOpt fMask tr t ls with
      | none => rw [hl] at hok; cases hok
      | some vl =>
        rw [hl] at hok; dsimp only at hok
        cases heq : Nat.beq (wGet tr t) (vq ^^^ vl)
        · rw [heq, Bool.cond_false] at hok; cases hok
        rw [heq, Bool.cond_true, someWTree_eq] at hok
        injection hok with htr'; subst htr'
        simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at htb
        obtain ⟨ht1, ht2⟩ := htb
        have hvt : wGet tr t = vq ^^^ vl := Nat.beq_eq.mp heq
        obtain ⟨hq_v, hq_ev⟩ := evalQuadParOpt_sound hI t qs hq
        obtain ⟨hl_v, hl_ev⟩ := evalLinParOpt_sound hI t ls hl
        obtain ⟨hpt, hfmt0⟩ := isParWire_of_anc (fMask := fMask) ht1 ht2
        have hfmt_bit : (getFMask fMask t).testBit bit = false := by rw [hfmt0, Nat.zero_testBit]
        have hval : validUnquad102 qs ls t := ⟨hq_v, hl_v, ht2⟩
        have hmt : m ⟨t, ht2⟩ = evalUnquad102 m qs ls := by
          rw [hI.eval_wire hpt hfmt_bit, hvt, Nat.testBit_xor, hq_ev, hl_ev]; rfl
        refine ⟨_, (by dsimp only [execOp102]; rw [dite_eq_left hval, ite_eq_left hmt]),
          fun w hw => ?_,
          hI.update_wire hpt hfmt_bit false (Nat.zero_testBit bit)⟩
        exact Function.update_of_ne
          (fun e => by have := congrArg Fin.val e; dsimp only at this; omega) _ _
  | z _ => cases hok
  | cz _ => cases hok
  | hGadget _ _ _ _ _ => cases hok

def runParListOpt (allM : Nat) (fMask : Nat → Nat) : List Op102 → WTree → Option WTree
  | [], tr => some tr
  | op :: ops, tr =>
      match stepParOpt allM fMask tr op with
      | some tr1 => runParListOpt allM fMask ops tr1
      | none => none

theorem runParListOpt_sound {bit allM : Nat} {fMask : Nat → Nat} {m1 : Fin 100 → Bool} :
    ∀ (ops : List Op102) {tr tr' : WTree} {m : Fin 100 → Bool},
      ParInv bit allM fMask m1 tr m →
      runParListOpt allM fMask ops tr = some tr' →
      ∃ m', execList102 ops m = some m' ∧
        (∀ w : Fin 100, w.val < 25 → m' w = m w) ∧
        ParInv bit allM fMask m1 tr' m'
  | [], _, _, m, hI, hok => by
    injection hok with htr'; subst htr'
    exact ⟨m, rfl, fun _ _ => rfl, hI⟩
  | op :: ops, tr, tr', m, hI, hok => by
    dsimp only [runParListOpt] at hok
    cases hs : stepParOpt allM fMask tr op with
    | none => rw [hs] at hok; cases hok
    | some tr1 =>
      rw [hs] at hok
      obtain ⟨m_a, hex1, hlo1, hI1⟩ := stepParOpt_sound hI hs
      obtain ⟨m', hex2, hlo2, hI2⟩ := runParListOpt_sound ops hI1 hok
      refine ⟨m', by simp [execList102, hex1, hex2], fun w hw => (hlo2 w hw).trans (hlo1 w hw), hI2⟩

def runParSeqOpt (allM : Nat) (fMask : Nat → Nat) : List (List Op102) → WTree → Option WTree
  | [], tr => some tr
  | l :: seqs, tr =>
      match runParListOpt allM fMask l tr with
      | some tr1 => runParSeqOpt allM fMask seqs tr1
      | none => none

def runParSeq (allM : Nat) (fMask : Nat → Nat) (seqs : List (List Op102))
    (tr : WTree) (k : WTree → Bool) : Bool :=
  match runParSeqOpt allM fMask seqs tr with
  | some tr' => k tr'
  | none => false

theorem runParSeq_sound {bit allM : Nat} {fMask : Nat → Nat} {m1 : Fin 100 → Bool} :
    ∀ (seqs : List (List Op102)) {tr : WTree} {m : Fin 100 → Bool},
      ParInv bit allM fMask m1 tr m →
      ∀ {k : WTree → Bool}, runParSeq allM fMask seqs tr k = true →
      ∃ tr' m', execList102 seqs.flatten m = some m' ∧
        (∀ w : Fin 100, w.val < 25 → m' w = m w) ∧
        ParInv bit allM fMask m1 tr' m' ∧ k tr' = true
  | [], tr, m, hI, k, hok => ⟨tr, m, rfl, fun _ _ => rfl, hI, hok⟩
  | l :: seqs, tr, m, hI, k, hok => by
    dsimp only [runParSeq, runParSeqOpt] at hok
    cases hs : runParListOpt allM fMask l tr with
    | none => rw [hs] at hok; cases hok
    | some tr1 =>
      rw [hs] at hok
      have hok1 : runParSeq allM fMask seqs tr1 k = true := hok
      obtain ⟨m_a, hex1, hlo1, hI1⟩ := runParListOpt_sound l hI hs
      obtain ⟨tr2, m', hex2, hlo2, hI2, hok2⟩ := runParSeq_sound seqs hI1 hok1
      refine ⟨tr2, m', ?_, fun w hw => (hlo2 w hw).trans (hlo1 w hw), hI2, hok2⟩
      rw [List.flatten_cons, execList102_append, hex1, Option.bind_some, hex2]

def add1Par (p0 p1 p2 dt : Nat) : Nat × Nat × Nat :=
  let c0 := p0 &&& dt
  let p0' := fastXor p0 dt
  let c1 := p1 &&& c0
  (p0', fastXor p1 c0, fastXor p2 c1)

def add7Par (p0 p1 p2 dt : Nat) : Nat × Nat × Nat :=
  let c0 := p0 &&& dt
  let p0' := fastXor p0 dt
  let c1 := p1 &&& c0
  let p1_a := fastXor p1 c0
  let p2_a := fastXor p2 c1
  let c1_b := p1_a &&& dt
  (p0', fastXor p1_a dt, fastXor (fastXor p2_a c1_b) dt)

theorem add1Par_testBit (p0 p1 p2 dt bit : Nat) :
    let r := add1Par p0 p1 p2 dt
    let rb := add1Bools (p0.testBit bit) (p1.testBit bit) (p2.testBit bit) (dt.testBit bit)
    r.1.testBit bit = rb.1 ∧ r.2.1.testBit bit = rb.2.1 ∧ r.2.2.testBit bit = rb.2.2 := by
  dsimp only [add1Par, add1Bools]
  simp only [fastXor_eq, Nat.testBit_xor, Nat.testBit_and, and_self]

theorem add7Par_testBit (p0 p1 p2 dt bit : Nat) :
    let r := add7Par p0 p1 p2 dt
    let rb := add7Bools (p0.testBit bit) (p1.testBit bit) (p2.testBit bit) (dt.testBit bit)
    r.1.testBit bit = rb.1 ∧ r.2.1.testBit bit = rb.2.1 ∧ r.2.2.testBit bit = rb.2.2 := by
  dsimp only [add7Par, add7Bools]
  simp only [fastXor_eq, Nat.testBit_xor, Nat.testBit_and, and_self]

def evalHPosPar (allM : Nat) (fMask : Nat → Nat) (tr : WTree) (t : Nat) :
    List (Bool × List Nat) → (Nat × Nat × Nat × Nat) → Option (Nat × Nat × Nat × Nat)
  | [], st => some st
  | (xc, ls) :: rest, (dt, p0, p1, p2) =>
      match evalLinParOpt fMask tr t ls with
      | some vl =>
          let v_step := cond xc (fastXor allM vl) vl
          let dt' := fastXor dt v_step
          let p := add1Par p0 p1 p2 dt'
          evalHPosPar allM fMask tr t rest (dt', p.1, p.2.1, p.2.2)
      | none => none

def evalHNegPar (allM : Nat) (fMask : Nat → Nat) (tr : WTree) (t : Nat) :
    List (Bool × List Nat) → (Nat × Nat × Nat × Nat) → Option (Nat × Nat × Nat × Nat)
  | [], st => some st
  | (xc, ls) :: rest, (dt, p0, p1, p2) =>
      match evalLinParOpt fMask tr t ls with
      | some vl =>
          let v_step := cond xc (fastXor allM vl) vl
          let dt' := fastXor dt v_step
          let p := add7Par p0 p1 p2 dt'
          evalHNegPar allM fMask tr t rest (dt', p.1, p.2.1, p.2.2)
      | none => none

def evalHGadgetPar (allM : Nat) (fMask : Nat → Nat) (tr : WTree) (t : Nat)
    (posSteps negSteps : List (Bool × List Nat)) : Option (Nat × Nat) :=
  match evalHPosPar allM fMask tr t posSteps (0, 0, 0, 0) with
  | some st1 =>
      match evalHNegPar allM fMask tr t negSteps st1 with
      | some st2 => some (st2.2.2.1, st2.2.2.2)
      | none => none
  | none => none

theorem cond_fastXor_allM_testBit {bit allM vl : Nat} (hAll : allM.testBit bit = true) (xc : Bool) :
    (cond xc (fastXor allM vl) vl).testBit bit = xor xc (vl.testBit bit) := by
  cases xc
  · simp [cond]
  · simp [cond, fastXor_eq, Nat.testBit_xor, hAll]

theorem evalHPosPar_sound {bit allM : Nat} {fMask : Nat → Nat} {m1 m : Fin 100 → Bool}
    {tr : WTree} (hI : ParInv bit allM fMask m1 tr m) (t : Nat) :
    ∀ (steps : List (Bool × List Nat)) (stP : Nat × Nat × Nat × Nat)
      (stB : Bool × Bool × Bool × Bool) {stP' : Nat × Nat × Nat × Nat},
      stP.1.testBit bit = stB.1 →
      stP.2.1.testBit bit = stB.2.1 →
      stP.2.2.1.testBit bit = stB.2.2.1 →
      stP.2.2.2.testBit bit = stB.2.2.2 →
      evalHPosPar allM fMask tr t steps stP = some stP' →
      let stB' := evalHPosBool m steps stB
      stP'.1.testBit bit = stB'.1 ∧
      stP'.2.1.testBit bit = stB'.2.1 ∧
      stP'.2.2.1.testBit bit = stB'.2.2.1 ∧
      stP'.2.2.2.testBit bit = stB'.2.2.2
  | [], stP, stB, stP', h0, h1, h2, h3, hok => by
    injection hok with h; subst h
    exact ⟨h0, h1, h2, h3⟩
  | (xc, ls) :: rest, (dt, p0, p1, p2), (dtb, b0, b1, b2), stP', h0, h1, h2, h3, hok => by
    dsimp only [evalHPosPar] at hok
    cases hl : evalLinParOpt fMask tr t ls with
    | none => rw [hl] at hok; cases hok
    | some vl =>
      rw [hl] at hok; dsimp only at hok
      obtain ⟨_, hl_ev⟩ := evalLinParOpt_sound hI t ls hl
      have hdt' : (fastXor dt (cond xc (fastXor allM vl) vl)).testBit bit =
          xor dtb (xor xc (evalLinBool102 m ls)) := by
        rw [fastXor_eq, Nat.testBit_xor, h0, cond_fastXor_allM_testBit hI.hAll xc, hl_ev]
      have hp := add1Par_testBit p0 p1 p2 (fastXor dt (cond xc (fastXor allM vl) vl)) bit
      dsimp only at hp
      rw [h1, h2, h3, hdt'] at hp
      exact evalHPosPar_sound hI t rest _ _ hdt' hp.1 hp.2.1 hp.2.2 hok

theorem evalHNegPar_sound {bit allM : Nat} {fMask : Nat → Nat} {m1 m : Fin 100 → Bool}
    {tr : WTree} (hI : ParInv bit allM fMask m1 tr m) (t : Nat) :
    ∀ (steps : List (Bool × List Nat)) (stP : Nat × Nat × Nat × Nat)
      (stB : Bool × Bool × Bool × Bool) {stP' : Nat × Nat × Nat × Nat},
      stP.1.testBit bit = stB.1 →
      stP.2.1.testBit bit = stB.2.1 →
      stP.2.2.1.testBit bit = stB.2.2.1 →
      stP.2.2.2.testBit bit = stB.2.2.2 →
      evalHNegPar allM fMask tr t steps stP = some stP' →
      let stB' := evalHNegBool m steps stB
      stP'.1.testBit bit = stB'.1 ∧
      stP'.2.1.testBit bit = stB'.2.1 ∧
      stP'.2.2.1.testBit bit = stB'.2.2.1 ∧
      stP'.2.2.2.testBit bit = stB'.2.2.2
  | [], stP, stB, stP', h0, h1, h2, h3, hok => by
    injection hok with h; subst h
    exact ⟨h0, h1, h2, h3⟩
  | (xc, ls) :: rest, (dt, p0, p1, p2), (dtb, b0, b1, b2), stP', h0, h1, h2, h3, hok => by
    dsimp only [evalHNegPar] at hok
    cases hl : evalLinParOpt fMask tr t ls with
    | none => rw [hl] at hok; cases hok
    | some vl =>
      rw [hl] at hok; dsimp only at hok
      obtain ⟨_, hl_ev⟩ := evalLinParOpt_sound hI t ls hl
      have hdt' : (fastXor dt (cond xc (fastXor allM vl) vl)).testBit bit =
          xor dtb (xor xc (evalLinBool102 m ls)) := by
        rw [fastXor_eq, Nat.testBit_xor, h0, cond_fastXor_allM_testBit hI.hAll xc, hl_ev]
      have hp := add7Par_testBit p0 p1 p2 (fastXor dt (cond xc (fastXor allM vl) vl)) bit
      dsimp only at hp
      rw [h1, h2, h3, hdt'] at hp
      exact evalHNegPar_sound hI t rest _ _ hdt' hp.1 hp.2.1 hp.2.2 hok

theorem evalHGadgetPar_sound {bit allM : Nat} {fMask : Nat → Nat} {m1 m : Fin 100 → Bool}
    {tr : WTree} (hI : ParInv bit allM fMask m1 tr m) (t : Nat)
    {pos neg : List (Bool × List Nat)} (uc : Bool) (ul : List Nat) {v1 v2 : Nat}
    (hok : evalHGadgetPar allM fMask tr t pos neg = some (v1, v2)) :
    let res := evalHGadgetBool m pos neg uc ul
    v1.testBit bit = res.2.2.1 ∧ v2.testBit bit = res.2.2.2 := by
  unfold evalHGadgetPar at hok
  cases hp : evalHPosPar allM fMask tr t pos (0, 0, 0, 0) with
  | none => rw [hp] at hok; cases hok
  | some st1 =>
    rw [hp] at hok; dsimp only at hok
    cases hn : evalHNegPar allM fMask tr t neg st1 with
    | none => rw [hn] at hok; cases hok
    | some st2 =>
      rw [hn] at hok; dsimp only at hok
      injection hok with hpair
      injection hpair with hv1 hv2; subst hv1 hv2
      have h1 := evalHPosPar_sound hI t pos (0, 0, 0, 0) (false, false, false, false)
        (Nat.zero_testBit bit) (Nat.zero_testBit bit)
        (Nat.zero_testBit bit) (Nat.zero_testBit bit) hp
      have h2 := evalHNegPar_sound hI t neg st1 (evalHPosBool m pos (false, false, false, false))
        h1.1 h1.2.1 h1.2.2.1 h1.2.2.2 hn
      exact ⟨h2.2.2.1, h2.2.2.2⟩

def stepParPhaseOpt (allM : Nat) (fMask : Nat → Nat) (tr : WTree) (pMask : Nat) :
    Op102 → Option (WTree × Nat)
  | .z q =>
      cond (isParWire q && Nat.beq (getFMask fMask q) 0)
        (some (tr, fastXor pMask (wGet tr q))) none
  | .cz c1 c2 =>
      cond ((!Nat.beq c1 c2) && isParWire c1 && isParWire c2 &&
            Nat.beq (getFMask fMask c1) 0 &&
            Nat.beq (wGet tr c1 &&& getFMask fMask c2) 0)
        (some (tr, fastLandXor (wGet tr c1) (wGet tr c2) pMask)) none
  | .hGadget t pos neg uc ul =>
      cond (Nat.ble 50 t && Nat.blt t 100 && Nat.beq (wGet tr t) 0 &&
            checkHGadgetStatic t pos neg uc ul)
        (match evalHGadgetPar allM fMask tr t pos neg with
         | some (v1, v2) => some (wSet tr t v1, fastXor pMask v2)
         | none => none)
        none
  | op =>
      cond op.noPhase
        (match stepParOpt allM fMask tr op with
         | some tr' => some (tr', pMask)
         | none => none)
        none

theorem stepParPhaseOpt_sound {bit allM : Nat} {fMask : Nat → Nat} {m1 : Fin 100 → Bool}
    {tr tr' : WTree} {pMask pMask' : Nat} {m : Fin 100 → Bool}
    (hI : ParInv bit allM fMask m1 tr m)
    {op : Op102}
    (hok : stepParPhaseOpt allM fMask tr pMask op = some (tr', pMask')) :
    ∃ m', execOp102 m op = some m' ∧
      pMask'.testBit bit = xor (pMask.testBit bit) (phaseOp102 m op) ∧
      (∀ w : Fin 100, w.val < 25 → m' w = m w) ∧
      ParInv bit allM fMask m1 tr' m' := by
  cases op with
  | z q =>
    dsimp only [stepParPhaseOpt] at hok
    cases hc : (isParWire q && Nat.beq (getFMask fMask q) 0)
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    injection hok with hpair
    injection hpair with htr' hp'; subst htr' hp'
    simp only [Bool.and_eq_true, Nat.beq_eq] at hc
    obtain ⟨hpq, hfmq⟩ := hc
    obtain ⟨_, hq2, _, _⟩ := isParWire_bounds hpq
    have hfmq_bit : (getFMask fMask q).testBit bit = false := by rw [hfmq, Nat.zero_testBit]
    have hmq : m ⟨q, hq2⟩ = (wGet tr q).testBit bit := hI.eval_wire hpq hfmq_bit
    refine ⟨m, by dsimp only [execOp102]; rw [ite_eq_left hq2], ?_, fun _ _ => rfl, hI⟩
    dsimp only [phaseOp102]
    rw [dite_eq_left hq2, fastXor_eq, Nat.testBit_xor, hmq]
  | cz c1 c2 =>
    dsimp only [stepParPhaseOpt] at hok
    cases hc : ((!Nat.beq c1 c2) && isParWire c1 && isParWire c2 &&
                Nat.beq (getFMask fMask c1) 0 &&
                Nat.beq (wGet tr c1 &&& getFMask fMask c2) 0)
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    injection hok with hpair
    injection hpair with htr' hp'; subst htr' hp'
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_false_iff, Nat.beq_eq] at hc
    obtain ⟨⟨⟨⟨hc12, hpc1⟩, hpc2⟩, hfm1⟩, hland⟩ := hc
    have hc1_hi : c1 < 100 := (isParWire_bounds hpc1).2.1
    have hc2_hi : c2 < 100 := (isParWire_bounds hpc2).2.1
    have hmc1 : m ⟨c1, hc1_hi⟩ = (wGet tr c1).testBit bit :=
      hI.eval_wire hpc1 (by rw [hfm1, Nat.zero_testBit])
    have hprod : (wGet tr c1 &&& wGet tr c2).testBit bit =
        (m ⟨c1, hc1_hi⟩ && m ⟨c2, hc2_hi⟩) := by
      rw [Nat.testBit_and, hmc1]
      cases hfm2 : (getFMask fMask c2).testBit bit
      · rw [hI.eval_wire hpc2 hfm2]
      · have h0 : ((wGet tr c1).testBit bit && (getFMask fMask c2).testBit bit) = false := by
          refine (Nat.testBit_and (wGet tr c1) (getFMask fMask c2) bit).symm.trans ?_
          exact (congrArg (fun x => x.testBit bit) hland).trans (Nat.zero_testBit bit)
        rw [hfm2, Bool.and_true] at h0
        rw [h0]; rfl
    refine ⟨m, (by dsimp only [execOp102]; rw [ite_eq_left ⟨hc1_hi, hc2_hi, hc12⟩]),
      ?_, fun _ _ => rfl, hI⟩
    dsimp only [phaseOp102]
    rw [dite_eq_left ⟨hc1_hi, hc2_hi⟩, fastLandXor_eq, Nat.testBit_xor, hprod, Bool.xor_comm]
  | hGadget t pos neg uc ul =>
    dsimp only [stepParPhaseOpt] at hok
    cases hc : (Nat.ble 50 t && Nat.blt t 100 && Nat.beq (wGet tr t) 0 &&
                checkHGadgetStatic t pos neg uc ul)
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    cases hg : evalHGadgetPar allM fMask tr t pos neg with
    | none => rw [hg] at hok; cases hok
    | some vp =>
      rcases vp with ⟨v1, v2⟩
      rw [hg] at hok; dsimp only at hok
      injection hok with hpair
      injection hpair with htr' hp'; subst htr' hp'
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at hc
      obtain ⟨⟨⟨ht1, ht2⟩, hvt0⟩, hstat⟩ := hc
      obtain ⟨hpt, hfmt0⟩ := isParWire_of_anc (fMask := fMask) ht1 ht2
      have hfmt_bit : (getFMask fMask t).testBit bit = false := by rw [hfmt0, Nat.zero_testBit]
      have hmt0 : m ⟨t, ht2⟩ = false := by
        rw [hI.eval_wire hpt hfmt_bit, hvt0, Nat.zero_testBit]
      obtain ⟨hv1, hv2⟩ := evalHGadgetPar_sound hI t uc ul hg
      refine ⟨_, by dsimp only [execOp102]; rw [dite_eq_left hstat, ite_eq_left hmt0],
        by dsimp only [phaseOp102]; rw [fastXor_eq, Nat.testBit_xor, hv2],
        fun w hw => ?_,
        hI.update_wire hpt hfmt_bit _ hv1⟩
      exact Function.update_of_ne
        (fun e => by have := congrArg Fin.val e; dsimp only at this; omega) _ _
  | x q =>
    dsimp only [stepParPhaseOpt, Op102.noPhase, Bool.cond_true] at hok
    cases hs : stepParOpt allM fMask tr (.x q) with
    | none => rw [hs] at hok; cases hok
    | some tr1 =>
      rw [hs] at hok; injection hok with hpair; injection hpair with htr' hp'; subst htr' hp'
      obtain ⟨m', hex, hlo, hI'⟩ := stepParOpt_sound hI hs
      exact ⟨m', hex, by simp [phaseOp102], hlo, hI'⟩
  | cx c t =>
    dsimp only [stepParPhaseOpt, Op102.noPhase, Bool.cond_true] at hok
    cases hs : stepParOpt allM fMask tr (.cx c t) with
    | none => rw [hs] at hok; cases hok
    | some tr1 =>
      rw [hs] at hok; injection hok with hpair; injection hpair with htr' hp'; subst htr' hp'
      obtain ⟨m', hex, hlo, hI'⟩ := stepParOpt_sound hI hs
      exact ⟨m', hex, by simp [phaseOp102], hlo, hI'⟩
  | and4t c1 c2 t =>
    dsimp only [stepParPhaseOpt, Op102.noPhase, Bool.cond_true] at hok
    cases hs : stepParOpt allM fMask tr (.and4t c1 c2 t) with
    | none => rw [hs] at hok; cases hok
    | some tr1 =>
      rw [hs] at hok; injection hok with hpair; injection hpair with htr' hp'; subst htr' hp'
      obtain ⟨m', hex, hlo, hI'⟩ := stepParOpt_sound hI hs
      exact ⟨m', hex, by simp [phaseOp102], hlo, hI'⟩
  | rccx0 c1 c2 t =>
    dsimp only [stepParPhaseOpt, Op102.noPhase, Bool.cond_true] at hok
    cases hs : stepParOpt allM fMask tr (.rccx0 c1 c2 t) with
    | none => rw [hs] at hok; cases hok
    | some tr1 =>
      rw [hs] at hok; injection hok with hpair; injection hpair with htr' hp'; subst htr' hp'
      obtain ⟨m', hex, hlo, hI'⟩ := stepParOpt_sound hI hs
      exact ⟨m', hex, by simp [phaseOp102], hlo, hI'⟩
  | rccx1 c1 c2 t =>
    dsimp only [stepParPhaseOpt, Op102.noPhase, Bool.cond_true] at hok
    cases hs : stepParOpt allM fMask tr (.rccx1 c1 c2 t) with
    | none => rw [hs] at hok; cases hok
    | some tr1 =>
      rw [hs] at hok; injection hok with hpair; injection hpair with htr' hp'; subst htr' hp'
      obtain ⟨m', hex, hlo, hI'⟩ := stepParOpt_sound hI hs
      exact ⟨m', hex, by simp [phaseOp102], hlo, hI'⟩
  | unand c1 c2 t =>
    dsimp only [stepParPhaseOpt, Op102.noPhase, Bool.cond_true] at hok
    cases hs : stepParOpt allM fMask tr (.unand c1 c2 t) with
    | none => rw [hs] at hok; cases hok
    | some tr1 =>
      rw [hs] at hok; injection hok with hpair; injection hpair with htr' hp'; subst htr' hp'
      obtain ⟨m', hex, hlo, hI'⟩ := stepParOpt_sound hI hs
      exact ⟨m', hex, by simp [phaseOp102], hlo, hI'⟩
  | unquad qs ls t =>
    dsimp only [stepParPhaseOpt, Op102.noPhase, Bool.cond_true] at hok
    cases hs : stepParOpt allM fMask tr (.unquad qs ls t) with
    | none => rw [hs] at hok; cases hok
    | some tr1 =>
      rw [hs] at hok; injection hok with hpair; injection hpair with htr' hp'; subst htr' hp'
      obtain ⟨m', hex, hlo, hI'⟩ := stepParOpt_sound hI hs
      exact ⟨m', hex, by simp [phaseOp102], hlo, hI'⟩

def runParPhaseListOpt (allM : Nat) (fMask : Nat → Nat) :
    List Op102 → (WTree × Nat) → Option (WTree × Nat)
  | [], st => some st
  | op :: ops, (tr, pMask) =>
      match stepParPhaseOpt allM fMask tr pMask op with
      | some st1 => runParPhaseListOpt allM fMask ops st1
      | none => none

theorem runParPhaseListOpt_sound {bit allM : Nat} {fMask : Nat → Nat} {m1 : Fin 100 → Bool} :
    ∀ (ops : List Op102) {tr tr' : WTree} {pMask pMask' : Nat} {m : Fin 100 → Bool},
      ParInv bit allM fMask m1 tr m →
      runParPhaseListOpt allM fMask ops (tr, pMask) = some (tr', pMask') →
      ∃ m', execList102 ops m = some m' ∧
        pMask'.testBit bit = xor (pMask.testBit bit) (phaseList102 ops m) ∧
        (∀ w : Fin 100, w.val < 25 → m' w = m w) ∧
        ParInv bit allM fMask m1 tr' m'
  | [], _, _, pMask, _, m, hI, hok => by
    injection hok with hpair
    injection hpair with htr' hp'; subst htr' hp'
    exact ⟨m, rfl, by simp [phaseList102], fun _ _ => rfl, hI⟩
  | op :: ops, tr, tr', pMask, pMask', m, hI, hok => by
    dsimp only [runParPhaseListOpt] at hok
    cases hs : stepParPhaseOpt allM fMask tr pMask op with
    | none => rw [hs] at hok; cases hok
    | some st1 =>
      rcases st1 with ⟨tr1, pMask1⟩
      rw [hs] at hok
      obtain ⟨m_a, hex1, hph1, hlo1, hI1⟩ := stepParPhaseOpt_sound hI hs
      obtain ⟨m', hex2, hph2, hlo2, hI2⟩ := runParPhaseListOpt_sound ops hI1 hok
      refine ⟨m', by simp [execList102, hex1, hex2], ?_,
        fun w hw => (hlo2 w hw).trans (hlo1 w hw), hI2⟩
      dsimp only [phaseList102]
      rw [hex1, hph2, hph1, Bool.xor_assoc]

def runParPhaseSeqOpt (allM : Nat) (fMask : Nat → Nat) :
    List (List Op102) → (WTree × Nat) → Option (WTree × Nat)
  | [], st => some st
  | l :: seqs, st =>
      match runParPhaseListOpt allM fMask l st with
      | some st1 => runParPhaseSeqOpt allM fMask seqs st1
      | none => none

theorem runParPhaseSeqOpt_sound {bit allM : Nat} {fMask : Nat → Nat} {m1 : Fin 100 → Bool} :
    ∀ (seqs : List (List Op102)) {tr tr' : WTree} {pMask pMask' : Nat} {m : Fin 100 → Bool},
      ParInv bit allM fMask m1 tr m →
      runParPhaseSeqOpt allM fMask seqs (tr, pMask) = some (tr', pMask') →
      ∃ m', execList102 seqs.flatten m = some m' ∧
        pMask'.testBit bit = xor (pMask.testBit bit) (phaseList102 seqs.flatten m) ∧
        (∀ w : Fin 100, w.val < 25 → m' w = m w) ∧
        ParInv bit allM fMask m1 tr' m'
  | [], _, _, pMask, _, m, hI, hok => by
    injection hok with hpair
    injection hpair with htr' hp'; subst htr' hp'
    exact ⟨m, rfl, by simp [phaseList102], fun _ _ => rfl, hI⟩
  | l :: seqs, tr, tr', pMask, pMask', m, hI, hok => by
    dsimp only [runParPhaseSeqOpt] at hok
    cases hs : runParPhaseListOpt allM fMask l (tr, pMask) with
    | none => rw [hs] at hok; cases hok
    | some st1 =>
      rcases st1 with ⟨tr1, pMask1⟩
      rw [hs] at hok
      obtain ⟨m_a, hex1, hph1, hlo1, hI1⟩ := runParPhaseListOpt_sound l hI hs
      obtain ⟨m', hex2, hph2, hlo2, hI2⟩ := runParPhaseSeqOpt_sound seqs hI1 hok
      refine ⟨m', ?_, ?_, fun w hw => (hlo2 w hw).trans (hlo1 w hw), hI2⟩
      · rw [List.flatten_cons, execList102_append, hex1, Option.bind_some, hex2]
      · rw [List.flatten_cons, phaseList102_append l seqs.flatten hex1, hph2, hph1, Bool.xor_assoc]

def runParPhaseSeq (allM : Nat) (fMask : Nat → Nat) (seqs : List (List Op102))
    (tr : WTree) (k : WTree → Bool) : Bool :=
  match runParPhaseSeqOpt allM fMask seqs (tr, 0) with
  | some (tr', pMask') => Nat.beq pMask' 0 && k tr'
  | none => false

theorem runParPhaseSeq_sound {bit allM : Nat} {fMask : Nat → Nat} {m1 : Fin 100 → Bool}
    (seqs : List (List Op102)) {tr : WTree} {m : Fin 100 → Bool}
    (hI : ParInv bit allM fMask m1 tr m)
    {k : WTree → Bool} (hok : runParPhaseSeq allM fMask seqs tr k = true) :
    ∃ tr' m', execList102 seqs.flatten m = some m' ∧
      phaseList102 seqs.flatten m = false ∧
      (∀ w : Fin 100, w.val < 25 → m' w = m w) ∧
      ParInv bit allM fMask m1 tr' m' ∧ k tr' = true := by
  unfold runParPhaseSeq at hok
  cases hs : runParPhaseSeqOpt allM fMask seqs (tr, 0) with
  | none => rw [hs] at hok; cases hok
  | some stf =>
    rcases stf with ⟨tr', pMask'⟩
    rw [hs] at hok; dsimp only at hok
    simp only [Bool.and_eq_true, Nat.beq_eq] at hok
    obtain ⟨m', hex, hph, hlo, hI'⟩ := runParPhaseSeqOpt_sound seqs hI hs
    rw [hok.1, Nat.zero_testBit, Bool.false_xor] at hph
    exact ⟨tr', m', hex, hph.symm, hlo, hI', hok.2⟩

def checkEqList (tr : WTree) : List Nat → List Nat → Bool
  | [], [] => true
  | w :: ws, v :: vs => cond (Nat.beq (wGet tr w) v) (checkEqList tr ws vs) false
  | _, _ => false

theorem checkEqList_sound {tr : WTree} :
    ∀ (ws vs : List Nat), checkEqList tr ws vs = true →
      ∀ (i w v : Nat), ws[i]? = some w → vs[i]? = some v → wGet tr w = v
  | [], _, _, _, _, _, hw, _ => by cases hw
  | _ :: _, [], hok, _, _, _, _, _ => by cases hok
  | w :: ws, v :: vs, hok, i, w', v', hw, hv => by
    dsimp only [checkEqList] at hok
    cases hc : Nat.beq (wGet tr w) v
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    cases i with
    | zero =>
      injection hw with hw'; injection hv with hv'
      subst hw' hv'
      exact Nat.beq_eq.mp hc
    | succ i =>
      exact checkEqList_sound ws vs hok i w' v' hw hv

def checkZeroList (tr : WTree) : List Nat → Bool
  | [] => true
  | w :: ws => cond (Nat.beq (wGet tr w) 0) (checkZeroList tr ws) false

theorem checkZeroList_sound {tr : WTree} :
    ∀ (ws : List Nat), checkZeroList tr ws = true → ∀ w ∈ ws, wGet tr w = 0
  | [], _, _, hw => absurd hw List.not_mem_nil
  | w :: ws, hok, w', hw' => by
    dsimp only [checkZeroList] at hok
    cases hc : Nat.beq (wGet tr w) 0
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    rcases List.mem_cons.mp hw' with rfl | hmem
    · exact Nat.beq_eq.mp hc
    · exact checkZeroList_sound ws hok w' hmem


inductive LTree : Type where
  | leaf (w0 w1 w2 : Nat)
  | node (l r : LTree)

def ltGet : Nat → LTree → Nat → (Nat × Nat × Nat)
  | _, .leaf w0 w1 w2, _ => (w0, w1, w2)
  | 0, .node l r, idx => cond (Nat.blt idx 1) (ltGet 0 l idx) (ltGet 0 r (idx - 1))
  | d + 1, .node l r, idx =>
      let half := Nat.shiftLeft 1 (d + 1)
      cond (Nat.blt idx half) (ltGet d l idx) (ltGet d r (idx - half))

def ltSet : Nat → LTree → Nat → (Nat × Nat × Nat) → LTree
  | _, .leaf _ _ _, _, p => .leaf p.1 p.2.1 p.2.2
  | 0, .node l r, idx, p =>
      cond (Nat.blt idx 1) (.node (ltSet 0 l idx p) r) (.node l (ltSet 0 r (idx - 1) p))
  | d + 1, .node l r, idx, p =>
      let half := Nat.shiftLeft 1 (d + 1)
      cond (Nat.blt idx half)
        (.node (ltSet d l idx p) r)
        (.node l (ltSet d r (idx - half) p))

inductive LTreeWF : Nat → LTree → Prop where
  | leaf (w0 w1 w2 : Nat) : LTreeWF 0 (.leaf w0 w1 w2)
  | node {d : Nat} {l r : LTree} : LTreeWF d l → LTreeWF d r → LTreeWF (d + 1) (.node l r)

def checkLTreeWF : Nat → LTree → Bool
  | 0, .leaf _ _ _ => true
  | d + 1, .node l r => checkLTreeWF d l && checkLTreeWF d r
  | _, _ => false

theorem checkLTreeWF_sound : ∀ d tr, checkLTreeWF d tr = true → LTreeWF d tr
  | 0, .leaf w0 w1 w2, _ => .leaf w0 w1 w2
  | d + 1, .node l r, h => by
    dsimp only [checkLTreeWF] at h
    rw [Bool.and_eq_true] at h
    exact .node (checkLTreeWF_sound d l h.1) (checkLTreeWF_sound d r h.2)
  | 0, .node _ _, h => by cases h
  | _ + 1, .leaf _ _ _, h => by cases h

theorem ltSet_wf : ∀ {d : Nat} {tr : LTree}, LTreeWF (d + 1) tr →
    ∀ idx p, LTreeWF (d + 1) (ltSet d tr idx p)
  | 0, .node (.leaf a0 a1 a2) (.leaf b0 b1 b2), .node (.leaf _ _ _) (.leaf _ _ _), idx, p => by
    dsimp only [ltSet]
    cases Nat.blt idx 1 <;> exact .node (.leaf _ _ _) (.leaf _ _ _)
  | d + 1, .node l r, .node hfl hfr, idx, p => by
    dsimp only [ltSet]
    cases Nat.blt idx (Nat.shiftLeft 1 (d + 1))
    · exact .node hfl (ltSet_wf hfr _ _)
    · exact .node (ltSet_wf hfl _ _) hfr

theorem ltGet_ltSet : ∀ {d : Nat} {tr : LTree}, LTreeWF (d + 1) tr →
    ∀ {idx j : Nat}, idx < 2 ^ (d + 1) → j < 2 ^ (d + 1) → ∀ p : Nat × Nat × Nat,
    ltGet d (ltSet d tr idx p) j = if j = idx then p else ltGet d tr j
  | 0, .node (.leaf _ _ _) (.leaf _ _ _), .node (.leaf _ _ _) (.leaf _ _ _),
      idx, j, hidx, hj, p => by
    have hi1 : idx = 0 ∨ idx = 1 := by omega
    have hj1 : j = 0 ∨ j = 1 := by omega
    rcases hi1 with rfl | rfl <;> rcases hj1 with rfl | rfl <;> rfl
  | d + 1, .node l r, .node hl hr, idx, j, hidx, hj, p => by
    have hpow : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by ring
    dsimp only [ltGet, ltSet]
    rw [shiftLeft_eq_mul_pow, one_mul]
    cases hbi : Nat.blt idx (2 ^ (d + 1))
    · have hi' : 2 ^ (d + 1) ≤ idx := (blt_false_iff _ _).1 hbi
      dsimp only [cond, ltGet]
      rw [shiftLeft_eq_mul_pow, one_mul]
      cases hbj : Nat.blt j (2 ^ (d + 1))
      · have hj' : 2 ^ (d + 1) ≤ j := (blt_false_iff _ _).1 hbj
        dsimp only [cond]
        rw [ltGet_ltSet hr (by omega) (by omega)]
        split_ifs with h1 h2 <;> first | rfl | omega
      · have hj' : j < 2 ^ (d + 1) := Nat.blt_eq.mp hbj
        dsimp only [cond]
        rw [ite_eq_right (by omega)]
    · have hi' : idx < 2 ^ (d + 1) := Nat.blt_eq.mp hbi
      dsimp only [cond, ltGet]
      rw [shiftLeft_eq_mul_pow, one_mul]
      cases hbj : Nat.blt j (2 ^ (d + 1))
      · have hj' : 2 ^ (d + 1) ≤ j := (blt_false_iff _ _).1 hbj
        dsimp only [cond]
        rw [ite_eq_right (by omega)]
      · have hj' : j < 2 ^ (d + 1) := Nat.blt_eq.mp hbj
        dsimp only [cond]
        exact ltGet_ltSet hl hi' hj' p

def xorFold (f : Nat → Bool) (word : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => xor (xorFold f word n) (word.testBit n && f n)

theorem xorFold_zero (f : Nat → Bool) : ∀ n, xorFold f 0 n = false
  | 0 => rfl
  | n + 1 => by simp [xorFold, xorFold_zero f n]

theorem xorFold_xor (f : Nat → Bool) (a b : Nat) :
    ∀ n, xorFold f (a ^^^ b) n = xor (xorFold f a n) (xorFold f b n)
  | 0 => rfl
  | n + 1 => by
    have htb : (a ^^^ b).testBit n = xor (a.testBit n) (b.testBit n) := Nat.testBit_xor a b n
    simp only [xorFold, htb, xorFold_xor f a b n]
    cases xorFold f a n <;> cases xorFold f b n <;>
      cases a.testBit n <;> cases b.testBit n <;> cases f n <;> rfl

theorem xorFold_shl_eq_false (f : Nat → Bool) (i : Nat) :
    ∀ n, n ≤ i → xorFold f (Nat.shiftLeft 1 i) n = false
  | 0, _ => rfl
  | n + 1, hn => by
    have htb : (Nat.shiftLeft 1 i).testBit n = false := by
      rw [shiftLeft_eq_mul_pow, one_mul, Nat.testBit_two_pow_of_ne (by omega)]
    rw [xorFold, xorFold_shl_eq_false f i n (by omega), htb]
    rfl

theorem xorFold_shl_one (f : Nat → Bool) {i : Nat} :
    ∀ {n : Nat}, i < n → xorFold f (Nat.shiftLeft 1 i) n = f i
  | 0, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, hi => by
    rw [xorFold]
    by_cases h : i = n
    · subst h
      have htb : (Nat.shiftLeft 1 i).testBit i = true := by
        rw [shiftLeft_eq_mul_pow, one_mul, Nat.testBit_two_pow_self]
      rw [xorFold_shl_eq_false f i i le_rfl, htb]
      cases f i <;> rfl
    · have htb : (Nat.shiftLeft 1 i).testBit n = false := by
        rw [shiftLeft_eq_mul_pow, one_mul, Nat.testBit_two_pow_of_ne (by omega)]
      rw [xorFold_shl_one f (by omega), htb]
      cases f i <;> rfl

theorem xorLinMask_sound (m : Fin 100 → Bool) (t : Nat) :
    ∀ (ls : List Nat) (acc acc' : Nat),
      xorLinMask t ls acc = some acc' →
      (∀ c ∈ ls, c < 100 ∧ c ≠ t) ∧
      xorFold (fun c => if h : c < 100 then m ⟨c, h⟩ else false) acc' 100 =
        xor (xorFold (fun c => if h : c < 100 then m ⟨c, h⟩ else false) acc 100)
          (evalLinBool102 m ls)
  | [], acc, acc', h => by
    injection h with heq; subst heq
    exact ⟨fun _ hc => (by cases hc), by simp [evalLinBool102]⟩
  | c :: cs, acc, acc', h => by
    dsimp only [xorLinMask] at h
    cases hc : (Nat.blt c 100 && !Nat.beq c t)
    · rw [hc, Bool.cond_false] at h; cases h
    rw [hc, Bool.cond_true] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff] at hc
    obtain ⟨hclt, hct⟩ := hc
    obtain ⟨hcs, hev⟩ := xorLinMask_sound m t cs (acc ^^^ Nat.shiftLeft 1 c) acc' h
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hmem
      · exact ⟨hclt, hct⟩
      · exact hcs x hmem
    · set f : Nat → Bool := fun j => if hj : j < 100 then m ⟨j, hj⟩ else false
      have hfc : f c = m ⟨c, hclt⟩ := dite_eq_left hclt
      rw [hev, xorFold_xor, xorFold_shl_one f hclt, hfc]
      dsimp only [evalLinBool102]
      rw [dite_eq_left hclt, Bool.xor_assoc]

abbrev mBitFn (m : Fin 100 → Bool) (j : Nat) : Bool :=
  if hj : j < 100 then m ⟨j, hj⟩ else false

theorem stepHStatic_pos_sound (m : Fin 100 → Bool) (t : Nat) :
    ∀ (steps : List (Bool × List Nat)) (stS stS' : Nat × Bool × Nat × Bool)
      (stB : Bool × Bool × Bool × Bool),
      stB.1 = xor stS.2.1 (xorFold (mBitFn m) stS.1 100) →
      stB.2.1 = xor stS.2.2.2 (xorFold (mBitFn m) stS.2.2.1 100) →
      stepHStatic t steps stS = some stS' →
      (∀ p ∈ steps, ∀ c ∈ p.2, c < 100 ∧ c ≠ t) ∧
      let stB' := evalHPosBool m steps stB
      stB'.1 = xor stS'.2.1 (xorFold (mBitFn m) stS'.1 100) ∧
      stB'.2.1 = xor stS'.2.2.2 (xorFold (mBitFn m) stS'.2.2.1 100)
  | [], stS, stS', stB, hdt, hb0, hok => by
    injection hok with h; subst h
    exact ⟨fun _ hp => (by cases hp), hdt, hb0⟩
  | (xc, ls) :: rest, (dtM, dtC, b0M, b0C), stS', (dt, b0, b1, b2), hdt, hb0, hok => by
    dsimp only at hdt hb0
    dsimp only [stepHStatic] at hok
    cases hx : xorLinMask t ls dtM with
    | none => rw [hx] at hok; cases hok
    | some dtM' =>
      rw [hx] at hok; dsimp only at hok
      obtain ⟨hls, hx_ev⟩ := xorLinMask_sound m t ls dtM dtM' hx
      set dt' := xor dt (xor xc (evalLinBool102 m ls))
      set r := add1Bools b0 b1 b2 dt'
      have hdt' : dt' = xor (xor dtC xc) (xorFold (mBitFn m) dtM' 100) := by
        dsimp only [dt']; rw [hdt, hx_ev, xor_xor_comm]
      have hb0' : r.1 = xor (xor b0C (xor dtC xc)) (xorFold (mBitFn m) (b0M ^^^ dtM') 100) := by
        change xor b0 dt' = _
        rw [hb0, hdt', xorFold_xor, xor_xor_comm]
      obtain ⟨hrest, hdt_f, hb0_f⟩ :=
        stepHStatic_pos_sound m t rest (dtM', xor dtC xc, b0M ^^^ dtM', xor b0C (xor dtC xc))
          stS' (dt', r.1, r.2.1, r.2.2) hdt' hb0' hok
      refine ⟨fun p hp => ?_, hdt_f, hb0_f⟩
      rcases List.mem_cons.mp hp with rfl | hmem
      · exact hls
      · exact hrest p hmem

theorem stepHStatic_neg_sound (m : Fin 100 → Bool) (t : Nat) :
    ∀ (steps : List (Bool × List Nat)) (stS stS' : Nat × Bool × Nat × Bool)
      (stB : Bool × Bool × Bool × Bool),
      stB.1 = xor stS.2.1 (xorFold (mBitFn m) stS.1 100) →
      stB.2.1 = xor stS.2.2.2 (xorFold (mBitFn m) stS.2.2.1 100) →
      stepHStatic t steps stS = some stS' →
      (∀ p ∈ steps, ∀ c ∈ p.2, c < 100 ∧ c ≠ t) ∧
      let stB' := evalHNegBool m steps stB
      stB'.1 = xor stS'.2.1 (xorFold (mBitFn m) stS'.1 100) ∧
      stB'.2.1 = xor stS'.2.2.2 (xorFold (mBitFn m) stS'.2.2.1 100)
  | [], stS, stS', stB, hdt, hb0, hok => by
    injection hok with h; subst h
    exact ⟨fun _ hp => (by cases hp), hdt, hb0⟩
  | (xc, ls) :: rest, (dtM, dtC, b0M, b0C), stS', (dt, b0, b1, b2), hdt, hb0, hok => by
    dsimp only at hdt hb0
    dsimp only [stepHStatic] at hok
    cases hx : xorLinMask t ls dtM with
    | none => rw [hx] at hok; cases hok
    | some dtM' =>
      rw [hx] at hok; dsimp only at hok
      obtain ⟨hls, hx_ev⟩ := xorLinMask_sound m t ls dtM dtM' hx
      set dt' := xor dt (xor xc (evalLinBool102 m ls))
      set r := add7Bools b0 b1 b2 dt'
      have hdt' : dt' = xor (xor dtC xc) (xorFold (mBitFn m) dtM' 100) := by
        dsimp only [dt']; rw [hdt, hx_ev, xor_xor_comm]
      have hb0' : r.1 = xor (xor b0C (xor dtC xc)) (xorFold (mBitFn m) (b0M ^^^ dtM') 100) := by
        change xor b0 dt' = _
        rw [hb0, hdt', xorFold_xor, xor_xor_comm]
      obtain ⟨hrest, hdt_f, hb0_f⟩ :=
        stepHStatic_neg_sound m t rest (dtM', xor dtC xc, b0M ^^^ dtM', xor b0C (xor dtC xc))
          stS' (dt', r.1, r.2.1, r.2.2) hdt' hb0' hok
      refine ⟨fun p hp => ?_, hdt_f, hb0_f⟩
      rcases List.mem_cons.mp hp with rfl | hmem
      · exact hls
      · exact hrest p hmem

theorem checkHGadgetStatic_sound (m : Fin 100 → Bool) {t : Nat}
    {pos neg : List (Bool × List Nat)} {uc : Bool} {ul : List Nat}
    (hok : checkHGadgetStatic t pos neg uc ul = true) :
    t < 100 ∧
    pos.length = neg.length ∧
    (∀ p ∈ pos, ∀ c ∈ p.2, c < 100 ∧ c ≠ t) ∧
    (∀ p ∈ neg, ∀ c ∈ p.2, c < 100 ∧ c ≠ t) ∧
    (∀ c ∈ ul, c < 100 ∧ c ≠ t) ∧
    (evalHGadgetBool m pos neg uc ul).1 = false ∧
    (evalHGadgetBool m pos neg uc ul).2.1 = false := by
  unfold checkHGadgetStatic at hok
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hok
  obtain ⟨⟨ht, hlen⟩, hrun⟩ := hok
  cases hs1 : stepHStatic t pos (0, false, 0, false) with
  | none => rw [hs1] at hrun; cases hrun
  | some st1 =>
    rw [hs1] at hrun; dsimp only at hrun
    cases hs2 : stepHStatic t neg st1 with
    | none => rw [hs2] at hrun; cases hrun
    | some st2 =>
      rcases st2 with ⟨dtM2, dtC2, b0M2, b0C2⟩
      rw [hs2] at hrun; dsimp only at hrun
      cases hs3 : xorLinMask t ul dtM2 with
      | none => rw [hs3] at hrun; cases hrun
      | some dtMf =>
        rw [hs3] at hrun; dsimp only at hrun
        simp only [Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hrun
        obtain ⟨⟨⟨hdtMf, hdtCf⟩, hb0M2⟩, hb0C2⟩ := hrun
        set f : Nat → Bool := fun j => if hj : j < 100 then m ⟨j, hj⟩ else false
        have h0_dt : (false : Bool) = xor false (xorFold f 0 100) := by rw [xorFold_zero]; rfl
        have h0_b0 : (false : Bool) = xor false (xorFold f 0 100) := by rw [xorFold_zero]; rfl
        obtain ⟨hpos_v, hdt1, hb0_1⟩ := stepHStatic_pos_sound m t pos (0, false, 0, false) st1
          (false, false, false, false) h0_dt h0_b0 hs1
        obtain ⟨hneg_v, hdt2, hb0_2⟩ := stepHStatic_neg_sound m t neg st1 (dtM2, dtC2, b0M2, b0C2)
          (evalHPosBool m pos (false, false, false, false)) hdt1 hb0_1 hs2
        obtain ⟨hul_v, hul_ev⟩ := xorLinMask_sound m t ul dtM2 dtMf hs3
        refine ⟨ht, hlen, hpos_v, hneg_v, hul_v, ?_, ?_⟩
        · unfold evalHGadgetBool
          dsimp only
          rw [hdt2, xor_xor_comm, ← hul_ev, hdtMf, hdtCf, xorFold_zero]; rfl
        · unfold evalHGadgetBool
          dsimp only
          rw [hb0_2, hb0M2, hb0C2, xorFold_zero]; rfl

def xor3 (a b : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (a.1 ^^^ b.1, a.2.1 ^^^ b.2.1, a.2.2 ^^^ b.2.2)

def eq3 (a b : Nat × Nat × Nat) : Bool :=
  Nat.beq a.1 b.1 && Nat.beq a.2.1 b.2.1 && Nat.beq a.2.2 b.2.2

theorem eq3_iff {a b : Nat × Nat × Nat} : eq3 a b = true ↔ a = b := by
  rcases a with ⟨a1, a2, a3⟩
  rcases b with ⟨b1, b2, b3⟩
  simp only [eq3, Bool.and_eq_true, Nat.beq_eq, Prod.mk.injEq]
  tauto

def evalL3 (f0 f1 f2 : Nat → Bool) (p : Nat × Nat × Nat) : Bool :=
  xor (xor (xorFold f0 p.1 60) (xorFold f1 p.2.1 57)) (xorFold f2 p.2.2 28)

theorem evalL3_zero (f0 f1 f2 : Nat → Bool) : evalL3 f0 f1 f2 (0, 0, 0) = false := by
  simp [evalL3, xorFold_zero]

theorem evalL3_xor (f0 f1 f2 : Nat → Bool) (a b : Nat × Nat × Nat) :
    evalL3 f0 f1 f2 (xor3 a b) = xor (evalL3 f0 f1 f2 a) (evalL3 f0 f1 f2 b) := by
  simp only [evalL3, xor3, xorFold_xor]
  cases xorFold f0 a.1 60 <;> cases xorFold f0 b.1 60 <;>
    cases xorFold f1 a.2.1 57 <;> cases xorFold f1 b.2.1 57 <;>
    cases xorFold f2 a.2.2 28 <;> cases xorFold f2 b.2.2 28 <;> rfl

theorem evalL3_shl0 (f0 f1 f2 : Nat → Bool) {b : Nat} (hb : b < 60) :
    evalL3 f0 f1 f2 (Nat.shiftLeft 1 b, 0, 0) = f0 b := by
  simp only [evalL3, xorFold_shl_one f0 hb, xorFold_zero]
  cases f0 b <;> rfl

theorem evalL3_shl1 (f0 f1 f2 : Nat → Bool) {b : Nat} (hb : b < 57) :
    evalL3 f0 f1 f2 (0, Nat.shiftLeft 1 b, 0) = f1 b := by
  simp only [evalL3, xorFold_zero, xorFold_shl_one f1 hb]
  cases f1 b <;> rfl

theorem evalL3_shl2 (f0 f1 f2 : Nat → Bool) {b : Nat} (hb : b < 28) :
    evalL3 f0 f1 f2 (0, 0, Nat.shiftLeft 1 b) = f2 b := by
  simp only [evalL3, xorFold_zero, xorFold_shl_one f2 hb]
  cases f2 b <;> rfl

theorem evalL3_one (f0 f1 f2 : Nat → Bool) : evalL3 f0 f1 f2 (1, 0, 0) = f0 0 := by
  rw [show (1 : Nat) = Nat.shiftLeft 1 0 from rfl]
  exact evalL3_shl0 f0 f1 f2 (by omega)

def majBool (a b c : Bool) : Bool := (a && b) || ((a || b) && c)

theorem majBool_cuccaro (x b c : Bool) :
    xor ((xor x c) && (xor b c)) c = majBool x b c := by
  cases x <;> cases b <;> cases c <;> rfl

theorem majBool_zero (b c : Bool) :
    (c && b) = majBool false b c := by
  cases b <;> cases c <;> rfl

theorem majBool_one_not (b c : Bool) :
    ((!b) && (!c)) = !(majBool true b c) := by
  cases b <;> cases c <;> rfl

def idExpr (w : Nat) : Nat × Nat × Nat :=
  if w + 1 < 60 then (Nat.shiftLeft 1 (w + 1), 0, 0)
  else (0, Nat.shiftLeft 1 (w - 59), 0)

def bExpr (targ : List Nat) (flip_out : Bool) (falseW : List Nat) (k : Nat) : Nat × Nat × Nat :=
  let base := match targ[k]? with
    | some w => if falseW.elem w then (0, 0, 0) else idExpr w
    | none => (0, 0, 0)
  xor3 base (if flip_out then (1, 0, 0) else (0, 0, 0))

def cExpr (targ : List Nat) (flip_out : Bool) (falseW : List Nat)
    (c0_expr : Nat × Nat × Nat) (xlist : List (Nat × Nat × Nat)) : Nat → (Nat × Nat × Nat)
  | 0 => c0_expr
  | k + 1 =>
      let prev_c := cExpr targ flip_out falseW c0_expr xlist k
      let xk := xlist.getD k (0, 0, 0)
      let bk := bExpr targ flip_out falseW k
      cond ((eq3 prev_c (0, 0, 0) && eq3 xk (0, 0, 0)) ||
            (eq3 bk (0, 0, 0) && eq3 xk (0, 0, 0)) ||
            (eq3 bk (0, 0, 0) && eq3 prev_c (0, 0, 0)))
        (0, 0, 0)
        (0, 0, Nat.shiftLeft 1 (k + 1))

def matchCarryBit (targ : List Nat) (flip_out : Bool) (falseW : List Nat)
    (c0_expr : Nat × Nat × Nat) (xlist : List (Nat × Nat × Nat)) (v1 v2 : Nat × Nat × Nat) :
    List (Nat × Nat × Nat) → Nat → Option (Nat × Nat × Nat)
  | [], _ => none
  | xk :: rest, k =>
      let bk := bExpr targ flip_out falseW k
      let ck := cExpr targ flip_out falseW c0_expr xlist k
      let bc := xor3 bk ck
      let xc := xor3 xk ck
      let bx := xor3 bk xk
      let ck1 := cExpr targ flip_out falseW c0_expr xlist (k + 1)
      let nbk := xor3 (1, 0, 0) bk
      let nck := xor3 (1, 0, 0) ck
      cond ((eq3 v1 xc && eq3 v2 bc) || (eq3 v1 bc && eq3 v2 xc))
        (some (xor3 ck1 ck))
        (cond (((eq3 v1 bk && eq3 v2 ck) || (eq3 v1 ck && eq3 v2 bk)) && eq3 xk (0, 0, 0))
          (some ck1)
          (cond ((!flip_out) && eq3 xk (1, 0, 0) &&
                 ((eq3 v1 nbk && eq3 v2 nck) || (eq3 v1 nck && eq3 v2 nbk)))
            (some (xor3 (1, 0, 0) ck1))
            (cond ((eq3 v1 bx && eq3 v2 xc) || (eq3 v1 xc && eq3 v2 bx))
              (some (xor3 ck1 xk))
              (cond (((eq3 v1 xk && eq3 v2 ck) || (eq3 v1 ck && eq3 v2 xk)) && eq3 bk (0, 0, 0))
                (some ck1)
                (matchCarryBit targ flip_out falseW c0_expr xlist v1 v2 rest (k + 1))))))

def mulLin (targ : List Nat) (flip_out : Bool) (falseW : List Nat) (c0_expr : Nat × Nat × Nat)
    (xlist : List (Nat × Nat × Nat)) (v1 v2 : Nat × Nat × Nat) : Option (Nat × Nat × Nat) :=
  cond (eq3 v1 (0, 0, 0) || eq3 v2 (0, 0, 0))
    (some (0, 0, 0))
    (cond (eq3 v1 (1, 0, 0))
      (some v2)
      (cond (eq3 v2 (1, 0, 0))
        (some v1)
        (cond (eq3 v1 v2)
          (some v1)
          (cond (eq3 (xor3 v1 v2) (1, 0, 0))
            (some (0, 0, 0))
            (matchCarryBit targ flip_out falseW c0_expr xlist v1 v2 xlist 0)))))

def evalQuadAddOpt (targ : List Nat) (flip_out : Bool) (falseW : List Nat)
    (c0_expr : Nat × Nat × Nat) (xlist : List (Nat × Nat × Nat)) (tr : LTree) (t : Nat) :
    List (Nat × Nat) → Option (Nat × Nat × Nat)
  | [] => some (0, 0, 0)
  | (a, b) :: rest =>
      cond (Nat.blt a 100 && Nat.blt b 100 && (!Nat.beq a b) && (!Nat.beq a t) && (!Nat.beq b t))
        (match mulLin targ flip_out falseW c0_expr xlist (ltGet 6 tr a) (ltGet 6 tr b) with
         | none => none
         | some pr =>
             match evalQuadAddOpt targ flip_out falseW c0_expr xlist tr t rest with
             | none => none
             | some acc => some (xor3 pr acc))
        none

def evalLinAddOpt (tr : LTree) (t : Nat) : List Nat → Option (Nat × Nat × Nat)
  | [] => some (0, 0, 0)
  | c :: rest =>
      cond (Nat.blt c 100 && (!Nat.beq c t))
        (match evalLinAddOpt tr t rest with
         | some acc => some (xor3 (ltGet 6 tr c) acc)
         | none => none)
        none

def stepAddOpt (targ : List Nat) (flip_out : Bool) (falseW : List Nat)
    (c0_expr : Nat × Nat × Nat) (xlist : List (Nat × Nat × Nat)) (tr : LTree) : Op102 → Option LTree
  | .x q =>
      cond (Nat.blt q 100)
        (some (ltSet 6 tr q (xor3 (ltGet 6 tr q) (1, 0, 0))))
        none
  | .cx c t =>
      cond (Nat.blt c 100 && Nat.blt t 100 && (!Nat.beq c t))
        (some (ltSet 6 tr t (xor3 (ltGet 6 tr t) (ltGet 6 tr c))))
        none
  | .and4t c1 c2 t =>
      cond (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
            (!Nat.beq c1 c2) && (!Nat.beq c1 t) && (!Nat.beq c2 t) &&
            eq3 (ltGet 6 tr t) (0, 0, 0))
        (match mulLin targ flip_out falseW c0_expr xlist (ltGet 6 tr c1) (ltGet 6 tr c2) with
         | none => none
         | some pr => some (ltSet 6 tr t pr))
        none
  | .rccx0 _ _ _ => none
  | .rccx1 _ _ _ => none
  | .unand c1 c2 t =>
      cond (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
            (!Nat.beq c1 c2) && (!Nat.beq c1 t) && (!Nat.beq c2 t))
        (match mulLin targ flip_out falseW c0_expr xlist (ltGet 6 tr c1) (ltGet 6 tr c2) with
         | none => none
         | some pr =>
             cond (eq3 (ltGet 6 tr t) pr)
               (some (ltSet 6 tr t (0, 0, 0)))
               none)
        none
  | .unquad qs ls t =>
      cond (Nat.blt t 100)
        (match evalQuadAddOpt targ flip_out falseW c0_expr xlist tr t qs with
         | none => none
         | some vq =>
             match evalLinAddOpt tr t ls with
             | none => none
             | some vl =>
                 cond (eq3 (ltGet 6 tr t) (xor3 vq vl))
                   (some (ltSet 6 tr t (0, 0, 0)))
                   none)
        none
  | .z _ => none
  | .cz _ _ => none
  | .hGadget _ _ _ _ _ => none

def runAddListOpt (targ : List Nat) (flip_out : Bool) (falseW : List Nat)
    (c0_expr : Nat × Nat × Nat) (xlist : List (Nat × Nat × Nat)) : List Op102 → LTree → Option LTree
  | [], tr => some tr
  | op :: ops, tr =>
      match stepAddOpt targ flip_out falseW c0_expr xlist tr op with
      | some tr1 => runAddListOpt targ flip_out falseW c0_expr xlist ops tr1
      | none => none

def addFLo (m0 : Fin 100 → Bool) : Nat → Bool
  | 0 => true
  | j + 1 => if h : j < 100 then m0 ⟨j, h⟩ else false

def addFMid (m0 : Fin 100 → Bool) (j : Nat) : Bool :=
  if h : 59 + j < 100 then m0 ⟨59 + j, h⟩ else false

def targBit (targ : List Nat) (m : Fin 100 → Bool) (k : Nat) : Bool :=
  match targ[k]? with
  | some w => if h : w < 100 then m ⟨w, h⟩ else false
  | none => false

def addCarry (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out : Bool)
    (c0_val : Bool) (x_eval : Nat → Bool) : Nat → Bool
  | 0 => c0_val
  | k + 1 =>
      majBool (x_eval k) (xor (targBit targ m0 k) flip_out)
        (addCarry m0 targ flip_out c0_val x_eval k)

def addEv (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out : Bool) (c0_val : Bool)
    (x_eval : Nat → Bool) (p : Nat × Nat × Nat) : Bool :=
  evalL3 (addFLo m0) (addFMid m0) (addCarry m0 targ flip_out c0_val x_eval) p

theorem addEv_zero (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out c0_val : Bool)
    (x_eval : Nat → Bool) :
    addEv m0 targ flip_out c0_val x_eval (0, 0, 0) = false :=
  evalL3_zero _ _ _

theorem addEv_one (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out c0_val : Bool)
    (x_eval : Nat → Bool) :
    addEv m0 targ flip_out c0_val x_eval (1, 0, 0) = true :=
  evalL3_one _ _ _

theorem addEv_xor (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out c0_val : Bool)
    (x_eval : Nat → Bool)
    (a b : Nat × Nat × Nat) :
    addEv m0 targ flip_out c0_val x_eval (xor3 a b) =
    xor (addEv m0 targ flip_out c0_val x_eval a) (addEv m0 targ flip_out c0_val x_eval b) :=
  evalL3_xor _ _ _ a b

theorem addEv_idExpr (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out c0_val : Bool)
    (x_eval : Nat → Bool) (w : Fin 100) :
    addEv m0 targ flip_out c0_val x_eval (idExpr w.val) = m0 w := by
  unfold idExpr addEv
  by_cases hw : w.val + 1 < 60
  · simp only [ite_eq_left hw, evalL3_shl0 _ _ _ hw, addFLo, dite_eq_left w.isLt]
  · simp only [ite_eq_right hw, evalL3_shl1 _ _ _ (by omega : w.val - 59 < 57)]
    unfold addFMid
    simp only [show 59 + (w.val - 59) = w.val by omega, dite_eq_left w.isLt]

theorem addEv_bExpr (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out c0_val : Bool)
    (falseW : List Nat) (x_eval : Nat → Bool) (k : Nat)
    (htarg : ∀ w ∈ targ, w < 100)
    (hfalse : ∀ w : Fin 100, w.val ∈ falseW → m0 w = false) :
    addEv m0 targ flip_out c0_val x_eval (bExpr targ flip_out falseW k) =
    xor (targBit targ m0 k) flip_out := by
  unfold bExpr targBit
  have hbase : addEv m0 targ flip_out c0_val x_eval
      (match targ[k]? with
       | some w => if falseW.elem w then (0, 0, 0) else idExpr w
       | none => (0, 0, 0)) =
      (match targ[k]? with
       | some w => if h : w < 100 then m0 ⟨w, h⟩ else false
       | none => false) := by
    cases hget : targ[k]? with
    | none => exact addEv_zero m0 targ flip_out c0_val x_eval
    | some w =>
      dsimp only
      have hwlt : w < 100 := htarg w (List.mem_of_getElem? hget)
      rw [dite_eq_left hwlt]
      cases he : falseW.elem w
      · exact addEv_idExpr m0 targ flip_out c0_val x_eval ⟨w, hwlt⟩
      · rw [ite_eq_left rfl, addEv_zero]
        exact (hfalse ⟨w, hwlt⟩ (List.mem_of_elem_eq_true he)).symm
  rw [addEv_xor, hbase]
  cases flip_out <;> simp [addEv_zero, addEv_one]

theorem addEv_cExpr (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out c0_val : Bool)
    (falseW : List Nat) (x_eval : Nat → Bool)
    {c0_expr : Nat × Nat × Nat} {xlist : List (Nat × Nat × Nat)}
    (hc0 : addEv m0 targ flip_out c0_val x_eval c0_expr = c0_val)
    (htarg : ∀ w ∈ targ, w < 100)
    (hfalse : ∀ w : Fin 100, w.val ∈ falseW → m0 w = false)
    (hx_all : ∀ j, addEv m0 targ flip_out c0_val x_eval (xlist.getD j (0, 0, 0)) = x_eval j) :
    ∀ {k : Nat} (_hk : k ≤ 25),
      addEv m0 targ flip_out c0_val x_eval (cExpr targ flip_out falseW c0_expr xlist k) =
        addCarry m0 targ flip_out c0_val x_eval k
  | 0, _ => hc0
  | k + 1, hk => by
    have ih :=
      addEv_cExpr m0 targ flip_out c0_val falseW x_eval hc0 htarg hfalse hx_all (by omega : k ≤ 25)
    have hxk_ev := hx_all k
    have hbk_ev := addEv_bExpr m0 targ flip_out c0_val falseW x_eval k htarg hfalse
    dsimp only [cExpr]
    set prev_c := cExpr targ flip_out falseW c0_expr xlist k
    set xk := xlist.getD k (0, 0, 0)
    set bk := bExpr targ flip_out falseW k
    cases hcond : ((eq3 prev_c (0, 0, 0) && eq3 xk (0, 0, 0)) ||
                   (eq3 bk (0, 0, 0) && eq3 xk (0, 0, 0)) ||
                   (eq3 bk (0, 0, 0) && eq3 prev_c (0, 0, 0)))
    · simp only [Bool.cond_false]
      unfold addEv
      rw [evalL3_shl2 _ _ _ (by omega : k + 1 < 28)]
    · simp only [Bool.cond_true]
      rw [addEv_zero, addCarry]
      simp only [Bool.or_eq_true, Bool.and_eq_true, eq3_iff] at hcond
      rcases hcond with (⟨hprev0, hxk0⟩ | ⟨hbk0, hxk0⟩) | ⟨hbk0, hprev0⟩
      · rw [hprev0, addEv_zero] at ih
        rw [hxk0, addEv_zero] at hxk_ev
        rw [← hxk_ev, ← ih]
        cases xor (targBit targ m0 k) flip_out <;> rfl
      · rw [hbk0, addEv_zero] at hbk_ev
        rw [hxk0, addEv_zero] at hxk_ev
        rw [← hxk_ev, ← hbk_ev]
        cases addCarry m0 targ flip_out c0_val x_eval k <;> rfl
      · rw [hbk0, addEv_zero] at hbk_ev
        rw [hprev0, addEv_zero] at ih
        rw [← hbk_ev, ← ih]
        cases x_eval k <;> rfl

attribute [irreducible] addEv

theorem matchCarryBit_sound (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out c0_val : Bool)
    (falseW : List Nat) (x_eval : Nat → Bool)
    {c0_expr : Nat × Nat × Nat} {xlist : List (Nat × Nat × Nat)}
    (hc0 : addEv m0 targ flip_out c0_val x_eval c0_expr = c0_val)
    (htarg : ∀ w ∈ targ, w < 100)
    (hfalse : ∀ w : Fin 100, w.val ∈ falseW → m0 w = false)
    (hx_all : ∀ j, addEv m0 targ flip_out c0_val x_eval (xlist.getD j (0, 0, 0)) = x_eval j)
    (v1 v2 : Nat × Nat × Nat) :
    ∀ (xs : List (Nat × Nat × Nat)) (k : Nat) {pr : Nat × Nat × Nat},
      k + xs.length ≤ targ.length →
      k + xs.length ≤ 25 →
      (∀ i p, xs[i]? = some p → addEv m0 targ flip_out c0_val x_eval p = x_eval (k + i)) →
      matchCarryBit targ flip_out falseW c0_expr xlist v1 v2 xs k = some pr →
      addEv m0 targ flip_out c0_val x_eval pr =
        (addEv m0 targ flip_out c0_val x_eval v1 && addEv m0 targ flip_out c0_val x_eval v2)
  | [], _, _, _, _, _, h => by cases h
  | xk :: rest, k, pr, hlen, hM, hxs, h => by
    dsimp only [List.length_cons] at hlen hM
    have hbk := addEv_bExpr m0 targ flip_out c0_val falseW x_eval k htarg hfalse
    have hck :=
      addEv_cExpr m0 targ flip_out c0_val falseW x_eval hc0 htarg hfalse hx_all (by omega : k ≤ 25)
    have hck1 := addEv_cExpr m0 targ flip_out c0_val falseW x_eval hc0 htarg hfalse hx_all
      (by omega : k + 1 ≤ 25)
    have hxk : addEv m0 targ flip_out c0_val x_eval xk = x_eval k := by
      simpa using hxs 0 xk rfl
    dsimp only [matchCarryBit] at h
    set bk := bExpr targ flip_out falseW k
    set ck := cExpr targ flip_out falseW c0_expr xlist k
    set bc := xor3 bk ck
    set xc := xor3 xk ck
    set bx := xor3 bk xk
    set ck1 := cExpr targ flip_out falseW c0_expr xlist (k + 1)
    set nbk := xor3 (1, 0, 0) bk
    set nck := xor3 (1, 0, 0) ck
    cases c1 : ((eq3 v1 xc && eq3 v2 bc) || (eq3 v1 bc && eq3 v2 xc))
    · rw [c1, Bool.cond_false] at h
      cases c2 : (((eq3 v1 bk && eq3 v2 ck) || (eq3 v1 ck && eq3 v2 bk)) && eq3 xk (0, 0, 0))
      · rw [c2, Bool.cond_false] at h
        cases c3 : ((!flip_out) && eq3 xk (1, 0, 0) &&
                    ((eq3 v1 nbk && eq3 v2 nck) || (eq3 v1 nck && eq3 v2 nbk)))
        · rw [c3, Bool.cond_false] at h
          cases c4 : ((eq3 v1 bx && eq3 v2 xc) || (eq3 v1 xc && eq3 v2 bx))
          · rw [c4, Bool.cond_false] at h
            cases c5 : (((eq3 v1 xk && eq3 v2 ck) || (eq3 v1 ck && eq3 v2 xk)) && eq3 bk (0, 0, 0))
            · rw [c5, Bool.cond_false] at h
              exact matchCarryBit_sound m0 targ flip_out c0_val falseW x_eval
                hc0 htarg hfalse hx_all v1 v2 rest (k + 1)
                (by omega) (by omega)
                (fun i p hp => by
                  rw [show k + 1 + i = k + (i + 1) by omega]; exact hxs (i + 1) p hp) h
            · rw [c5, Bool.cond_true] at h
              injection h with hpr; subst hpr
              simp only [Bool.and_eq_true, Bool.or_eq_true, eq3_iff] at c5
              rcases c5 with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hbk0⟩
              · rw [hbk0, addEv_zero] at hbk
                rw [hck1, hck, hxk, addCarry, ← hbk]
                cases x_eval k <;> cases addCarry m0 targ flip_out c0_val x_eval k <;> rfl
              · rw [hbk0, addEv_zero] at hbk
                rw [hck1, hck, hxk, addCarry, ← hbk]
                cases x_eval k <;> cases addCarry m0 targ flip_out c0_val x_eval k <;> rfl
          · rw [c4, Bool.cond_true] at h
            injection h with hpr; subst hpr
            simp only [Bool.or_eq_true, Bool.and_eq_true, eq3_iff] at c4
            rcases c4 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rw [addEv_xor, addEv_xor, addEv_xor, hck1, hck, hbk, hxk, addCarry]
              generalize x_eval k = x1
              generalize xor (targBit targ m0 k) flip_out = b1
              generalize addCarry m0 targ flip_out c0_val x_eval k = c1v
              cases x1 <;> cases b1 <;> cases c1v <;> rfl
            · rw [addEv_xor, addEv_xor, addEv_xor, hck1, hck, hbk, hxk, addCarry]
              generalize x_eval k = x1
              generalize xor (targBit targ m0 k) flip_out = b1
              generalize addCarry m0 targ flip_out c0_val x_eval k = c1v
              cases x1 <;> cases b1 <;> cases c1v <;> rfl
        · rw [c3, Bool.cond_true] at h
          injection h with hpr; subst hpr
          simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', eq3_iff] at c3
          obtain ⟨⟨hflip0, rfl⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := c3
          · rw [addEv_one] at hxk
            simp only [nbk, nck, addEv_xor, addEv_one, hck1, hbk, hck, addCarry, ← hxk]
            generalize targBit targ m0 k = b1
            generalize addCarry m0 targ flip_out c0_val x_eval k = b2
            subst hflip0
            cases b1 <;> cases b2 <;> rfl
          · rw [addEv_one] at hxk
            simp only [nbk, nck, addEv_xor, addEv_one, hck1, hbk, hck, addCarry, ← hxk]
            generalize targBit targ m0 k = b1
            generalize addCarry m0 targ flip_out c0_val x_eval k = b2
            subst hflip0
            cases b1 <;> cases b2 <;> rfl
      · rw [c2, Bool.cond_true] at h
        injection h with hpr; subst hpr
        simp only [Bool.and_eq_true, Bool.or_eq_true, eq3_iff] at c2
        rcases c2 with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl⟩
        · rw [addEv_zero] at hxk
          rw [hck1, hck, hbk, addCarry, ← hxk, Bool.and_comm]
          exact (majBool_zero _ _).symm
        · rw [addEv_zero] at hxk
          rw [hck1, hck, hbk, addCarry, ← hxk]
          exact (majBool_zero _ _).symm
    · rw [c1, Bool.cond_true] at h
      injection h with hpr; subst hpr
      simp only [Bool.or_eq_true, Bool.and_eq_true, eq3_iff] at c1
      rcases c1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [addEv_xor, addEv_xor, addEv_xor, hck1, hck, hbk, hxk, addCarry]
        generalize x_eval k = x1
        generalize xor (targBit targ m0 k) flip_out = b1
        generalize addCarry m0 targ flip_out c0_val x_eval k = c1v
        cases x1 <;> cases b1 <;> cases c1v <;> rfl
      · rw [addEv_xor, addEv_xor, addEv_xor, hck1, hck, hbk, hxk, addCarry]
        generalize x_eval k = x1
        generalize xor (targBit targ m0 k) flip_out = b1
        generalize addCarry m0 targ flip_out c0_val x_eval k = c1v
        cases x1 <;> cases b1 <;> cases c1v <;> rfl

theorem mulLin_sound (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out c0_val : Bool)
    (falseW : List Nat)
    {x_eval : Nat → Bool} {c0_expr : Nat × Nat × Nat}
    (hc0 : addEv m0 targ flip_out c0_val x_eval c0_expr = c0_val)
    (htarg : ∀ w ∈ targ, w < 100)
    (hfalse : ∀ w : Fin 100, w.val ∈ falseW → m0 w = false)
    (xlist : List (Nat × Nat × Nat))
    (hlen : xlist.length ≤ targ.length) (hM : xlist.length ≤ 25)
    (hx_all : ∀ j, addEv m0 targ flip_out c0_val x_eval (xlist.getD j (0, 0, 0)) = x_eval j)
    (hxs : ∀ i p, xlist[i]? = some p → addEv m0 targ flip_out c0_val x_eval p = x_eval i)
    {v1 v2 pr : Nat × Nat × Nat}
    (h : mulLin targ flip_out falseW c0_expr xlist v1 v2 = some pr) :
    addEv m0 targ flip_out c0_val x_eval pr =
      (addEv m0 targ flip_out c0_val x_eval v1 && addEv m0 targ flip_out c0_val x_eval v2) := by
  unfold mulLin at h
  cases z : (eq3 v1 (0, 0, 0) || eq3 v2 (0, 0, 0))
  · rw [z, Bool.cond_false] at h
    cases o1 : eq3 v1 (1, 0, 0)
    · rw [o1, Bool.cond_false] at h
      cases o2 : eq3 v2 (1, 0, 0)
      · rw [o2, Bool.cond_false] at h
        cases s1 : eq3 v1 v2
        · rw [s1, Bool.cond_false] at h
          cases s2 : eq3 (xor3 v1 v2) (1, 0, 0)
          · rw [s2, Bool.cond_false] at h
            exact matchCarryBit_sound m0 targ flip_out c0_val falseW x_eval
              hc0 htarg hfalse hx_all v1 v2 xlist 0
              (by omega) (by omega) (fun i p hp => by simpa using hxs i p hp) h
          · rw [s2, Bool.cond_true] at h
            injection h with hpr; subst hpr
            have hxor := congrArg (addEv m0 targ flip_out c0_val x_eval) (eq3_iff.mp s2)
            rw [addEv_xor, addEv_one] at hxor
            rw [addEv_zero]
            revert hxor
            generalize addEv m0 targ flip_out c0_val x_eval v1 = b1
            generalize addEv m0 targ flip_out c0_val x_eval v2 = b2
            cases b1 <;> cases b2 <;> decide
        · rw [s1, Bool.cond_true] at h
          injection h with hpr; subst hpr
          rw [eq3_iff.mp s1, Bool.and_self]
      · rw [o2, Bool.cond_true] at h
        injection h with hpr; subst hpr
        rw [eq3_iff.mp o2, addEv_one, Bool.and_true]
    · rw [o1, Bool.cond_true] at h
      injection h with hpr; subst hpr
      rw [eq3_iff.mp o1, addEv_one, Bool.true_and]
  · rw [z, Bool.cond_true] at h
    injection h with hpr; subst hpr
    rw [addEv_zero]
    rcases Bool.or_eq_true_iff.mp z with h1 | h2
    · rw [eq3_iff.mp h1, addEv_zero]; rfl
    · rw [eq3_iff.mp h2, addEv_zero, Bool.and_false]

structure AddInv (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out c0_val : Bool)
    (x_eval : Nat → Bool) (tr : LTree) (m : Fin 100 → Bool) : Prop where
  wf : LTreeWF 7 tr
  hWire : ∀ w : Fin 100, m w = addEv m0 targ flip_out c0_val x_eval (ltGet 6 tr w.val)

theorem AddInv.update_wire {m0 : Fin 100 → Bool} {targ : List Nat} {flip_out c0_val : Bool}
    {x_eval : Nat → Bool} {tr : LTree} {m : Fin 100 → Bool}
    (hI : AddInv m0 targ flip_out c0_val x_eval tr m)
    {t : Nat} (ht : t < 100) {p : Nat × Nat × Nat} {hb : Bool}
    (hev : addEv m0 targ flip_out c0_val x_eval p = hb) :
    AddInv m0 targ flip_out c0_val x_eval (ltSet 6 tr t p) (Function.update m ⟨t, ht⟩ hb) := by
  refine ⟨ltSet_wf hI.wf _ _, fun w => ?_⟩
  by_cases hw : w = ⟨t, ht⟩
  · subst hw
    simp [Function.update_self,
      ltGet_ltSet hI.wf (by omega : t < 2 ^ 7) (by omega : t < 2 ^ 7), hev]
  · have hne : w.val ≠ t := fun e => hw (Fin.ext e)
    simp [Function.update_of_ne hw,
      ltGet_ltSet hI.wf (by omega : t < 2 ^ 7) (by omega : w.val < 2 ^ 7),
      hne, hI.hWire w]

theorem evalQuadAddOpt_sound {m0 : Fin 100 → Bool} {targ : List Nat} {flip_out c0_val : Bool}
    {falseW : List Nat} {c0_expr : Nat × Nat × Nat} {x_eval : Nat → Bool}
    (hc0 : addEv m0 targ flip_out c0_val x_eval c0_expr = c0_val)
    (htarg : ∀ w ∈ targ, w < 100)
    (hfalse : ∀ w : Fin 100, w.val ∈ falseW → m0 w = false)
    {xlist : List (Nat × Nat × Nat)} (hlen : xlist.length ≤ targ.length) (hM : xlist.length ≤ 25)
    (hx_all : ∀ j, addEv m0 targ flip_out c0_val x_eval (xlist.getD j (0, 0, 0)) = x_eval j)
    (hxs : ∀ i p, xlist[i]? = some p → addEv m0 targ flip_out c0_val x_eval p = x_eval i)
    {tr : LTree} {m : Fin 100 → Bool} (hI : AddInv m0 targ flip_out c0_val x_eval tr m) (t : Nat) :
    ∀ (qs : List (Nat × Nat)) {vq : Nat × Nat × Nat},
      evalQuadAddOpt targ flip_out falseW c0_expr xlist tr t qs = some vq →
      (∀ p ∈ qs, p.1 < 100 ∧ p.2 < 100 ∧ p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧
      addEv m0 targ flip_out c0_val x_eval vq = evalQuadBool102 m qs
  | [], vq, h => by
    injection h with hvq; subst hvq
    exact ⟨fun _ hp => (by cases hp), addEv_zero m0 targ flip_out c0_val x_eval⟩
  | (a, b) :: rest, vq, h => by
    dsimp only [evalQuadAddOpt] at h
    cases hc : (Nat.blt a 100 && Nat.blt b 100 &&
      (!Nat.beq a b) && (!Nat.beq a t) && (!Nat.beq b t))
    · rw [hc, Bool.cond_false] at h; cases h
    rw [hc, Bool.cond_true] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, beq_false_iff] at hc
    obtain ⟨⟨⟨⟨ha102, hb102⟩, hab⟩, hat⟩, hbt⟩ := hc
    cases hm : mulLin targ flip_out falseW c0_expr xlist (ltGet 6 tr a) (ltGet 6 tr b) with
    | none => rw [hm] at h; cases h
    | some pr =>
      rw [hm] at h; dsimp only at h
      cases hrest : evalQuadAddOpt targ flip_out falseW c0_expr xlist tr t rest with
      | none => rw [hrest] at h; cases h
      | some acc =>
        rw [hrest] at h; dsimp only at h
        injection h with hvq; subst hvq
        obtain ⟨hrest_v, hrest_ev⟩ :=
          evalQuadAddOpt_sound hc0 htarg hfalse hlen hM hx_all hxs hI t rest hrest
        have hpr_ev : addEv m0 targ flip_out c0_val x_eval pr = (m ⟨a, ha102⟩ && m ⟨b, hb102⟩) := by
          rw [hI.hWire ⟨a, ha102⟩, hI.hWire ⟨b, hb102⟩]
          exact mulLin_sound m0 targ flip_out c0_val falseW hc0 htarg hfalse
            xlist hlen hM hx_all hxs hm
        refine ⟨fun p hp => ?_, ?_⟩
        · rcases List.mem_cons.mp hp with rfl | hmem
          · exact ⟨ha102, hb102, hab, hat, hbt⟩
          · exact hrest_v p hmem
        · dsimp only [evalQuadBool102]
          rw [dite_eq_left ⟨ha102, hb102⟩, addEv_xor, hpr_ev, hrest_ev]

theorem evalLinAddOpt_sound {m0 : Fin 100 → Bool} {targ : List Nat} {flip_out c0_val : Bool}
    {x_eval : Nat → Bool} {tr : LTree} {m : Fin 100 → Bool}
    (hI : AddInv m0 targ flip_out c0_val x_eval tr m) (t : Nat) :
    ∀ (ls : List Nat) {vl : Nat × Nat × Nat},
      evalLinAddOpt tr t ls = some vl →
      (∀ c ∈ ls, c < 100 ∧ c ≠ t) ∧
      addEv m0 targ flip_out c0_val x_eval vl = evalLinBool102 m ls
  | [], vl, h => by
    injection h with hvl; subst hvl
    exact ⟨fun _ hc => (by cases hc), addEv_zero m0 targ flip_out c0_val x_eval⟩
  | c :: rest, vl, h => by
    dsimp only [evalLinAddOpt] at h
    cases hc : (Nat.blt c 100 && (!Nat.beq c t))
    · rw [hc, Bool.cond_false] at h; cases h
    rw [hc, Bool.cond_true] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, beq_false_iff] at hc
    obtain ⟨hc102, hct⟩ := hc
    cases hrest : evalLinAddOpt tr t rest with
    | none => rw [hrest] at h; cases h
    | some acc =>
      rw [hrest] at h; dsimp only at h
      injection h with hvl; subst hvl
      obtain ⟨hrest_v, hrest_ev⟩ := evalLinAddOpt_sound hI t rest hrest
      refine ⟨fun x hx => ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hmem
        · exact ⟨hc102, hct⟩
        · exact hrest_v x hmem
      · dsimp only [evalLinBool102]
        rw [dite_eq_left hc102, addEv_xor, ← hI.hWire ⟨c, hc102⟩, hrest_ev]

theorem stepAddOpt_sound {m0 : Fin 100 → Bool} {targ : List Nat} {flip_out c0_val : Bool}
    {falseW : List Nat} {c0_expr : Nat × Nat × Nat} {x_eval : Nat → Bool}
    (hc0 : addEv m0 targ flip_out c0_val x_eval c0_expr = c0_val)
    (htarg : ∀ w ∈ targ, w < 100)
    (hfalse : ∀ w : Fin 100, w.val ∈ falseW → m0 w = false)
    {xlist : List (Nat × Nat × Nat)} (hlen : xlist.length ≤ targ.length) (hM : xlist.length ≤ 25)
    (hx_all : ∀ j, addEv m0 targ flip_out c0_val x_eval (xlist.getD j (0, 0, 0)) = x_eval j)
    (hxs : ∀ i p, xlist[i]? = some p → addEv m0 targ flip_out c0_val x_eval p = x_eval i)
    {tr tr' : LTree} {m : Fin 100 → Bool}
    (hI : AddInv m0 targ flip_out c0_val x_eval tr m)
    {op : Op102}
    (hok : stepAddOpt targ flip_out falseW c0_expr xlist tr op = some tr') :
    ∃ m', execOp102 m op = some m' ∧ AddInv m0 targ flip_out c0_val x_eval tr' m' := by
  cases op with
  | x q =>
    dsimp only [stepAddOpt] at hok
    cases hq : Nat.blt q 100
    · rw [hq, Bool.cond_false] at hok; cases hok
    rw [hq, Bool.cond_true] at hok
    injection hok with htr'; subst htr'
    have hqlt : q < 100 := Nat.blt_eq.mp hq
    have hev :
        addEv m0 targ flip_out c0_val x_eval (xor3 (ltGet 6 tr q) (1, 0, 0)) = !m ⟨q, hqlt⟩ := by
      rw [addEv_xor, addEv_one, ← hI.hWire ⟨q, hqlt⟩]
      cases m ⟨q, hqlt⟩ <;> rfl
    exact ⟨_, by dsimp only [execOp102]; rw [dite_eq_left hqlt], hI.update_wire hqlt hev⟩
  | cx c t =>
    dsimp only [stepAddOpt] at hok
    cases hc : (Nat.blt c 100 && Nat.blt t 100 && (!Nat.beq c t))
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    injection hok with htr'; subst htr'
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, beq_false_iff] at hc
    obtain ⟨⟨hclt, htlt⟩, hct⟩ := hc
    have hev : addEv m0 targ flip_out c0_val x_eval (xor3 (ltGet 6 tr t) (ltGet 6 tr c)) =
        xor (m ⟨t, htlt⟩) (m ⟨c, hclt⟩) := by
      rw [addEv_xor, ← hI.hWire ⟨t, htlt⟩, ← hI.hWire ⟨c, hclt⟩]
    exact ⟨_, by dsimp only [execOp102]; rw [dite_eq_left ⟨hclt, htlt, hct⟩],
      hI.update_wire htlt hev⟩
  | and4t c1 c2 t =>
    dsimp only [stepAddOpt] at hok
    cases hc : (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
                (!Nat.beq c1 c2) && (!Nat.beq c1 t) && (!Nat.beq c2 t) &&
                eq3 (ltGet 6 tr t) (0, 0, 0))
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, beq_false_iff, eq3_iff] at hc
    obtain ⟨⟨⟨⟨⟨⟨hc1lt, hc2lt⟩, htlt⟩, hc12⟩, hc1t⟩, hc2t⟩, ht0⟩ := hc
    have hmt : m ⟨t, htlt⟩ = false := by rw [hI.hWire ⟨t, htlt⟩, ht0, addEv_zero]
    cases hm : mulLin targ flip_out falseW c0_expr xlist (ltGet 6 tr c1) (ltGet 6 tr c2) with
    | none => rw [hm] at hok; cases hok
    | some pr =>
      rw [hm] at hok
      dsimp only at hok
      injection hok with htr'; subst htr'
      have hev : addEv m0 targ flip_out c0_val x_eval pr = (m ⟨c1, hc1lt⟩ && m ⟨c2, hc2lt⟩) := by
        rw [hI.hWire ⟨c1, hc1lt⟩, hI.hWire ⟨c2, hc2lt⟩]
        exact mulLin_sound m0 targ flip_out c0_val falseW hc0 htarg hfalse
          xlist hlen hM hx_all hxs hm
      exact ⟨_, (by
          dsimp only [execOp102]
          rw [dite_eq_left ⟨hc1lt, hc2lt, htlt, hc12, hc1t, hc2t⟩, ite_eq_left hmt]),
        hI.update_wire htlt hev⟩
  | rccx0 _ _ _ => cases hok
  | rccx1 _ _ _ => cases hok
  | unand c1 c2 t =>
    dsimp only [stepAddOpt] at hok
    cases hc : (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
                (!Nat.beq c1 c2) && (!Nat.beq c1 t) && (!Nat.beq c2 t))
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, beq_false_iff] at hc
    obtain ⟨⟨⟨⟨⟨hc1lt, hc2lt⟩, htlt⟩, hc12⟩, hc1t⟩, hc2t⟩ := hc
    cases hm : mulLin targ flip_out falseW c0_expr xlist (ltGet 6 tr c1) (ltGet 6 tr c2) with
    | none => rw [hm] at hok; cases hok
    | some pr =>
      rw [hm] at hok
      dsimp only at hok
      cases hteq : eq3 (ltGet 6 tr t) pr
      · rw [hteq, Bool.cond_false] at hok; cases hok
      rw [hteq, Bool.cond_true] at hok
      injection hok with htr'; subst htr'
      have hmt : m ⟨t, htlt⟩ = (m ⟨c1, hc1lt⟩ && m ⟨c2, hc2lt⟩) := by
        rw [hI.hWire ⟨t, htlt⟩, eq3_iff.mp hteq, hI.hWire ⟨c1, hc1lt⟩, hI.hWire ⟨c2, hc2lt⟩]
        exact mulLin_sound m0 targ flip_out c0_val falseW hc0 htarg hfalse
          xlist hlen hM hx_all hxs hm
      exact ⟨_, (by
          dsimp only [execOp102]
          rw [dite_eq_left ⟨hc1lt, hc2lt, htlt, hc12, hc1t, hc2t⟩, ite_eq_left hmt]),
        hI.update_wire htlt (addEv_zero m0 targ flip_out c0_val x_eval)⟩
  | unquad qs ls t =>
    dsimp only [stepAddOpt] at hok
    cases htb : Nat.blt t 100
    · rw [htb, Bool.cond_false] at hok; cases hok
    rw [htb, Bool.cond_true] at hok
    have htlt : t < 100 := Nat.blt_eq.mp htb
    cases hq : evalQuadAddOpt targ flip_out falseW c0_expr xlist tr t qs with
    | none => rw [hq] at hok; cases hok
    | some vq =>
      rw [hq] at hok; dsimp only at hok
      cases hl : evalLinAddOpt tr t ls with
      | none => rw [hl] at hok; cases hok
      | some vl =>
        rw [hl] at hok; dsimp only at hok
        cases hteq : eq3 (ltGet 6 tr t) (xor3 vq vl)
        · rw [hteq, Bool.cond_false] at hok; cases hok
        rw [hteq, Bool.cond_true] at hok
        injection hok with htr'; subst htr'
        obtain ⟨hq_v, hq_ev⟩ := evalQuadAddOpt_sound hc0 htarg hfalse hlen hM hx_all hxs hI t qs hq
        obtain ⟨hl_v, hl_ev⟩ := evalLinAddOpt_sound hI t ls hl
        have hval : validUnquad102 qs ls t := ⟨hq_v, hl_v, htlt⟩
        have hmt : m ⟨t, htlt⟩ = evalUnquad102 m qs ls := by
          rw [hI.hWire ⟨t, htlt⟩, eq3_iff.mp hteq, addEv_xor, hq_ev, hl_ev]; rfl
        exact ⟨_, by dsimp only [execOp102]; rw [dite_eq_left hval, ite_eq_left hmt],
          hI.update_wire htlt (addEv_zero m0 targ flip_out c0_val x_eval)⟩
  | z _ => cases hok
  | cz _ => cases hok
  | hGadget _ _ _ _ _ => cases hok

theorem runAddListOpt_sound {m0 : Fin 100 → Bool} {targ : List Nat} {flip_out c0_val : Bool}
    {falseW : List Nat} {c0_expr : Nat × Nat × Nat} {x_eval : Nat → Bool}
    (hc0 : addEv m0 targ flip_out c0_val x_eval c0_expr = c0_val)
    (htarg : ∀ w ∈ targ, w < 100)
    (hfalse : ∀ w : Fin 100, w.val ∈ falseW → m0 w = false)
    {xlist : List (Nat × Nat × Nat)} (hlen : xlist.length ≤ targ.length) (hM : xlist.length ≤ 25)
    (hx_all : ∀ j, addEv m0 targ flip_out c0_val x_eval (xlist.getD j (0, 0, 0)) = x_eval j)
    (hxs : ∀ i p, xlist[i]? = some p → addEv m0 targ flip_out c0_val x_eval p = x_eval i) :
    ∀ (ops : List Op102) {tr trf : LTree} {m : Fin 100 → Bool},
      AddInv m0 targ flip_out c0_val x_eval tr m →
      runAddListOpt targ flip_out falseW c0_expr xlist ops tr = some trf →
      ∃ mf, execList102 ops m = some mf ∧ AddInv m0 targ flip_out c0_val x_eval trf mf
  | [], _, _, m, hI, hok => by
    injection hok with htrf; subst htrf
    exact ⟨m, rfl, hI⟩
  | op :: ops, tr, trf, m, hI, hok => by
    dsimp only [runAddListOpt] at hok
    cases hs : stepAddOpt targ flip_out falseW c0_expr xlist tr op with
    | none => rw [hs] at hok; cases hok
    | some tr1 =>
      rw [hs] at hok
      obtain ⟨m1, hex1, hI1⟩ := stepAddOpt_sound hc0 htarg hfalse hlen hM hx_all hxs hI hs
      obtain ⟨mf, hex2, hIf⟩ := runAddListOpt_sound hc0 htarg hfalse hlen hM hx_all hxs ops hI1 hok
      exact ⟨mf, by simp [execList102, hex1, hex2], hIf⟩

def sumBits : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | M + 1, g => sumBits M g + 2 ^ M * (g M).toNat

theorem sumBits_zero (g : Nat → Bool) : sumBits 0 g = 0 := rfl

theorem sumBits_succ (M : Nat) (g : Nat → Bool) :
    sumBits (M + 1) g = sumBits M g + 2 ^ M * (g M).toNat := rfl

theorem sumBits_congr {M : Nat} {g1 g2 : Nat → Bool} (h : ∀ k < M, g1 k = g2 k) :
    sumBits M g1 = sumBits M g2 := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [sumBits_succ, sumBits_succ, ih (fun k hk => h k (by omega)), h M (by omega)]

theorem sumBits_lt : ∀ (M : Nat) (g : Nat → Bool), sumBits M g < 2 ^ M
  | 0, _ => by simp [sumBits]
  | M + 1, g => by
    rw [sumBits_succ]
    have h1 := sumBits_lt M g
    have hpow : 2 ^ (M + 1) = 2 * 2 ^ M := by ring
    cases g M <;> simp [Bool.toNat] <;> omega

theorem sumBits_not : ∀ (M : Nat) (g : Nat → Bool),
    sumBits M (fun k => !(g k)) + sumBits M g = 2 ^ M - 1
  | 0, _ => by simp [sumBits]
  | M + 1, g => by
    rw [sumBits_succ, sumBits_succ]
    have ih := sumBits_not M g
    have hlt := sumBits_lt M g
    have hpow : 2 ^ (M + 1) = 2 * 2 ^ M := by ring
    have hb : (!(g M)).toNat + (g M).toNat = 1 := by cases g M <;> decide
    calc (sumBits M fun k => !g k) + 2 ^ M * (!g M).toNat + (sumBits M g + 2 ^ M * (g M).toNat)
        = ((sumBits M fun k => !g k) + sumBits M g) +
            2 ^ M * ((!g M).toNat + (g M).toNat) := by ring
      _ = (2 ^ M - 1) + 2 ^ M * 1 := by rw [ih, hb]
      _ = 2 ^ (M + 1) - 1 := by omega

theorem sumBits_split {A B : Nat} (g : Nat → Bool) :
    sumBits (A + B) g = sumBits A g + 2 ^ A * sumBits B (fun k => g (A + k)) := by
  induction B with
  | zero => simp [sumBits]
  | succ B ih =>
    rw [Nat.add_succ, sumBits_succ, ih, sumBits_succ, pow_add]
    ring

theorem evalBits_eq_sumBits (g : Nat → Bool) (start : Nat) :
    ∀ n, evalBits g start n = sumBits n (fun k => g (start + k))
  | 0 => rfl
  | n + 1 => by
    simp only [evalBits, sumBits, evalBits_eq_sumBits g start n, shiftLeft_eq_mul_pow]
    cases g (start + n) <;> simp [Bool.toNat, mul_comm]

theorem evalBits_lt (g : Nat → Bool) (start len : Nat) :
    evalBits g start len < 2 ^ len := by
  rw [evalBits_eq_sumBits]
  exact sumBits_lt len _

theorem evalBits_split (g : Nat → Bool) (start a b : Nat) :
    evalBits g start (a + b) =
      evalBits g start a + 2 ^ a * evalBits g (start + a) b := by
  rw [evalBits_eq_sumBits, evalBits_eq_sumBits, evalBits_eq_sumBits, sumBits_split]
  congr 2
  refine sumBits_congr fun k _ => ?_
  rw [Nat.add_assoc]

theorem full_adder_bit (x b c : Bool) :
    (xor (xor b x) c).toNat + 2 * (majBool x b c).toNat =
      b.toNat + x.toNat + c.toNat := by
  cases x <;> cases b <;> cases c <;> decide

def addCarryGen (bBit x_eval : Nat → Bool) (c0 : Bool) : Nat → Bool
  | 0 => c0
  | k + 1 => majBool (x_eval k) (bBit k) (addCarryGen bBit x_eval c0 k)

theorem addCarryGen_congr {b1 b2 x_eval : Nat → Bool} {c0 : Bool} :
    ∀ k, (∀ j < k, b1 j = b2 j) → addCarryGen b1 x_eval c0 k = addCarryGen b2 x_eval c0 k
  | 0, _ => rfl
  | k + 1, h => by
    simp [addCarryGen, h k (by omega), addCarryGen_congr k (fun j hj => h j (by omega))]

theorem sumBits_addCarryGen (c0 : Bool) : ∀ (M : Nat) (bBit x_eval : Nat → Bool),
    sumBits M (fun k => xor (xor (bBit k) (x_eval k)) (addCarryGen bBit x_eval c0 k)) +
      2 ^ M * (addCarryGen bBit x_eval c0 M).toNat =
      sumBits M bBit + sumBits M x_eval + c0.toNat
  | 0, _, _ => by simp [sumBits, addCarryGen]
  | M + 1, bBit, x_eval => by
    rw [sumBits_succ, sumBits_succ, sumBits_succ, addCarryGen]
    have ih := sumBits_addCarryGen c0 M bBit x_eval
    have hfa := full_adder_bit (x_eval M) (bBit M) (addCarryGen bBit x_eval c0 M)
    have hpow : 2 ^ (M + 1) = 2 * 2 ^ M := by ring
    calc (sumBits M fun k => xor (xor (bBit k) (x_eval k)) (addCarryGen bBit x_eval c0 k)) +
          2 ^ M * (xor (xor (bBit M) (x_eval M)) (addCarryGen bBit x_eval c0 M)).toNat +
          2 ^ (M + 1) * (majBool (x_eval M) (bBit M) (addCarryGen bBit x_eval c0 M)).toNat
        = (sumBits M fun k => xor (xor (bBit k) (x_eval k)) (addCarryGen bBit x_eval c0 k)) +
          2 ^ M * ((xor (xor (bBit M) (x_eval M)) (addCarryGen bBit x_eval c0 M)).toNat +
            2 * (majBool (x_eval M) (bBit M) (addCarryGen bBit x_eval c0 M)).toNat) := by
          rw [hpow]; ring
      _ = (sumBits M fun k => xor (xor (bBit k) (x_eval k)) (addCarryGen bBit x_eval c0 k)) +
          2 ^ M * ((bBit M).toNat + (x_eval M).toNat + (addCarryGen bBit x_eval c0 M).toNat) := by
          rw [hfa]
      _ = (sumBits M bBit + sumBits M x_eval + c0.toNat) +
          2 ^ M * ((bBit M).toNat + (x_eval M).toNat) := by
          linarith
      _ = sumBits M bBit + 2 ^ M * (bBit M).toNat +
          (sumBits M x_eval + 2 ^ M * (x_eval M).toNat) + c0.toNat := by
          ring

theorem sumBits_subCarryGen (c0 : Bool) (M : Nat) (mBit x_eval : Nat → Bool) :
    sumBits M (fun k => !(xor (xor (!(mBit k)) (x_eval k))
        (addCarryGen (fun j => !(mBit j)) x_eval c0 k))) +
      (sumBits M x_eval + c0.toNat) =
      sumBits M mBit + 2 ^ M * (addCarryGen (fun j => !(mBit j)) x_eval c0 M).toNat := by
  set bBit := fun j => !(mBit j)
  set sBit := fun k => xor (xor (bBit k) (x_eval k)) (addCarryGen bBit x_eval c0 k)
  have hpos := sumBits_addCarryGen c0 M bBit x_eval
  have hnot_m := sumBits_not M mBit
  have hnot_s := sumBits_not M sBit
  linarith

def ltreeTargVal (targ : List Nat) (m : Fin 100 → Bool) : Nat :=
  sumBits targ.length (targBit targ m)

theorem ltreeTargVal_lt (targ : List Nat) (m : Fin 100 → Bool) :
    ltreeTargVal targ m < 2 ^ targ.length :=
  sumBits_lt targ.length _

theorem rangeList_getElem? : ∀ {sout M k : Nat}, k < M → (rangeList sout M)[k]? = some (sout + k)
  | _, 0, _, hk => absurd hk (Nat.not_lt_zero _)
  | sout, M + 1, 0, _ => by simp [rangeList]
  | sout, M + 1, k + 1, hk => by
    simp only [rangeList, List.getElem?_cons_succ]
    rw [rangeList_getElem? (by omega : k < M)]
    congr 1; omega

def sliceVal (sout M : Nat) (m : Fin 100 → Bool) : Nat :=
  sumBits M (fun k => if h : sout + k < 100 then m ⟨sout + k, h⟩ else false)

theorem ltreeTargVal_rangeList (sout M : Nat) (m : Fin 100 → Bool) :
    ltreeTargVal (rangeList sout M) m = sliceVal sout M m := by
  unfold ltreeTargVal sliceVal
  rw [rangeList_length]
  refine sumBits_congr fun k hk => ?_
  unfold targBit
  rw [rangeList_getElem? hk]

def outVal102 (m : Fin 100 → Bool) : Nat :=
  sliceVal 0 25 m

theorem outVal102_lt (m : Fin 100 → Bool) : outVal102 m < 33554432 :=
  sumBits_lt 25 _

theorem outVal102_congr {m1 m2 : Fin 100 → Bool} (h : ∀ j : Fin 100, j.val < 25 → m1 j = m2 j) :
    outVal102 m1 = outVal102 m2 := by
  unfold outVal102 sliceVal
  refine sumBits_congr fun k hk => ?_
  have hk102 : k < 100 := by omega
  simp only [Nat.zero_add, dite_eq_left hk102, h ⟨k, hk102⟩ hk]

def checkNonOutRestored (targ : List Nat) (tr0 trf : LTree) : Nat → Bool
  | 0 => true
  | w + 1 =>
      let same := cond (targ.elem w) true (eq3 (ltGet 6 trf w) (ltGet 6 tr0 w))
      cond same (checkNonOutRestored targ tr0 trf w) false

theorem checkNonOutRestored_sound (targ : List Nat) (tr0 trf : LTree) :
    ∀ n, checkNonOutRestored targ tr0 trf n = true →
      ∀ w < n, w ∉ targ → ltGet 6 trf w = ltGet 6 tr0 w
  | 0, _, _, hw, _ => absurd hw (Nat.not_lt_zero _)
  | n + 1, hok, w, hw, hnot => by
    dsimp only [checkNonOutRestored] at hok
    set same := cond (targ.elem n) true (eq3 (ltGet 6 trf n) (ltGet 6 tr0 n))
    cases hs : same
    · rw [hs, Bool.cond_false] at hok; cases hok
    rw [hs, Bool.cond_true] at hok
    by_cases hwn : w = n
    · subst hwn
      have hb : targ.elem w = false := by
        cases he : targ.elem w
        · rfl
        · exact absurd (List.mem_of_elem_eq_true he) hnot
      dsimp only [same] at hs
      rw [hb, Bool.cond_false] at hs
      exact eq3_iff.mp hs
    · exact checkNonOutRestored_sound targ tr0 trf n hok w (by omega) hnot

def checkOutBits (targ : List Nat) (flip_out is_noop : Bool) (falseW : List Nat)
    (c0_expr : Nat × Nat × Nat) (xlist : List (Nat × Nat × Nat)) (tr0 trf : LTree) :
    List (Nat × Nat × Nat) → Nat → Bool
  | [], _ => true
  | xk :: rest, k =>
      match targ[k]? with
      | none => false
      | some tw =>
          let p0 := ltGet 6 tr0 tw
          let ck := cExpr targ flip_out falseW c0_expr xlist k
          let exp := cond is_noop p0 (xor3 (xor3 p0 xk) ck)
          cond (eq3 (ltGet 6 trf tw) exp)
            (checkOutBits targ flip_out is_noop falseW c0_expr xlist tr0 trf rest (k + 1))
            false

theorem addCarry_eq_gen (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out c0_val : Bool)
    (x_eval : Nat → Bool) :
    ∀ k, addCarry m0 targ flip_out c0_val x_eval k =
      addCarryGen (fun j => xor (targBit targ m0 j) flip_out) x_eval c0_val k
  | 0 => rfl
  | k + 1 => by simp [addCarry, addCarryGen, addCarry_eq_gen m0 targ flip_out c0_val x_eval k]

theorem checkOutBits_sound {m0 mf : Fin 100 → Bool} {targ : List Nat}
    {flip_out is_noop c0_val : Bool} {falseW : List Nat} {c0_expr : Nat × Nat × Nat}
    {xlist : List (Nat × Nat × Nat)} {x_eval : Nat → Bool}
    (hc0 : addEv m0 targ flip_out c0_val x_eval c0_expr = c0_val)
    (htarg : ∀ w ∈ targ, w < 100)
    (hfalse : ∀ w : Fin 100, w.val ∈ falseW → m0 w = false)
    (hx_all : ∀ j, addEv m0 targ flip_out c0_val x_eval (xlist.getD j (0, 0, 0)) = x_eval j)
    {tr0 trf : LTree}
    (hI0 : AddInv m0 targ flip_out c0_val x_eval tr0 m0)
    (hIf : AddInv m0 targ flip_out c0_val x_eval trf mf) :
    ∀ (xs : List (Nat × Nat × Nat)) (k : Nat)
      (_hlen : k + xs.length ≤ targ.length) (_hM : k + xs.length ≤ 25),
      (∀ i p, xs[i]? = some p → addEv m0 targ flip_out c0_val x_eval p = x_eval (k + i)) →
      checkOutBits targ flip_out is_noop falseW c0_expr xlist tr0 trf xs k = true →
      ∀ i (_hi : i < xs.length),
        targBit targ mf (k + i) =
          if is_noop then targBit targ m0 (k + i)
          else xor (xor (targBit targ m0 (k + i)) (x_eval (k + i)))
            (addCarryGen (fun j => xor (targBit targ m0 j) flip_out) x_eval c0_val (k + i))
  | [], _, _, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | xk :: rest, k, hlen, hM, hxs, hok, i, hi => by
    dsimp only [List.length_cons] at hlen hM hi
    dsimp only [checkOutBits] at hok
    have hk_lt : k < targ.length := by omega
    have hget : targ[k]? = some targ[k] := List.getElem?_eq_getElem hk_lt
    have htw_lt : targ[k] < 100 := htarg targ[k] (List.getElem_mem hk_lt)
    rw [hget] at hok
    dsimp only at hok
    set tw := targ[k]
    set p0 := ltGet 6 tr0 tw
    set ck := cExpr targ flip_out falseW c0_expr xlist k
    set exp := cond is_noop p0 (xor3 (xor3 p0 xk) ck)
    cases hc : eq3 (ltGet 6 trf tw) exp
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    cases i with
    | zero =>
      simp only [Nat.add_zero]
      have htb_mf : targBit targ mf k = mf ⟨tw, htw_lt⟩ := by
        unfold targBit; rw [hget]; dsimp only; rw [dite_eq_left htw_lt]
      have htb_m0 : targBit targ m0 k = m0 ⟨tw, htw_lt⟩ := by
        unfold targBit; rw [hget]; dsimp only; rw [dite_eq_left htw_lt]
      rw [htb_mf, htb_m0]
      have hmf_k : mf ⟨tw, htw_lt⟩ = addEv m0 targ flip_out c0_val x_eval exp := by
        have h1 := hIf.hWire ⟨tw, htw_lt⟩
        rw [h1, eq3_iff.mp hc]
      have hm0_k : m0 ⟨tw, htw_lt⟩ = addEv m0 targ flip_out c0_val x_eval p0 :=
        hI0.hWire ⟨tw, htw_lt⟩
      cases is_noop
      · dsimp only [exp, cond] at hmf_k
        have hxk : addEv m0 targ flip_out c0_val x_eval xk = x_eval k := by
          simpa using hxs 0 xk rfl
        have hck : addEv m0 targ flip_out c0_val x_eval ck =
            addCarryGen (fun j => xor (targBit targ m0 j) flip_out) x_eval c0_val k := by
          rw [addEv_cExpr m0 targ flip_out c0_val falseW x_eval hc0 htarg hfalse hx_all
                (by omega : k ≤ 25),
              addCarry_eq_gen]
        rw [addEv_xor, addEv_xor, ← hm0_k, hxk, hck] at hmf_k
        simpa using hmf_k
      · dsimp only [exp, cond] at hmf_k
        simpa [← hm0_k] using hmf_k
    | succ i =>
      have ih :=
        checkOutBits_sound hc0 htarg hfalse hx_all hI0 hIf rest (k + 1) (by omega) (by omega)
        (fun j p hp => by rw [show k + 1 + j = k + (j + 1) by omega]; exact hxs (j + 1) p hp)
        hok i (by omega)
      simpa [show k + 1 + i = k + (i + 1) by omega] using ih

def checkTreeWires (tr : LTree) (trueW falseW : List Nat) : Nat → Bool
  | 0 => true
  | w + 1 =>
      let exp := if trueW.elem w then (1, 0, 0) else if falseW.elem w then (0, 0, 0) else idExpr w
      cond (eq3 (ltGet 6 tr w) exp) (checkTreeWires tr trueW falseW w) false

theorem checkTreeWires_sound (tr : LTree) (trueW falseW : List Nat) :
    ∀ n, checkTreeWires tr trueW falseW n = true →
      ∀ w < n, ltGet 6 tr w =
        if trueW.elem w then (1, 0, 0) else if falseW.elem w then (0, 0, 0) else idExpr w
  | 0, _, _, hw => absurd hw (Nat.not_lt_zero _)
  | n + 1, hok, w, hw => by
    dsimp only [checkTreeWires] at hok
    set exp := if trueW.elem n then (1, 0, 0) else if falseW.elem n then (0, 0, 0) else idExpr n
    cases hc : eq3 (ltGet 6 tr n) exp
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    by_cases hwn : w = n
    · subst hwn; exact eq3_iff.mp hc
    · exact checkTreeWires_sound tr trueW falseW n hok w (by omega)

theorem AddInv_of_treeSpec {m0 : Fin 100 → Bool} {targ : List Nat} {flip_out c0_val : Bool}
    {x_eval : Nat → Bool} {tr0 : LTree} {trueW falseW : List Nat}
    (hwf : checkLTreeWF 7 tr0 = true)
    (htw : checkTreeWires tr0 trueW falseW 100 = true)
    (htrue : ∀ w : Fin 100, w.val ∈ trueW → m0 w = true)
    (hfalse : ∀ w : Fin 100, w.val ∈ falseW → m0 w = false) :
    AddInv m0 targ flip_out c0_val x_eval tr0 m0 := by
  refine ⟨checkLTreeWF_sound 7 tr0 hwf, fun w => ?_⟩
  have h := checkTreeWires_sound tr0 trueW falseW 100 htw w.val w.isLt
  rw [h]
  by_cases h1 : trueW.elem w.val = true
  · simp only [h1, ↓reduceIte, addEv_one]
    exact htrue w (List.mem_of_elem_eq_true h1)
  · simp only [Bool.not_eq_true] at h1
    rw [h1, ite_eq_right Bool.false_ne_true]
    by_cases h2 : falseW.elem w.val = true
    · simp only [h2, ↓reduceIte, addEv_zero]
      exact hfalse w (List.mem_of_elem_eq_true h2)
    · simp only [Bool.not_eq_true] at h2
      rw [h2, ite_eq_right Bool.false_ne_true, addEv_idExpr]

def mkLTreeAux (f : Nat → Nat × Nat × Nat) : Nat → Nat → LTree
  | 0, base =>
      let p := f base
      .leaf p.1 p.2.1 p.2.2
  | d + 1, base =>
      let half := Nat.shiftLeft 1 d
      .node (mkLTreeAux f d base) (mkLTreeAux f d (base + half))

def mkLTree0 (trueW falseW : List Nat) : LTree :=
  mkLTreeAux (fun w =>
    if Nat.blt w 100 then
      if trueW.elem w then (1, 0, 0) else if falseW.elem w then (0, 0, 0) else idExpr w
    else (0, 0, 0)) 7 0

inductive XWire : Type where
  | zero
  | one
  | wire (w : Nat) (flip : Bool)
  deriving Repr, DecidableEq

def wireExpr : XWire → (Nat × Nat × Nat)
  | .zero => (0, 0, 0)
  | .one => (1, 0, 0)
  | .wire w flip => xor3 (idExpr w) (if flip then (1, 0, 0) else (0, 0, 0))

def evalXWire (m0 : Fin 100 → Bool) : XWire → Bool
  | .zero => false
  | .one => true
  | .wire w flip => if h : w < 100 then xor (m0 ⟨w, h⟩) flip else false

def evalXWires (m0 : Fin 100 → Bool) (xwires : List XWire) (i : Nat) : Bool :=
  match xwires[i]? with
  | some xw => evalXWire m0 xw
  | none => false

def xwireValid : XWire → Prop
  | .zero => True
  | .one => True
  | .wire w _ => w < 100

theorem addEv_wireExpr (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out c0_val : Bool)
    (x_eval : Nat → Bool) (xw : XWire)
    (hw_lt : xwireValid xw) :
    addEv m0 targ flip_out c0_val x_eval (wireExpr xw) = evalXWire m0 xw := by
  cases xw with
  | zero => simp [wireExpr, evalXWire, addEv_zero]
  | one => simp [wireExpr, evalXWire, addEv_one]
  | wire w flip =>
    dsimp only [xwireValid] at hw_lt
    dsimp only [wireExpr, evalXWire]
    rw [dite_eq_left hw_lt, addEv_xor, addEv_idExpr m0 targ flip_out c0_val x_eval ⟨w, hw_lt⟩]
    cases flip <;> simp [addEv_zero, addEv_one]

theorem hxs_of_wireExpr (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out c0_val : Bool)
    (xwires : List XWire)
    (hw_lt : ∀ xw ∈ xwires, xwireValid xw) :
    ∀ i p, (xwires.map wireExpr)[i]? = some p →
      addEv m0 targ flip_out c0_val (evalXWires m0 xwires) p = evalXWires m0 xwires i := by
  intro i p hp
  rw [List.getElem?_map] at hp
  unfold evalXWires
  cases hx : xwires[i]? with
  | none => rw [hx] at hp; cases hp
  | some xw =>
    rw [hx] at hp
    injection hp with hp'; subst hp'
    exact addEv_wireExpr m0 targ flip_out c0_val _ xw (hw_lt xw (List.mem_of_getElem? hx))

theorem hx_all_of_wireExpr (m0 : Fin 100 → Bool) (targ : List Nat) (flip_out c0_val : Bool)
    (xwires : List XWire)
    (hw_lt : ∀ xw ∈ xwires, xwireValid xw) :
    ∀ j, addEv m0 targ flip_out c0_val (evalXWires m0 xwires)
        ((xwires.map wireExpr).getD j (0, 0, 0)) =
      evalXWires m0 xwires j := by
  intro j
  unfold List.getD evalXWires
  rw [List.getElem?_map]
  cases hx : xwires[j]? with
  | none => simp [addEv_zero]
  | some xw =>
    dsimp only [Option.getD]
    exact addEv_wireExpr m0 targ flip_out c0_val _ xw (hw_lt xw (List.mem_of_getElem? hx))

def checkXWire : XWire → Bool
  | .zero => true
  | .one => true
  | .wire w _ => Nat.blt w 100

theorem checkXWire_sound (xw : XWire) (h : checkXWire xw = true) :
    xwireValid xw := by
  cases xw with
  | zero => trivial
  | one => trivial
  | wire w _ => exact Nat.blt_eq.mp h

def checkAdderSpec (ops : List Op102) (targ : List Nat) (flip_out is_noop : Bool)
    (trueW falseW : List Nat)
    (c0_wire : XWire) (xwires : List XWire) : Bool :=
  let tr0 := mkLTree0 trueW falseW
  let M := targ.length
  (targ.all (fun w => Nat.blt w 100)) &&
  Nat.ble M 25 &&
  Nat.beq xwires.length M &&
  checkXWire c0_wire &&
  (xwires.all checkXWire) &&
  checkLTreeWF 7 tr0 &&
  checkTreeWires tr0 trueW falseW 100 &&
  let c0_expr := wireExpr c0_wire
  let xlist := xwires.map wireExpr
  match runAddListOpt targ flip_out falseW c0_expr xlist ops tr0 with
  | none => false
  | some trf =>
      checkNonOutRestored targ tr0 trf 100 &&
      checkOutBits targ flip_out is_noop falseW c0_expr xlist tr0 trf xlist 0

theorem mod_eq_of_add_carry {a b Q c : Nat} (ha : a < Q) (hc : c = 0 ∨ c = 1)
    (h : a + Q * c = b) : a = b % Q := by
  rcases hc with rfl | rfl
  · rw [mul_zero, add_zero] at h; subst h; exact (Nat.mod_eq_of_lt ha).symm
  · rw [mul_one] at h; subst h; rw [Nat.add_mod_right, Nat.mod_eq_of_lt ha]

theorem ltreeTargVal_adder_eq {targ : List Nat}
    {flip_out is_noop c0_val : Bool} {x_eval : Nat → Bool}
    {m0 mf : Fin 100 → Bool}
    (hhi : ∀ k : Nat, k < targ.length →
      targBit targ mf k =
        if is_noop then targBit targ m0 k
        else xor (xor (targBit targ m0 k) (x_eval k))
          (addCarryGen (fun j => xor (targBit targ m0 j) flip_out) x_eval c0_val k)) :
    ltreeTargVal targ mf =
      (ltreeTargVal targ m0 +
        if is_noop then 0
        else if flip_out then 2 ^ targ.length - (sumBits targ.length x_eval + c0_val.toNat)
        else (sumBits targ.length x_eval + c0_val.toNat)) % 2 ^ targ.length := by
  set M := targ.length
  have hm0_lt : ltreeTargVal targ m0 < 2 ^ M := ltreeTargVal_lt targ m0
  have hmf_lt : ltreeTargVal targ mf < 2 ^ M := ltreeTargVal_lt targ mf
  have hx_lt : sumBits M x_eval < 2 ^ M := sumBits_lt M _
  have hc0_le : c0_val.toNat ≤ 1 := by cases c0_val <;> decide
  cases is_noop
  · set bBit := fun j => xor (targBit targ m0 j) flip_out
    set mBit := targBit targ m0
    cases flip_out
    · have hb_eq : ∀ j < M, bBit j = mBit j := by
        intro j _; simp [bBit, mBit]
      have hhi' : ltreeTargVal targ mf =
          sumBits M
            (fun k => xor (xor (mBit k) (x_eval k)) (addCarryGen mBit x_eval c0_val k)) := by
        refine sumBits_congr fun k hk => ?_
        rw [hhi k hk, ite_eq_right Bool.false_ne_true,
            addCarryGen_congr k (fun j hj => hb_eq j (by omega))]
      have hadd := sumBits_addCarryGen c0_val M mBit x_eval
      set cout := (addCarryGen mBit x_eval c0_val M).toNat
      have hcout : cout = 0 ∨ cout = 1 := by
        change (addCarryGen mBit x_eval c0_val M).toNat = 0 ∨
          (addCarryGen mBit x_eval c0_val M).toNat = 1
        cases addCarryGen mBit x_eval c0_val M <;> decide
      have hm0_eq : ltreeTargVal targ m0 = sumBits M mBit := rfl
      have hlin : ltreeTargVal targ mf + 2 ^ M * cout =
          ltreeTargVal targ m0 + (sumBits M x_eval + c0_val.toNat) := by
        rw [hhi', hm0_eq]; linarith
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact mod_eq_of_add_carry hmf_lt hcout hlin
    · have hb_eq : ∀ j < M, bBit j = !(mBit j) := by
        intro j _; simp [bBit, mBit]
      have hxor_not : ∀ (a b c : Bool), xor (xor a b) c = !(xor (xor (!a) b) c) := by
        intro a b c; cases a <;> cases b <;> cases c <;> rfl
      have hhi' : ltreeTargVal targ mf =
          sumBits M (fun k =>
            !(xor (xor (!(mBit k)) (x_eval k))
              (addCarryGen (fun j => !(mBit j)) x_eval c0_val k))) := by
        refine sumBits_congr fun k hk => ?_
        rw [hhi k hk, ite_eq_right Bool.false_ne_true,
            addCarryGen_congr k (fun j hj => hb_eq j (by omega)), hxor_not]
      have hsub := sumBits_subCarryGen c0_val M mBit x_eval
      set cout := (addCarryGen (fun j => !(mBit j)) x_eval c0_val M).toNat
      have hcout : cout = 0 ∨ cout = 1 := by
        change (addCarryGen _ _ _ _).toNat = 0 ∨ (addCarryGen _ _ _ _).toNat = 1
        cases addCarryGen (fun j => !(mBit j)) x_eval c0_val M <;> decide
      have hlin : ltreeTargVal targ mf + (sumBits M x_eval + c0_val.toNat) =
          ltreeTargVal targ m0 + 2 ^ M * cout := by
        rw [hhi']; exact hsub
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases hcout with h0 | h1
      · rw [h0, mul_zero, add_zero] at hlin
        exact mod_eq_of_add_carry hmf_lt (Or.inr rfl) (by omega)
      · rw [h1, mul_one] at hlin
        exact mod_eq_of_add_carry hmf_lt (Or.inl rfl) (by omega)
  · have h1 : ltreeTargVal targ mf = ltreeTargVal targ m0 := by
      refine sumBits_congr fun k hk => ?_
      rw [hhi k hk, ite_eq_left rfl]
    simp only [↓reduceIte, add_zero, h1, Nat.mod_eq_of_lt hm0_lt]

theorem checkAdderSpec_sound
    {ops : List Op102} {targ : List Nat} {flip_out is_noop : Bool}
    {trueW falseW : List Nat}
    {c0_wire : XWire} {xwires : List XWire}
    (hspec : checkAdderSpec ops targ flip_out is_noop trueW falseW c0_wire xwires = true)
    {m0 : Fin 100 → Bool}
    (htrue : ∀ w : Fin 100, w.val ∈ trueW → m0 w = true)
    (hfalse : ∀ w : Fin 100, w.val ∈ falseW → m0 w = false) :
    ∃ mf : Fin 100 → Bool,
      execList102 ops m0 = some mf ∧
      (∀ w : Fin 100, w.val ∉ targ → mf w = m0 w) ∧
      ltreeTargVal targ mf =
        (ltreeTargVal targ m0 +
          if is_noop then 0
          else if flip_out then
            2 ^ targ.length -
              (sumBits targ.length (evalXWires m0 xwires) + (evalXWire m0 c0_wire).toNat)
          else
            (sumBits targ.length (evalXWires m0 xwires) +
              (evalXWire m0 c0_wire).toNat)) % 2 ^ targ.length := by
  unfold checkAdderSpec at hspec
  dsimp only at hspec
  set tr0 := mkLTree0 trueW falseW
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, List.all_eq_true, Nat.blt_eq] at hspec
  obtain ⟨⟨⟨⟨⟨⟨⟨htarg, hM25⟩, hlen⟩, hc0_b⟩, hw_lt_b⟩, hwf⟩, htw⟩, hrun⟩ := hspec
  cases hopt :
      runAddListOpt targ flip_out falseW (wireExpr c0_wire) (xwires.map wireExpr) ops tr0 with
  | none => rw [hopt] at hrun; cases hrun
  | some trf =>
    rw [hopt] at hrun
    simp only [Bool.and_eq_true] at hrun
    obtain ⟨hnon, hout⟩ := hrun
    have hc0_lt : xwireValid c0_wire := checkXWire_sound c0_wire hc0_b
    have hw_lt : ∀ xw ∈ xwires, xwireValid xw :=
      fun xw hxw => checkXWire_sound xw (hw_lt_b xw hxw)
    set c0_val := evalXWire m0 c0_wire
    have hI0 := AddInv_of_treeSpec (targ := targ) (flip_out := flip_out) (c0_val := c0_val)
      (x_eval := evalXWires m0 xwires) hwf htw htrue hfalse
    have hc0 := addEv_wireExpr m0 targ flip_out c0_val (evalXWires m0 xwires) c0_wire hc0_lt
    have hx_all := hx_all_of_wireExpr m0 targ flip_out c0_val xwires hw_lt
    have hxs := hxs_of_wireExpr m0 targ flip_out c0_val xwires hw_lt
    obtain ⟨mf, hex, hIf⟩ := runAddListOpt_sound hc0 htarg hfalse
      (by simp [hlen]) (by simp [hlen, hM25]) hx_all hxs ops hI0 hopt
    have hw_non : ∀ w : Fin 100, w.val ∉ targ → mf w = m0 w := by
      intro w hcond
      have heq := checkNonOutRestored_sound targ tr0 trf 100 hnon w.val w.isLt hcond
      rw [hIf.hWire w, heq, ← hI0.hWire w]
    have hw_out := checkOutBits_sound hc0 htarg hfalse hx_all hI0 hIf (xwires.map wireExpr) 0
      (by simp [hlen]) (by simp [hlen, hM25]) (fun i p hp => by simpa using hxs i p hp) hout
    refine ⟨mf, hex, hw_non, ltreeTargVal_adder_eq ?_⟩
    intro k hk
    simpa using hw_out k (by simp [hlen, hk])

def checkAdderRangeSpec (ops : List Op102) (sout M : Nat) (flip_out is_noop : Bool)
    (trueW falseW : List Nat) (c0_wire : XWire) (xwires : List XWire) : Bool :=
  checkAdderSpec ops (rangeList sout M) flip_out is_noop trueW falseW c0_wire xwires

theorem checkAdderRangeSpec_sound
    {ops : List Op102} {sout M : Nat} {flip_out is_noop : Bool}
    {trueW falseW : List Nat}
    {c0_wire : XWire} {xwires : List XWire}
    (hspec : checkAdderRangeSpec ops sout M flip_out is_noop trueW falseW c0_wire xwires = true)
    {m0 : Fin 100 → Bool}
    (htrue : ∀ w : Fin 100, w.val ∈ trueW → m0 w = true)
    (hfalse : ∀ w : Fin 100, w.val ∈ falseW → m0 w = false) :
    ∃ mf : Fin 100 → Bool,
      execList102 ops m0 = some mf ∧
      (∀ w : Fin 100, (w.val < sout ∨ sout + M ≤ w.val) → mf w = m0 w) ∧
      sliceVal sout M mf =
        (sliceVal sout M m0 +
          if is_noop then 0
          else if flip_out then
            2 ^ M - (sumBits M (evalXWires m0 xwires) + (evalXWire m0 c0_wire).toNat)
          else (sumBits M (evalXWires m0 xwires) + (evalXWire m0 c0_wire).toNat)) % 2 ^ M := by
  obtain ⟨mf, hex, hnon, hval⟩ := checkAdderSpec_sound hspec htrue hfalse
  rw [ltreeTargVal_rangeList, ltreeTargVal_rangeList, rangeList_length] at hval
  refine ⟨mf, hex, fun w hw => hnon w (fun hm => ?_), hval⟩
  have := mem_rangeList_iff.mp hm
  omega

def adderStepVal25 (sout : Nat) (flip_out is_noop : Bool) (c0_val : Bool)
    (x_eval : Nat → Bool) : Nat :=
  if is_noop then 0
  else
    let mag := 2 ^ sout * (sumBits (25 - sout) x_eval + c0_val.toNat)
    if flip_out then 33554432 - mag else mag

theorem checkAdder25_sound
    {ops : List Op102} {sout : Nat} {flip_out is_noop : Bool}
    {trueW falseW : List Nat}
    {c0_wire : XWire} {xwires : List XWire}
    (hsout : sout ≤ 25)
    (hspec :
      checkAdderRangeSpec ops sout (25 - sout) flip_out is_noop trueW falseW c0_wire xwires = true)
    {bit allM : Nat} {fMask : Nat → Nat} {m1 : Fin 100 → Bool}
    {tr : WTree} {m0 : Fin 100 → Bool}
    (hI : ParInv bit allM fMask m1 tr m0)
    (htrue : ∀ w : Fin 100, w.val ∈ trueW → m0 w = true)
    (hfalse : ∀ w : Fin 100, w.val ∈ falseW → m0 w = false) :
    ∃ mf : Fin 100 → Bool,
      execList102 ops m0 = some mf ∧
      ParInv bit allM fMask m1 tr mf ∧
      (∀ w : Fin 100, 25 ≤ w.val → mf w = m0 w) ∧
      outVal102 mf =
        (outVal102 m0 +
          adderStepVal25 sout flip_out is_noop (evalXWire m0 c0_wire) (evalXWires m0 xwires)) %
          33554432 := by
  obtain ⟨mf, hex, hnon, hsl⟩ := checkAdderRangeSpec_sound hspec htrue hfalse
  have hge25 : ∀ w : Fin 100, 25 ≤ w.val → mf w = m0 w :=
    fun w hw => hnon w (Or.inr (by omega))
  refine ⟨mf, hex, hI.congr_ge25 hge25, hge25, ?_⟩
  set M := 25 - sout
  have hsplit : sout + M = 25 := by omega
  have hpow25 : 2 ^ sout * 2 ^ M = 33554432 := by rw [← pow_add, hsplit]; norm_num
  have hlo_eq : sliceVal 0 sout mf = sliceVal 0 sout m0 := by
    refine sumBits_congr fun j hj => ?_
    simp only [Nat.zero_add]
    have hj102 : j < 100 := by omega
    rw [dite_eq_left hj102, dite_eq_left hj102]
    exact hnon ⟨j, hj102⟩ (Or.inl hj)
  have hmf_split : outVal102 mf = sliceVal 0 sout m0 + 2 ^ sout * sliceVal sout M mf := by
    unfold outVal102 sliceVal at hlo_eq ⊢
    rw [← hsplit, sumBits_split, hlo_eq]
    congr 2; refine sumBits_congr fun k _ => by simp only [Nat.zero_add]
  have hm0_split : outVal102 m0 = sliceVal 0 sout m0 + 2 ^ sout * sliceVal sout M m0 := by
    unfold outVal102 sliceVal
    rw [← hsplit, sumBits_split]
    congr 2; refine sumBits_congr fun k _ => by simp only [Nat.zero_add]
  have hhi_m0_lt : sliceVal sout M m0 < 2 ^ M := sumBits_lt M _
  have hx_lt : sumBits M (evalXWires m0 xwires) < 2 ^ M := sumBits_lt M _
  have hc0_le : (evalXWire m0 c0_wire).toNat ≤ 1 := by cases evalXWire m0 c0_wire <;> decide
  have hmf_lt : outVal102 mf < 33554432 := outVal102_lt mf
  unfold adderStepVal25
  dsimp only [M] at hsl hmf_split hm0_split hpow25 hhi_m0_lt hx_lt ⊢
  set A := sliceVal 0 sout m0
  set B0 := sliceVal sout (25 - sout) m0
  set Bf := sliceVal sout (25 - sout) mf
  set X := sumBits (25 - sout) (evalXWires m0 xwires) + (evalXWire m0 c0_wire).toNat
  set P := 2 ^ sout
  set Q := 2 ^ (25 - sout)
  cases is_noop <;> cases flip_out <;> simp only [Bool.false_eq_true, ↓reduceIte] at hsl ⊢
  · have hdiv_mod := Nat.div_add_mod (B0 + X) Q
    rw [← hsl] at hdiv_mod
    have hmul_eq : P * Bf + 33554432 * ((B0 + X) / Q) = P * B0 + P * X := by
      calc P * Bf + 33554432 * ((B0 + X) / Q)
          = P * (Bf + Q * ((B0 + X) / Q)) := by rw [← hpow25]; ring
        _ = P * B0 + P * X := by rw [add_comm Bf, hdiv_mod]; ring
    have h_eq : outVal102 mf + ((B0 + X) / Q) * 33554432 = outVal102 m0 + P * X := by linarith
    rw [← h_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmf_lt]
  · have hdiv_mod := Nat.div_add_mod (B0 + (Q - X)) Q
    rw [← hsl] at hdiv_mod
    have hPQ : P * (Q - X) = 33554432 - P * X := by
      rw [Nat.mul_sub_left_distrib, hpow25]
    have hmul_eq : P * Bf + 33554432 * ((B0 + (Q - X)) / Q) = P * B0 + (33554432 - P * X) := by
      calc P * Bf + 33554432 * ((B0 + (Q - X)) / Q)
          = P * (Bf + Q * ((B0 + (Q - X)) / Q)) := by rw [← hpow25]; ring
        _ = P * (B0 + (Q - X)) := by rw [add_comm Bf, hdiv_mod]
        _ = P * B0 + (33554432 - P * X) := by rw [Nat.mul_add, hPQ]
    have h_eq :
        outVal102 mf + ((B0 + (Q - X)) / Q) * 33554432 = outVal102 m0 + (33554432 - P * X) := by
      linarith
    rw [← h_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmf_lt]
  · simp only [add_zero, Nat.mod_eq_of_lt hhi_m0_lt] at hsl
    rw [hmf_split, hsl, ← hm0_split, add_zero, Nat.mod_eq_of_lt (outVal102_lt m0)]
  · simp only [add_zero, Nat.mod_eq_of_lt hhi_m0_lt] at hsl
    rw [hmf_split, hsl, ← hm0_split, add_zero, Nat.mod_eq_of_lt (outVal102_lt m0)]

def checkPermOut (sout : Nat) (trf : LTree) : List (Nat × Nat × Nat) → Nat → Bool
  | [], _ => true
  | p :: rest, k =>
      cond (eq3 (ltGet 6 trf (sout + k)) p)
        (checkPermOut sout trf rest (k + 1)) false

theorem checkPermOut_sound {m0 mf : Fin 100 → Bool} {sout : Nat} {x_eval target_eval : Nat → Bool}
    {trf : LTree} (hIf : AddInv m0 [] false false x_eval trf mf) :
    ∀ (ps : List (Nat × Nat × Nat)) (k : Nat) (_hlen : sout + k + ps.length ≤ 100),
      (∀ i p, ps[i]? = some p → addEv m0 [] false false x_eval p = target_eval (k + i)) →
      checkPermOut sout trf ps k = true →
      ∀ j (_hj : j < ps.length),
        mf ⟨sout + k + j, by omega⟩ = target_eval (k + j)
  | [], _, _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | p :: rest, k, hlen, hps, hok, j, hj => by
    dsimp only [List.length_cons] at hlen hj
    dsimp only [checkPermOut] at hok
    cases hc : eq3 (ltGet 6 trf (sout + k)) p
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    cases j with
    | zero =>
      have h1 := hIf.hWire ⟨sout + k, by omega⟩
      have hp0 := hps 0 p rfl
      rw [eq3_iff.mp hc] at h1
      simpa using h1.trans hp0
    | succ j =>
      have ih := checkPermOut_sound hIf rest (k + 1) (by omega)
        (fun i q hq => by rw [show k + 1 + i = k + (i + 1) by omega]; exact hps (i + 1) q hq)
        hok j (by omega)
      simpa [show sout + (k + 1) + j = sout + k + (j + 1) by omega,
             show k + 1 + j = k + (j + 1) by omega] using ih

def checkPermSpec (ops : List Op102) (sout M : Nat)
    (trueW falseW : List Nat) (targets : List XWire) : Bool :=
  let tr0 := mkLTree0 trueW falseW
  Nat.ble (sout + M) 100 &&
  Nat.beq targets.length M &&
  (targets.all checkXWire) &&
  checkLTreeWF 7 tr0 &&
  checkTreeWires tr0 trueW falseW 100 &&
  match runAddListOpt [] false falseW (0, 0, 0) [] ops tr0 with
  | none => false
  | some trf =>
      checkNonOutRestored (rangeList sout M) tr0 trf 100 &&
      checkPermOut sout trf (targets.map wireExpr) 0

theorem checkPermSpec_sound
    {ops : List Op102} {sout M : Nat} {trueW falseW : List Nat} {targets : List XWire}
    (hspec : checkPermSpec ops sout M trueW falseW targets = true)
    {m0 : Fin 100 → Bool}
    (htrue : ∀ w : Fin 100, w.val ∈ trueW → m0 w = true)
    (hfalse : ∀ w : Fin 100, w.val ∈ falseW → m0 w = false) :
    ∃ mf : Fin 100 → Bool,
      execList102 ops m0 = some mf ∧
      (∀ w : Fin 100, (w.val < sout ∨ sout + M ≤ w.val) → mf w = m0 w) ∧
      (∀ k : Nat, (hk : k < M) →
        mf ⟨sout + k, (by
          have := hspec; unfold checkPermSpec at this
          simp only [Bool.and_eq_true, Nat.ble_eq] at this; omega)⟩ =
          evalXWires m0 targets k) ∧
      sliceVal sout M mf = sumBits M (evalXWires m0 targets) := by
  unfold checkPermSpec at hspec
  dsimp only at hspec
  set tr0 := mkLTree0 trueW falseW
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, List.all_eq_true] at hspec
  obtain ⟨⟨⟨⟨⟨hsoutM, hlen⟩, hw_lt_b⟩, hwf⟩, htw⟩, hrun⟩ := hspec
  cases hopt : runAddListOpt [] false falseW (0, 0, 0) [] ops tr0 with
  | none => rw [hopt] at hrun; cases hrun
  | some trf =>
    rw [hopt] at hrun
    simp only [Bool.and_eq_true] at hrun
    obtain ⟨hnon, hperm⟩ := hrun
    have hw_lt : ∀ xw ∈ targets, xwireValid xw :=
      fun xw hxw => checkXWire_sound xw (hw_lt_b xw hxw)
    have hI0 := AddInv_of_treeSpec (targ := []) (flip_out := false) (c0_val := false)
      (x_eval := fun _ => false) hwf htw htrue hfalse
    have hx_empty : ∀ j, addEv m0 [] false false (fun _ => false)
        (([] : List (Nat × Nat × Nat)).getD j (0, 0, 0)) = false :=
      fun _ => addEv_zero m0 [] false false _
    obtain ⟨mf, hex, hIf⟩ :=
      runAddListOpt_sound (addEv_zero m0 [] false false _) (fun _ h => by cases h)
      hfalse (by decide) (by decide) hx_empty (fun _ _ hp => by cases hp) ops hI0 hopt
    have hw_non : ∀ w : Fin 100, (w.val < sout ∨ sout + M ≤ w.val) → mf w = m0 w := by
      intro w hcond
      have hnot : w.val ∉ rangeList sout M := fun hm => by
        have := mem_rangeList_iff.mp hm
        omega
      have heq := checkNonOutRestored_sound (rangeList sout M) tr0 trf 100 hnon w.val w.isLt hnot
      rw [hIf.hWire w, heq, ← hI0.hWire w]
    have hps : ∀ i p, (targets.map wireExpr)[i]? = some p →
        addEv m0 [] false false (fun _ => false) p = evalXWires m0 targets i := by
      intro i p hp
      rw [List.getElem?_map] at hp
      unfold evalXWires
      cases hx : targets[i]? with
      | none => rw [hx] at hp; cases hp
      | some xw =>
        rw [hx] at hp
        injection hp with hp'; subst hp'
        exact addEv_wireExpr m0 [] false false _ xw (hw_lt xw (List.mem_of_getElem? hx))
    have hw_perm :=
      checkPermOut_sound (target_eval := evalXWires m0 targets) hIf (targets.map wireExpr) 0
      (by simp [hlen, hsoutM]) (fun i p hp => by simpa using hps i p hp) hperm
    have hbit : ∀ k : Nat, (hk : k < M) → mf ⟨sout + k, by omega⟩ = evalXWires m0 targets k := by
      intro k hk
      simpa using hw_perm k (by simp [hlen, hk])
    refine ⟨mf, hex, hw_non, hbit, ?_⟩
    unfold sliceVal
    refine sumBits_congr fun k hk => ?_
    rw [dite_eq_left (by omega)]
    exact hbit k hk

def beqWTree : WTree → WTree → Bool
  | .leaf v1, .leaf v2 => Nat.beq v1 v2
  | .node l1 r1, .node l2 r2 => beqWTree l1 l2 && beqWTree r1 r2
  | _, _ => false

theorem beqWTree_sound : ∀ (t1 t2 : WTree), beqWTree t1 t2 = true → t1 = t2
  | .leaf v1, .leaf v2, h => by
      dsimp only [beqWTree] at h
      exact congrArg WTree.leaf (Nat.beq_eq.mp h)
  | .node l1 r1, .node l2 r2, h => by
      dsimp only [beqWTree] at h
      rw [Bool.and_eq_true] at h
      rw [beqWTree_sound l1 l2 h.1, beqWTree_sound r1 r2 h.2]
  | .leaf _, .node _ _, h => by cases h
  | .node _ _, .leaf _, h => by cases h


def zAnc52 : List Nat := rangeList 50 50

theorem mem_zAnc52_iff {w : Nat} : w ∈ zAnc52 ↔ 50 ≤ w ∧ w < 100 :=
  mem_rangeList_iff


theorem checkEqList_length {tr : WTree} :
    ∀ {ws vs : List Nat}, checkEqList tr ws vs = true → ws.length = vs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | w :: ws, v :: vs, h => by
      dsimp only [checkEqList] at h
      cases hc : Nat.beq (wGet tr w) v
      · rw [hc, Bool.cond_false] at h; cases h
      rw [hc, Bool.cond_true] at h
      simp [checkEqList_length h]

theorem checkEqList_rangeList_getD {tr : WTree} {sout M : Nat} {expL : List Nat}
    (heq : checkEqList tr (rangeList sout M) expL = true)
    (k : Nat) (hk : k < M) :
    wGet tr (sout + k) = expL.getD k 0 := by
  have h1 := rangeList_getElem? (sout := sout) (M := M) (k := k) hk
  have hlen_eq : (rangeList sout M).length = expL.length := checkEqList_length heq
  rw [rangeList_length] at hlen_eq
  have hexp_lt : k < expL.length := by omega
  have h2 : expL[k]? = some (expL.getD k 0) := by
    rw [List.getElem?_eq_getElem hexp_lt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hexp_lt]; rfl
  exact checkEqList_sound _ _ heq k (sout + k) (expL.getD k 0) h1 h2

def checkU24Restored (t0 tf : WTree) : Bool :=
  checkEqList tf (rangeList 25 24) ((rangeList 25 24).map (wGet t0))

theorem checkU24Restored_sound {bit allM : Nat} {fMask : Nat → Nat}
    {m1 m : Fin 100 → Bool} {t0 tf : WTree}
    (hI0 : ParInv bit allM fMask m1 t0 m1)
    (hIf : ParInv bit allM fMask m1 tf m)
    (hok : checkU24Restored t0 tf = true) :
    ∀ i : Nat, (hi : i < 24) → m ⟨25 + i, by omega⟩ = m1 ⟨25 + i, by omega⟩ := by
  unfold checkU24Restored at hok
  intro i hi
  by_cases hfm : (fMask i).testBit bit = true
  · exact hIf.hFree ⟨25 + i, by omega⟩
      (Or.inl ⟨by dsimp only; omega, by dsimp only; omega,
        by dsimp only; simpa [Nat.add_sub_cancel_left] using hfm⟩)
  · simp only [Bool.not_eq_true] at hfm
    have hp : isParWire (25 + i) = true := by
      unfold isParWire; simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; omega
    have hgfm : (getFMask fMask (25 + i)).testBit bit = false := by
      unfold getFMask; rw [ite_eq_left (by omega)]; simpa using hfm
    have h1 := rangeList_getElem? hi (sout := 25)
    have h2 : ((rangeList 25 24).map (wGet t0))[i]? = some (wGet t0 (25 + i)) := by
      rw [List.getElem?_map, h1]; rfl
    have hget := checkEqList_sound _ _ hok i (25 + i) (wGet t0 (25 + i)) h1 h2
    rw [hIf.hTracked ⟨25 + i, by omega⟩ hp hgfm,
        hI0.hTracked ⟨25 + i, by omega⟩ hp hgfm, hget]

theorem sumBits_testBit : ∀ (M : Nat) (g : Nat → Bool) (i : Nat), i < M →
    (sumBits M g).testBit i = g i
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | M + 1, g, i, hi => by
      rw [sumBits_succ]
      have hlt : sumBits M g < 2 ^ M := sumBits_lt M g
      by_cases hiM : i < M
      · have hmod : (sumBits M g + 2 ^ M * (g M).toNat) % 2 ^ M = sumBits M g := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
        have htb : (sumBits M g + 2 ^ M * (g M).toNat).testBit i =
            ((sumBits M g + 2 ^ M * (g M).toNat) % 2 ^ M).testBit i := by
          rw [Nat.testBit_mod_two_pow, decide_eq_true hiM, Bool.true_and]
        rw [htb, hmod]
        exact sumBits_testBit M g i hiM
      · have hi_eq : i = M := by omega
        subst i
        have hdiv : (sumBits M g + 2 ^ M * (g M).toNat) / 2 ^ M = (g M).toNat := by
          rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
        rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]
        cases g M <;> decide

def fMaskZero (_ : Nat) : Nat := 0

theorem sumBits_zero_fn : ∀ (M : Nat), sumBits M (fun _ => false) = 0
  | 0 => rfl
  | M + 1 => by simp [sumBits_succ, sumBits_zero_fn M]

theorem testBit_two_pow_sub_one_of_lt {M i : Nat} (hi : i < M) :
    (2 ^ M - 1).testBit i = true := by
  have hnot := sumBits_not M (fun _ => false)
  rw [sumBits_zero_fn M, Nat.add_zero] at hnot
  rw [← hnot]
  exact sumBits_testBit M (fun _ => !false) i hi

theorem getFMask_fMaskZero_testBit (q bit : Nat) :
    (getFMask fMaskZero q).testBit bit = false := by
  unfold getFMask fMaskZero
  split_ifs <;> exact Nat.zero_testBit bit

theorem ble_false_iff (a b : Nat) : Nat.ble a b = false ↔ b < a := by
  rw [← Bool.not_eq_true, Nat.ble_eq, not_le]

def getBits (bit : Nat) (l : List Nat) (off len : Nat) : Nat :=
  sumBits len (fun i => (l.getD (off + i) 0).testBit bit)

theorem getBits_lt (bit : Nat) (l : List Nat) (off len : Nat) :
    getBits bit l off len < 2 ^ len :=
  sumBits_lt len _

theorem getBits_split (bit : Nat) (l : List Nat) (off a b : Nat) :
    getBits bit l off (a + b) = getBits bit l off a + 2 ^ a * getBits bit l (off + a) b := by
  unfold getBits
  rw [sumBits_split]
  congr 2
  refine sumBits_congr fun k _ => ?_
  rw [Nat.add_assoc]

theorem getBits_of_checkEqList {bit allM : Nat} {fMask : Nat → Nat}
    {m1 m : Fin 100 → Bool} {tr : WTree} {sout M : Nat} {expL : List Nat}
    (hI : ParInv bit allM fMask m1 tr m)
    (hanc : 50 ≤ sout) (htop : sout + M ≤ 100)
    (heq : checkEqList tr (rangeList sout M) expL = true)
    (off len : Nat) (hlen : off + len ≤ M) :
    sliceVal (sout + off) len m = getBits bit expL off len := by
  unfold sliceVal getBits
  refine sumBits_congr fun k hk => ?_
  have hw_lt : sout + off + k < 100 := by omega
  rw [dite_eq_left hw_lt]
  have hp : isParWire (sout + off + k) = true :=
    (isParWire_of_anc (fMask := fMask) (by omega) hw_lt).1
  have hfm : (getFMask fMask (sout + off + k)).testBit bit = false := by
    unfold getFMask; rw [ite_eq_right (by omega), Nat.zero_testBit]
  have h1 := rangeList_getElem? (sout := sout) (M := M) (k := off + k) (by omega)
  have hlen_eq : (rangeList sout M).length = expL.length := checkEqList_length heq
  rw [rangeList_length] at hlen_eq
  have hexp_lt : off + k < expL.length := by omega
  have h2 : expL[off + k]? = some (expL.getD (off + k) 0) := by
    rw [List.getElem?_eq_getElem hexp_lt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hexp_lt]; rfl
  have hget := checkEqList_sound _ _ heq (off + k) (sout + (off + k)) (expL.getD (off + k) 0) h1 h2
  rw [show sout + (off + k) = sout + off + k by omega] at hget
  rw [hI.hTracked ⟨sout + off + k, hw_lt⟩ hp hfm, hget]

theorem checkAdder25_raw_sound
    {ops : List Op102} {is_noop : Bool}
    {trueW falseW : List Nat} {c0_wire : XWire} {xwires : List XWire}
    (hspec : checkAdderRangeSpec ops 0 25 false is_noop trueW falseW c0_wire xwires = true)
    {m0 : Fin 100 → Bool}
    (htrue : ∀ w : Fin 100, w.val ∈ trueW → m0 w = true)
    (hfalse : ∀ w : Fin 100, w.val ∈ falseW → m0 w = false) :
    ∃ mf : Fin 100 → Bool,
      execList102 ops m0 = some mf ∧
      (∀ w : Fin 100, 25 ≤ w.val → mf w = m0 w) ∧
      outVal102 mf =
        if is_noop then outVal102 m0
        else (outVal102 m0 +
          (sumBits 25 (evalXWires m0 xwires) + (evalXWire m0 c0_wire).toNat)) % 33554432 := by
  obtain ⟨mf, hex, hnon, hsl⟩ := checkAdderRangeSpec_sound hspec htrue hfalse
  refine ⟨mf, hex, fun w hw => hnon w (Or.inr hw), ?_⟩
  unfold outVal102
  rw [hsl]
  have hpow : (2 : Nat) ^ 25 = 33554432 := by decide
  have hlt : sliceVal 0 25 m0 < 33554432 := sumBits_lt 25 _
  cases is_noop <;> simp [hpow, Nat.mod_eq_of_lt hlt]

theorem sumBits_testBit_eq (n : Nat) :
    ∀ u < 2 ^ n, sumBits n (fun k => u.testBit k) = u := by
  induction n with
  | zero =>
    intro u hu; simp [sumBits] at hu ⊢; omega
  | succ n ih =>
    intro u hu
    rw [sumBits_succ]
    have hdiv : u / 2 ^ n < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      simpa [pow_succ'] using hu
    have hmod : u % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
    have h_low : sumBits n (fun k => u.testBit k) = sumBits n (fun k => (u % 2 ^ n).testBit k) := by
      refine sumBits_congr fun k hk => ?_
      rw [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and]
    rw [h_low, ih (u % 2 ^ n) hmod]
    have htb : (u.testBit n).toNat = u / 2 ^ n := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.mod_eq_of_lt hdiv]
      generalize hd : u / 2 ^ n = d at hdiv
      rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl <;> rfl
    rw [htb]
    rw [Nat.add_comm, Nat.div_add_mod]



theorem andCount_s1 : (s1Ops.map Op102.andCount).sum = 47 := by decide +kernel
theorem andCount_s2a : (s2aOps.map Op102.andCount).sum = 17 := by decide +kernel
theorem andCount_s2b : (s2bOps.map Op102.andCount).sum = 47 := by decide +kernel
theorem andCount_s2c : (s2cOps.map Op102.andCount).sum = 0 := by decide +kernel
theorem andCount_s3a : seqAndCount s3aAllSeq = 33 := by decide +kernel
theorem andCount_s3b : (s3bOps.map Op102.andCount).sum = 42 := by decide +kernel
theorem andCount_s4_1 : (s4_1Ops.map Op102.andCount).sum = 12 := by decide +kernel
theorem andCount_s4_1Post : (s4_1PostOps.map Op102.andCount).sum = 0 := by decide +kernel
theorem andCount_s4_2 : (s4_2Ops.map Op102.andCount).sum = 40 := by decide +kernel
theorem andCount_s4_3 : (s4_3Ops.map Op102.andCount).sum = 98 := by decide +kernel
theorem andCount_s4_4 : (s4_4Ops.map Op102.andCount).sum = 50 := by decide +kernel
theorem andCount_s5_1 : (s5_1Ops.map Op102.andCount).sum = 90 := by decide +kernel
theorem andCount_s5_2Core : (s5_2CoreOps.map Op102.andCount).sum = 21 := by decide +kernel
theorem andCount_s5_2Pre : (s5_2PostPreOps.map Op102.andCount).sum = 0 := by decide +kernel
theorem andCount_s5_2Inner : seqAndCount s5_2PostInnerSeq = 16 := by decide +kernel
theorem andCount_s5_2Suf : (s5_2PostSufOps.map Op102.andCount).sum = 0 := by decide +kernel
theorem andCount_s5_3 : (s5_3Ops.map Op102.andCount).sum = 166 := by decide +kernel
theorem andCount_s5_4 : seqAndCount s5_4Seq = 19 := by decide +kernel
theorem andCount_s6a : (s6aOps.map Op102.andCount).sum = 0 := by decide +kernel
theorem andCount_s6b : (s6bOps.map Op102.andCount).sum = 47 := by decide +kernel
theorem andCount_s6c : (s6cOps.map Op102.andCount).sum = 5 := by decide +kernel
theorem andCount_s7 : (s7Ops.map Op102.andCount).sum = 23 := by decide +kernel

theorem andCount_allOps102 : (allOps102.map Op102.andCount).sum = 773 := by
  unfold allOps102 midOps102 preOps102 postOps102 s3aOps s5_2Ops
    s5_2PostOps s5_2PostInnerOps s5_4Ops
  simp only [map_andCount_append, map_andCount_flatten,
    andCount_s1, andCount_s2a, andCount_s2b, andCount_s2c,
    andCount_s3a, andCount_s3b, andCount_s4_1, andCount_s4_1Post,
    andCount_s4_2, andCount_s4_3, andCount_s4_4,
    andCount_s5_1, andCount_s5_2Core, andCount_s5_2Pre, andCount_s5_2Inner, andCount_s5_2Suf,
    andCount_s5_3, andCount_s5_4, andCount_s6a, andCount_s6b, andCount_s6c, andCount_s7]


theorem all_inSub_flatten (p : Nat → Bool) : ∀ (seq : List (List Op102)),
    seq.flatten.all (Op102.inSub p) = seq.all (fun l => l.all (Op102.inSub p))
  | [] => rfl
  | l :: ls => by rw [List.flatten_cons, List.all_append, List.all_cons, all_inSub_flatten p ls]

theorem inNoStash_s2a : s2aOps.all (Op102.inSub (pNoStash stash_pre)) = true := by decide +kernel
theorem inNoStash_s2b : s2bOps.all (Op102.inSub (pNoStash stash_pre)) = true := by decide +kernel
theorem inNoStash_s2c : s2cOps.all (Op102.inSub (pNoStash stash_pre)) = true := by decide +kernel
theorem inNoStash_s3a_0 :
    s3aSeq_0.all (fun l => l.all (Op102.inSub (pNoStash stash_pre))) = true := by
  decide +kernel
theorem inNoStash_s3a_1 :
    s3aSeq_1.all (fun l => l.all (Op102.inSub (pNoStash stash_pre))) = true := by
  decide +kernel
theorem inNoStash_s3a_2 :
    s3aSeq_2.all (fun l => l.all (Op102.inSub (pNoStash stash_pre))) = true := by
  decide +kernel
theorem inNoStash_s3a_3 :
    s3aSeq_3.all (fun l => l.all (Op102.inSub (pNoStash stash_pre))) = true := by
  decide +kernel
theorem inNoStash_s3a_4 :
    s3aSeq_4.all (fun l => l.all (Op102.inSub (pNoStash stash_pre))) = true := by
  decide +kernel
theorem inNoStash_s3a_5 :
    s3aSeq_5.all (fun l => l.all (Op102.inSub (pNoStash stash_pre))) = true := by
  decide +kernel
theorem inNoStash_s3b : s3bOps.all (Op102.inSub (pNoStash stash_pre)) = true := by decide +kernel

theorem inNoStash_pre : preOps102.all (Op102.inSub (pNoStash stash_pre)) = true := by
  unfold preOps102 s3aOps s3aAllSeq
  simp only [List.all_append, all_inSub_flatten,
    inNoStash_s2a, inNoStash_s2b, inNoStash_s2c,
    inNoStash_s3a_0, inNoStash_s3a_1, inNoStash_s3a_2,
    inNoStash_s3a_3, inNoStash_s3a_4, inNoStash_s3a_5,
    inNoStash_s3b, Bool.and_self]

theorem inNoStash_41 : s4_1Ops.all (Op102.inSub (pNoStash stash_41)) = true := by decide +kernel
theorem inNoStash_41p :
    s4_1PostOps.all (Op102.inSub (pNoStash stash_41p)) = true := by decide +kernel

theorem inNoStash_s4_2 :
    s4_2Ops.all (Op102.inSub (pNoStash stash_42_52c)) = true := by decide +kernel
theorem inNoStash_s4_3 :
    s4_3Ops.all (Op102.inSub (pNoStash stash_42_52c)) = true := by decide +kernel
theorem inNoStash_s4_4 :
    s4_4Ops.all (Op102.inSub (pNoStash stash_42_52c)) = true := by decide +kernel
theorem inNoStash_s5_1 :
    s5_1Ops.all (Op102.inSub (pNoStash stash_42_52c)) = true := by decide +kernel
theorem inNoStash_s5_2Core :
    s5_2CoreOps.all (Op102.inSub (pNoStash stash_42_52c)) = true := by decide +kernel

theorem inNoStash_42_52c :
    stages4_2_to_5_2Core.all (Op102.inSub (pNoStash stash_42_52c)) = true := by
  unfold stages4_2_to_5_2Core
  simp only [List.all_append, inNoStash_s4_2, inNoStash_s4_3, inNoStash_s4_4,
    inNoStash_s5_1, inNoStash_s5_2Core, Bool.and_self]

theorem inNoStash_52p :
    s5_2PostOps.all (Op102.inSub (pNoStash stash_52p)) = true := by decide +kernel
theorem inNoStash_53 : s5_3Ops.all (Op102.inSub (pNoStash stash_53)) = true := by decide +kernel

theorem inNoStash_s5_4 :
    s5_4Seq.all (fun l => l.all (Op102.inSub (pNoStash stash_post))) = true := by
  decide +kernel
theorem inNoStash_s6a : s6aOps.all (Op102.inSub (pNoStash stash_post)) = true := by decide +kernel
theorem inNoStash_s6b : s6bOps.all (Op102.inSub (pNoStash stash_post)) = true := by decide +kernel
theorem inNoStash_s6c : s6cOps.all (Op102.inSub (pNoStash stash_post)) = true := by decide +kernel

theorem inNoStash_post : postOps102.all (Op102.inSub (pNoStash stash_post)) = true := by
  unfold postOps102 s5_4Ops
  simp only [List.all_append, all_inSub_flatten,
    inNoStash_s5_4, inNoStash_s6a, inNoStash_s6b, inNoStash_s6c, Bool.and_self]

def midPhysicalOps : List Op102 :=
  hop_0 ++ preOps102 ++
  hop_1 ++ s4_1Ops ++
  hop_2 ++ s4_1PostOps ++
  hop_3 ++ stages4_2_to_5_2Core ++
  hop_4 ++ s5_2PostOps ++
  hop_5 ++ s5_3Ops ++
  hop_6 ++ postOps102 ++
  hop_7

theorem midPhysicalOps_eq_hops :
    midPhysicalOps =
      hopOps 48 stash_pre ++ preOps102 ++
      hopOps stash_pre stash_41 ++ s4_1Ops ++
      hopOps stash_41 stash_41p ++ s4_1PostOps ++
      hopOps stash_41p stash_42_52c ++ stages4_2_to_5_2Core ++
      hopOps stash_42_52c stash_52p ++ s5_2PostOps ++
      hopOps stash_52p stash_53 ++ s5_3Ops ++
      hopOps stash_53 stash_post ++ postOps102 ++
      hopOps stash_post 48 := rfl

def fullK25Ops : List Op102 := s1Ops ++ midPhysicalOps ++ s7Ops

theorem andCount_hop_0 : (hop_0.map Op102.andCount).sum = 0 := rfl
theorem andCount_hop_1 : (hop_1.map Op102.andCount).sum = 0 := rfl
theorem andCount_hop_2 : (hop_2.map Op102.andCount).sum = 0 := rfl
theorem andCount_hop_3 : (hop_3.map Op102.andCount).sum = 0 := rfl
theorem andCount_hop_4 : (hop_4.map Op102.andCount).sum = 0 := rfl
theorem andCount_hop_5 : (hop_5.map Op102.andCount).sum = 0 := rfl
theorem andCount_hop_6 : (hop_6.map Op102.andCount).sum = 0 := rfl
theorem andCount_hop_7 : (hop_7.map Op102.andCount).sum = 0 := rfl

theorem andCount_fullK25Ops : (fullK25Ops.map Op102.andCount).sum = 773 := by
  have h : (fullK25Ops.map Op102.andCount).sum = (allOps102.map Op102.andCount).sum := by
    unfold fullK25Ops allOps102 midPhysicalOps midOps102 stages4_2_to_5_2Core s5_2Ops
    simp only [map_andCount_append,
      andCount_hop_0, andCount_hop_1, andCount_hop_2, andCount_hop_3,
      andCount_hop_4, andCount_hop_5, andCount_hop_6, andCount_hop_7,
      Nat.zero_add, Nat.add_zero, Nat.add_assoc]
  rw [h, andCount_allOps102]

theorem tCount_s1 : (s1Ops.map Op102.tCount).sum = 188 := by decide +kernel
theorem tCount_s2a : (s2aOps.map Op102.tCount).sum = 68 := by decide +kernel
theorem tCount_s2b : (s2bOps.map Op102.tCount).sum = 188 := by decide +kernel
theorem tCount_s2c : (s2cOps.map Op102.tCount).sum = 0 := by decide +kernel
theorem tCount_s3a : seqTCount s3aAllSeq = 472 := by decide +kernel
theorem tCount_s3b : (s3bOps.map Op102.tCount).sum = 398 := by decide +kernel
theorem tCount_s4_1 : (s4_1Ops.map Op102.tCount).sum = 48 := by decide +kernel
theorem tCount_s4_1Post : (s4_1PostOps.map Op102.tCount).sum = 0 := by decide +kernel
theorem tCount_s4_2 : (s4_2Ops.map Op102.tCount).sum = 160 := by decide +kernel
theorem tCount_s4_3 : (s4_3Ops.map Op102.tCount).sum = 392 := by decide +kernel
theorem tCount_s4_4 : (s4_4Ops.map Op102.tCount).sum = 200 := by decide +kernel
theorem tCount_s5_1 : (s5_1Ops.map Op102.tCount).sum = 360 := by decide +kernel
theorem tCount_s5_2Core : (s5_2CoreOps.map Op102.tCount).sum = 84 := by decide +kernel
theorem tCount_s5_2Pre : (s5_2PostPreOps.map Op102.tCount).sum = 0 := by decide +kernel
theorem tCount_s5_2Inner : seqTCount s5_2PostInnerSeq = 64 := by decide +kernel
theorem tCount_s5_2Suf : (s5_2PostSufOps.map Op102.tCount).sum = 0 := by decide +kernel
theorem tCount_s5_3 : (s5_3Ops.map Op102.tCount).sum = 664 := by decide +kernel
theorem tCount_s5_4 : seqTCount s5_4Seq = 76 := by decide +kernel
theorem tCount_s6a : (s6aOps.map Op102.tCount).sum = 0 := by decide +kernel
theorem tCount_s6b : (s6bOps.map Op102.tCount).sum = 188 := by decide +kernel
theorem tCount_s6c : (s6cOps.map Op102.tCount).sum = 20 := by decide +kernel
theorem tCount_s7 : (s7Ops.map Op102.tCount).sum = 92 := by decide +kernel

theorem tCount_allOps102 : (allOps102.map Op102.tCount).sum = 3662 := by
  unfold allOps102 midOps102 preOps102 postOps102 s3aOps s5_2Ops
    s5_2PostOps s5_2PostInnerOps s5_4Ops
  simp only [map_tCount_append, map_tCount_flatten,
    tCount_s1, tCount_s2a, tCount_s2b, tCount_s2c,
    tCount_s3a, tCount_s3b, tCount_s4_1, tCount_s4_1Post, tCount_s4_2, tCount_s4_3, tCount_s4_4,
    tCount_s5_1, tCount_s5_2Core, tCount_s5_2Pre, tCount_s5_2Inner, tCount_s5_2Suf,
    tCount_s5_3, tCount_s5_4, tCount_s6a, tCount_s6b, tCount_s6c, tCount_s7]

theorem tCount_hop_0 : (hop_0.map Op102.tCount).sum = 0 := rfl
theorem tCount_hop_1 : (hop_1.map Op102.tCount).sum = 0 := rfl
theorem tCount_hop_2 : (hop_2.map Op102.tCount).sum = 0 := rfl
theorem tCount_hop_3 : (hop_3.map Op102.tCount).sum = 0 := rfl
theorem tCount_hop_4 : (hop_4.map Op102.tCount).sum = 0 := rfl
theorem tCount_hop_5 : (hop_5.map Op102.tCount).sum = 0 := rfl
theorem tCount_hop_6 : (hop_6.map Op102.tCount).sum = 0 := rfl
theorem tCount_hop_7 : (hop_7.map Op102.tCount).sum = 0 := rfl

theorem tCount_fullK25Ops : (fullK25Ops.map Op102.tCount).sum = 3662 := by
  have h : (fullK25Ops.map Op102.tCount).sum = (allOps102.map Op102.tCount).sum := by
    unfold fullK25Ops allOps102 midPhysicalOps midOps102 stages4_2_to_5_2Core s5_2Ops
    simp only [map_tCount_append,
      tCount_hop_0, tCount_hop_1, tCount_hop_2, tCount_hop_3,
      tCount_hop_4, tCount_hop_5, tCount_hop_6, tCount_hop_7,
      Nat.zero_add, Nat.add_zero, Nat.add_assoc]
  rw [h, tCount_allOps102]

theorem all_noPhase_flatten : ∀ (seq : List (List Op102)),
    seq.flatten.all Op102.noPhase = seq.all (fun l => l.all Op102.noPhase)
  | [] => rfl
  | l :: ls => by rw [List.flatten_cons, List.all_append, List.all_cons, all_noPhase_flatten ls]

theorem noPhase_s1 : s1Ops.all Op102.noPhase = true := by decide +kernel
theorem noPhase_s2a : s2aOps.all Op102.noPhase = true := by decide +kernel
theorem noPhase_s2b : s2bOps.all Op102.noPhase = true := by decide +kernel
theorem noPhase_s2c : s2cOps.all Op102.noPhase = true := by decide +kernel
theorem noPhase_s3bAdd : s3bAddOps.all Op102.noPhase = true := by decide +kernel
theorem noPhase_s4_1 : s4_1Ops.all Op102.noPhase = true := by decide +kernel
theorem noPhase_s4_1Post : s4_1PostOps.all Op102.noPhase = true := by decide +kernel
theorem noPhase_s4_2 : s4_2Ops.all Op102.noPhase = true := by decide +kernel
theorem noPhase_s4_3 : s4_3Ops.all Op102.noPhase = true := by decide +kernel
theorem noPhase_s4_4 : s4_4Ops.all Op102.noPhase = true := by decide +kernel
theorem noPhase_s5_1 : s5_1Ops.all Op102.noPhase = true := by decide +kernel
theorem noPhase_s5_2Core : s5_2CoreOps.all Op102.noPhase = true := by decide +kernel
theorem noPhase_42_52c : stages4_2_to_5_2Core.all Op102.noPhase = true := by
  unfold stages4_2_to_5_2Core
  simp only [List.all_append, noPhase_s4_2, noPhase_s4_3, noPhase_s4_4,
    noPhase_s5_1, noPhase_s5_2Core, Bool.and_self]
theorem noPhase_52p : s5_2PostOps.all Op102.noPhase = true := by decide +kernel
theorem noPhase_53 : s5_3Ops.all Op102.noPhase = true := by decide +kernel
theorem noPhase_s5_4 : s5_4Seq.all (fun l => l.all Op102.noPhase) = true := by decide +kernel
theorem noPhase_s6a : s6aOps.all Op102.noPhase = true := by decide +kernel
theorem noPhase_s6b : s6bOps.all Op102.noPhase = true := by decide +kernel
theorem noPhase_s6c : s6cOps.all Op102.noPhase = true := by decide +kernel
theorem noPhase_post : postOps102.all Op102.noPhase = true := by
  unfold postOps102 s5_4Ops
  simp only [List.all_append, all_noPhase_flatten,
    noPhase_s5_4, noPhase_s6a, noPhase_s6b, noPhase_s6c, Bool.and_self]
theorem noPhase_s7 : s7Ops.all Op102.noPhase = true := by decide +kernel


end QuantumComputation.Specs.ArcsinImpl
