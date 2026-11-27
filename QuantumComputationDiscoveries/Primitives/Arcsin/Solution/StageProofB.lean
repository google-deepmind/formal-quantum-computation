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

public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.StageProofA
public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.PolyBoundB

@[expose] public section

namespace QuantumComputation.Specs

namespace ArcsinImpl

open Function Operator Step

def p52Inner (q : Nat) : Bool :=
  Nat.ble 41 q && !(Nat.beq q 69 || Nat.beq q 70 || Nat.beq q 71)

def p52Pre (q : Nat) : Bool :=
  Nat.beq q 47 || s5_2PreControls.elem q

theorem s4_1PostInner_inSub :
    (s4_1PostInnerOps.all (Op102.inSub p52Inner)) = true := by decide +kernel
theorem s5_2PostInner_inSub :
    (s5_2PostInnerOps.all (Op102.inSub p52Inner)) = true := by decide +kernel
theorem s5_2PostPre_noUnquad : (s5_2PostPreOps.all Op102.noUnquad) = true := by decide +kernel
theorem s5_2PostSuf_inSub : (s5_2PostSufOps.all (Op102.inSub p52Pre)) = true := by decide +kernel

theorem checkEqList_self_all (tr1 tr2 : WTree) :
    ∀ ws : List Nat, checkEqList tr1 ws (ws.map (wGet tr2)) = true →
      (ws.all (fun q => Nat.beq (wGet tr1 q) (wGet tr2 q))) = true
  | [], _ => rfl
  | q :: qs, h => by
    cases hc : Nat.beq (wGet tr1 q) (wGet tr2 q)
    · rw [List.map_cons, checkEqList, hc, Bool.cond_false] at h; cases h
    · rw [List.map_cons, checkEqList, hc, Bool.cond_true] at h
      simp only [List.all_cons, Bool.and_eq_true, hc, true_and]
      exact checkEqList_self_all tr1 tr2 qs h

theorem p41_props :
    (∀ q ∈ rangeList 0 100, p52Inner q = true → q ≠ 49 → q ∉ [52, 81, 85, 86] → q ∈ s41KeepWires) ∧
    (∀ q ∈ rangeList 0 100, p52Pre q = true → q ≠ 86) := by
  decide +kernel

theorem p52_props :
    (∀ q ∈ rangeList 0 100, p52Inner q = true → q ≠ 47 → 25 ≤ q ∧ q ∉ [47, 69, 70, 71]) ∧
    (∀ q ∈ rangeList 0 100, p52Pre q = true → p52Inner q = true → q ∈ s52KeepWires) ∧
    (∀ q ∈ rangeList 0 25, p52Pre q = false ∧ p52Inner q = false) ∧
    (∀ q ∈ rangeList 0 41, p52Inner q = false) ∧
    (∀ q ∈ clean53Wires, p52Pre q = false ∧ p52Inner q = true ∧ 50 ≤ q) ∧
    (∀ q ∈ s52KeepWires, q ∉ [47, 70, 71] → p52Inner q = true) ∧
    (∀ q ∈ s52KeepWires, p52Pre q = true → q ∉ [47, 70, 71] →
      25 ≤ q ∧ q ∉ [47, 69, 70, 71, 86]) := by
  decide +kernel

theorem xor_xor_cancel_right' (a b : Bool) : xor (xor a b) b = a := by
  cases a <;> cases b <;> rfl

theorem xorControlsBool_suf_cancel (m3b : Fin 100 → Bool) (acc : Bool) :
    xorControlsBool m3b s5_2PreControls.reverse
      (xorControlsBool m3b s5_2PreControls acc) = acc := by
  dsimp only [s5_2PreControls, List.reverse, List.reverseAux, xorControlsBool]
  simp only [dite_eq_left (by decide : 46 < 100), dite_eq_left (by decide : 48 < 100),
    dite_eq_left (by decide : 30 < 100), dite_eq_left (by decide : 80 < 100),
    dite_eq_left (by decide : 29 < 100), dite_eq_left (by decide : 81 < 100),
    dite_eq_left (by decide : 28 < 100), dite_eq_left (by decide : 82 < 100),
    dite_eq_left (by decide : 27 < 100), dite_eq_left (by decide : 83 < 100),
    dite_eq_left (by decide : 26 < 100), dite_eq_left (by decide : 84 < 100),
    dite_eq_left (by decide : 25 < 100), dite_eq_left (by decide : 85 < 100),
    xor_xor_cancel_right']

theorem xorControlsBool_pre_piggyback {m m3b : Fin 100 → Bool} (acc : Bool)
    (h81 : m ⟨81, by decide⟩ = xor (m3b ⟨81, by decide⟩) (m3b ⟨85, by decide⟩))
    (h85 : m ⟨85, by decide⟩ = false)
    (hother : ∀ c ∈ [46, 48, 30, 80, 29, 28, 82, 27, 83, 26, 84, 25],
      ∀ hc : c < 100, m ⟨c, hc⟩ = m3b ⟨c, hc⟩) :
    xorControlsBool m s5_2PreControls acc = xorControlsBool m3b s5_2PreControls acc := by
  dsimp only [s5_2PreControls, xorControlsBool]
  simp only [dite_eq_left (by decide : 46 < 100), dite_eq_left (by decide : 48 < 100),
    dite_eq_left (by decide : 30 < 100), dite_eq_left (by decide : 80 < 100),
    dite_eq_left (by decide : 29 < 100), dite_eq_left (by decide : 81 < 100),
    dite_eq_left (by decide : 28 < 100), dite_eq_left (by decide : 82 < 100),
    dite_eq_left (by decide : 27 < 100), dite_eq_left (by decide : 83 < 100),
    dite_eq_left (by decide : 26 < 100), dite_eq_left (by decide : 84 < 100),
    dite_eq_left (by decide : 25 < 100), dite_eq_left (by decide : 85 < 100)]
  rw [hother 46 (by decide) (by decide), hother 48 (by decide) (by decide),
      hother 30 (by decide) (by decide), hother 80 (by decide) (by decide),
      hother 29 (by decide) (by decide), h81,
      hother 28 (by decide) (by decide), hother 82 (by decide) (by decide),
      hother 27 (by decide) (by decide), hother 83 (by decide) (by decide),
      hother 26 (by decide) (by decide), hother 84 (by decide) (by decide),
      hother 25 (by decide) (by decide), h85]
  generalize (xor (xor (xor (xor (xor acc (m3b ⟨46, by decide⟩)) (m3b ⟨48, by decide⟩))
    (m3b ⟨30, by decide⟩)) (m3b ⟨80, by decide⟩)) (m3b ⟨29, by decide⟩)) = x0
  generalize (m3b ⟨81, by decide⟩) = x81, (m3b ⟨28, by decide⟩) = x28, (m3b ⟨82, by decide⟩) = x82,
    (m3b ⟨27, by decide⟩) = x27, (m3b ⟨83, by decide⟩) = x83, (m3b ⟨26, by decide⟩) = x26,
    (m3b ⟨84, by decide⟩) = x84, (m3b ⟨25, by decide⟩) = x25, (m3b ⟨85, by decide⟩) = x85
  revert x0 x81 x28 x82 x27 x83 x26 x84 x25 x85; decide +kernel

theorem xorControlsBool_suf_piggyback {m m3b : Fin 100 → Bool} (acc : Bool)
    (h81 : m ⟨81, by decide⟩ = xor (m3b ⟨81, by decide⟩) (m3b ⟨85, by decide⟩))
    (h85 : m ⟨85, by decide⟩ = false)
    (hother : ∀ c ∈ [46, 48, 30, 80, 29, 28, 82, 27, 83, 26, 84, 25],
      ∀ hc : c < 100, m ⟨c, hc⟩ = m3b ⟨c, hc⟩) :
    xorControlsBool m s5_2PreControls.reverse acc =
      xorControlsBool m3b s5_2PreControls.reverse acc := by
  dsimp only [s5_2PreControls, List.reverse, List.reverseAux, xorControlsBool]
  simp only [dite_eq_left (by decide : 46 < 100), dite_eq_left (by decide : 48 < 100),
    dite_eq_left (by decide : 30 < 100), dite_eq_left (by decide : 80 < 100),
    dite_eq_left (by decide : 29 < 100), dite_eq_left (by decide : 81 < 100),
    dite_eq_left (by decide : 28 < 100), dite_eq_left (by decide : 82 < 100),
    dite_eq_left (by decide : 27 < 100), dite_eq_left (by decide : 83 < 100),
    dite_eq_left (by decide : 26 < 100), dite_eq_left (by decide : 84 < 100),
    dite_eq_left (by decide : 25 < 100), dite_eq_left (by decide : 85 < 100)]
  rw [hother 46 (by decide) (by decide), hother 48 (by decide) (by decide),
      hother 30 (by decide) (by decide), hother 80 (by decide) (by decide),
      hother 29 (by decide) (by decide), h81,
      hother 28 (by decide) (by decide), hother 82 (by decide) (by decide),
      hother 27 (by decide) (by decide), hother 83 (by decide) (by decide),
      hother 26 (by decide) (by decide), hother 84 (by decide) (by decide),
      hother 25 (by decide) (by decide), h85]
  generalize (m3b ⟨81, by decide⟩) = x81, (m3b ⟨28, by decide⟩) = x28, (m3b ⟨82, by decide⟩) = x82,
    (m3b ⟨27, by decide⟩) = x27, (m3b ⟨83, by decide⟩) = x83, (m3b ⟨26, by decide⟩) = x26,
    (m3b ⟨84, by decide⟩) = x84, (m3b ⟨25, by decide⟩) = x25, (m3b ⟨85, by decide⟩) = x85
  revert acc x81 x28 x82 x27 x83 x26 x84 x25 x85
  intro acc x81 x28 x82 x27 x83 x26 x84 x25 x85
  congr 1; congr 1; congr 1; congr 1; congr 1
  revert acc x81 x28 x82 x27 x83 x26 x84 x25 x85; decide +kernel

theorem exec_s4_1PostOps_slice {bit allM : Nat}
    {m2b m3b m41 : Fin 100 → Bool} {tr3b : WTree}
    (hI3b : ParInv bit allM (fun i => if i < 16 then allM else 0) m2b tr3b m3b)
    (h41p_cert : runParSeq allM (fun i => if i < 16 then allM else 0) [s4_1PostInnerOps] tr3b
      (fun tr => beqWTree tr (tr41pOf tr3b) &&
                 Nat.beq (wGet tr 86) 0 &&
                 Nat.beq (wGet tr 85) 0 &&
                 Nat.beq (wGet tr 52) 0 &&
                 Nat.beq (wGet tr 81) (wGet tr3b 81 ^^^ wGet tr3b 85) &&
                 checkEqList tr s41KeepWires (s41KeepWires.map (wGet tr3b))) = true)
    (hm41_agree : ∀ w : Fin 100, w.val ∉ [47, 69, 70, 71] → m41 w = m3b w)
    (hm41_47 : xorControlsBool m3b s5_2PreControls (m41 ⟨47, by decide⟩) = m3b ⟨47, by decide⟩) :
    ∃ st41Par m41p : Fin 100 → Bool,
      execList102 s4_1PostOps m41 = some m41p ∧
      ParInv bit allM (fun i => if i < 16 then allM else 0) m2b (tr41pOf tr3b) st41Par ∧
      st41Par ⟨86, by decide⟩ = false ∧
      st41Par ⟨85, by decide⟩ = false ∧
      st41Par ⟨52, by decide⟩ = false ∧
      st41Par ⟨81, by decide⟩ = xor (m3b ⟨81, by decide⟩) (m3b ⟨85, by decide⟩) ∧
      (∀ w : Fin 100, p52Inner w.val = true → w.val ∉ [52, 81, 85, 86] → st41Par w = m3b w) ∧
      m41p ⟨86, by decide⟩ = false ∧
      m41p ⟨85, by decide⟩ = false ∧
      m41p ⟨52, by decide⟩ = false ∧
      m41p ⟨81, by decide⟩ = xor (m3b ⟨81, by decide⟩) (m3b ⟨85, by decide⟩) ∧
      (∀ w : Fin 100, w.val ∉ [52, 81, 85, 86] → m41p w = m41 w) := by
  have hex_pre := execList102_xorControls (by decide : 47 < 100) s5_2PreControls m41 (by decide)
  change execList102 s5_2PostPreOps m41 = _ at hex_pre
  set st41a := Function.update m41 ⟨47, by decide⟩
    (xorControlsBool m41 s5_2PreControls (m41 ⟨47, by decide⟩))
  have hctrl_eq :
      xorControlsBool m41 s5_2PreControls (m41 ⟨47, by decide⟩) = m3b ⟨47, by decide⟩ := by
    rw [xorControlsBool_congr s5_2PreControls (m41 ⟨47, by decide⟩) (fun c hc hclt => ?_), hm41_47]
    have hnot : c ∉ [47, 69, 70, 71] := by revert c hc; decide
    exact hm41_agree ⟨c, hclt⟩ hnot
  have hm41_1_in : ∀ w : Fin 100, p52Inner w.val = true → st41a w = m3b w := by
    intro w hw
    by_cases hw47 : w = ⟨47, by decide⟩
    · subst hw47; dsimp only [st41a]; rw [Function.update_self, hctrl_eq]
    · dsimp only [st41a]; rw [Function.update_of_ne hw47]
      have hne47 : w.val ≠ 47 := fun e => hw47 (Fin.ext e)
      have hmem102 : w.val ∈ rangeList 0 100 := mem_rangeList_iff.mpr ⟨by omega, w.isLt⟩
      have ⟨_, hnot_b⟩ := p52_props.1 w.val hmem102 hw hne47
      exact hm41_agree w hnot_b
  obtain ⟨tr41', st41Par, hex_par, _, hI41p, hk41⟩ :=
    runParSeq_sound [s4_1PostInnerOps] hI3b h41p_cert
  rw [List.flatten_cons, List.flatten_nil, List.append_nil] at hex_par
  simp only [Bool.and_eq_true, Nat.beq_eq] at hk41
  obtain ⟨⟨⟨⟨⟨hbeq41, hz86⟩, hz85⟩, hz52⟩, h81_eq⟩, hkeep41⟩ := hk41
  rw [beqWTree_sound _ _ hbeq41] at hI41p hz86 hz85 hz52 h81_eq hkeep41
  obtain ⟨st41b, hex_inner, hout_inner, hin_inner⟩ :=
    execList102_congr_sub p52Inner s4_1PostInnerOps s4_1PostInner_inSub hex_par hm41_1_in
  have hm41_par_86 : st41Par ⟨86, by decide⟩ = false := by
    obtain ⟨hpw, hfm0⟩ :=
      isParWire_of_anc (fMask := fun i => if i < 16 then allM else 0) (t := 86)
        (by decide) (by decide)
    rw [hI41p.hTracked ⟨86, by decide⟩ hpw (by rw [hfm0, Nat.zero_testBit]), hz86, Nat.zero_testBit]
  have hm41_par_85 : st41Par ⟨85, by decide⟩ = false := by
    obtain ⟨hpw, hfm0⟩ :=
      isParWire_of_anc (fMask := fun i => if i < 16 then allM else 0) (t := 85)
        (by decide) (by decide)
    rw [hI41p.hTracked ⟨85, by decide⟩ hpw (by rw [hfm0, Nat.zero_testBit]), hz85, Nat.zero_testBit]
  have hm41_par_52 : st41Par ⟨52, by decide⟩ = false := by
    obtain ⟨hpw, hfm0⟩ :=
      isParWire_of_anc (fMask := fun i => if i < 16 then allM else 0) (t := 52)
        (by decide) (by decide)
    rw [hI41p.hTracked ⟨52, by decide⟩ hpw (by rw [hfm0, Nat.zero_testBit]), hz52, Nat.zero_testBit]
  have hm41_par_81 : st41Par ⟨81, by decide⟩ = xor (m3b ⟨81, by decide⟩) (m3b ⟨85, by decide⟩) := by
    obtain ⟨hpw81, hfm81⟩ :=
      isParWire_of_anc (fMask := fun i => if i < 16 then allM else 0) (t := 81)
        (by decide) (by decide)
    obtain ⟨hpw85, hfm85⟩ :=
      isParWire_of_anc (fMask := fun i => if i < 16 then allM else 0) (t := 85)
        (by decide) (by decide)
    rw [hI41p.hTracked ⟨81, by decide⟩ hpw81 (by rw [hfm81, Nat.zero_testBit]),
        h81_eq, Nat.testBit_xor,
        ← hI3b.hTracked ⟨81, by decide⟩ hpw81 (by rw [hfm81, Nat.zero_testBit]),
        ← hI3b.hTracked ⟨85, by decide⟩ hpw85 (by rw [hfm85, Nat.zero_testBit])]
  have hm41_par_keep : ∀ w : Fin 100, w.val ∈ s41KeepWires → st41Par w = m3b w := by
    intro w hw
    have hpw_fm : isParWire w.val = true ∧
        (getFMask (fun i => if i < 16 then allM else 0) w.val).testBit bit = false := by
      have hall : ∀ x ∈ s41KeepWires, (41 ≤ x ∧ x < 49) ∨ (50 ≤ x ∧ x < 100) := by decide
      rcases hall w.val hw with ⟨h41, h49⟩ | ⟨h50, h102⟩
      · refine ⟨by
          unfold isParWire
          simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
          omega, ?_⟩
        unfold getFMask
        rw [ite_eq_left h49]
        change (if w.val - 25 < 16 then allM else 0).testBit bit = false
        rw [ite_eq_right (by omega), Nat.zero_testBit]
      · obtain ⟨hpw, hfm0⟩ :=
          isParWire_of_anc (fMask := fun i => if i < 16 then allM else 0) h50 h102
        exact ⟨hpw, by rw [hfm0, Nat.zero_testBit]⟩
    have h_all := checkEqList_self_all (tr41pOf tr3b) tr3b s41KeepWires hkeep41
    have hget := Nat.beq_eq.mp (List.all_eq_true.mp h_all w.val hw)
    rw [hI41p.hTracked w hpw_fm.1 hpw_fm.2, hget, ← hI3b.hTracked w hpw_fm.1 hpw_fm.2]
  have hm41_par_in :
      ∀ w : Fin 100, p52Inner w.val = true → w.val ∉ [52, 81, 85, 86] → st41Par w = m3b w := by
    intro w hw hnot3
    by_cases hw49 : w.val = 49
    · have hfin : w = ⟨49, by decide⟩ := Fin.ext hw49
      rw [hfin, hI41p.hFree ⟨49, by decide⟩ (Or.inr rfl), ← hI3b.hFree ⟨49, by decide⟩ (Or.inr rfl)]
    · have hmem102 : w.val ∈ rangeList 0 100 := mem_rangeList_iff.mpr ⟨by omega, w.isLt⟩
      exact hm41_par_keep w (p41_props.1 w.val hmem102 hw hw49 hnot3)
  have hm41_2_not3 : ∀ w : Fin 100, w.val ∉ [52, 81, 85, 86] → st41b w = st41a w := by
    intro w hnot3
    cases hp : p52Inner w.val
    · exact hout_inner w hp
    · rw [hin_inner w hp, hm41_par_in w hp hnot3, ← hm41_1_in w hp]
  have hex_suf :=
    execList102_xorControls (by decide : 47 < 100) s5_2PreControls.reverse st41b (by decide)
  change execList102 s5_2PostSufOps st41b = _ at hex_suf
  set m41p := Function.update st41b ⟨47, by decide⟩
    (xorControlsBool st41b s5_2PreControls.reverse (st41b ⟨47, by decide⟩))
  have hm41_2_86 : st41b ⟨86, by decide⟩ = false :=
    (hin_inner ⟨86, by decide⟩ rfl).trans hm41_par_86
  have hm41_2_85 : st41b ⟨85, by decide⟩ = false :=
    (hin_inner ⟨85, by decide⟩ rfl).trans hm41_par_85
  have hm41_2_52 : st41b ⟨52, by decide⟩ = false :=
    (hin_inner ⟨52, by decide⟩ rfl).trans hm41_par_52
  have hm41_2_81 : st41b ⟨81, by decide⟩ = xor (m3b ⟨81, by decide⟩) (m3b ⟨85, by decide⟩) :=
    (hin_inner ⟨81, by decide⟩ rfl).trans hm41_par_81
  have hm41_2_47 : st41b ⟨47, by decide⟩ = m3b ⟨47, by decide⟩ :=
    (hm41_2_not3 ⟨47, by decide⟩ (by decide)).trans
      (by dsimp only [st41a]; rw [Function.update_self, hctrl_eq])
  have hm41_2_other : ∀ c ∈ [46, 48, 30, 80, 29, 28, 82, 27, 83, 26, 84, 25],
      ∀ hc : c < 100, st41b ⟨c, hc⟩ = m3b ⟨c, hc⟩ := by
    intro c hc hlt
    have hnot3 : c ∉ [52, 81, 85, 86] := by revert c hc; decide
    have hne47 : (⟨c, hlt⟩ : Fin 100) ≠ ⟨47, by decide⟩ := by
      intro e
      have := congrArg Fin.val e
      revert c hc this
      decide
    have hnot4 : c ∉ [47, 69, 70, 71] := by revert c hc; decide
    rw [hm41_2_not3 ⟨c, hlt⟩ hnot3]
    dsimp only [st41a]; rw [Function.update_of_ne hne47, hm41_agree ⟨c, hlt⟩ hnot4]
  have hsuf_47 :
      xorControlsBool st41b s5_2PreControls.reverse (st41b ⟨47, by decide⟩) =
        m41 ⟨47, by decide⟩ := by
    rw [hm41_2_47,
        xorControlsBool_suf_piggyback (m3b ⟨47, by decide⟩) hm41_2_81 hm41_2_85 hm41_2_other,
        ← hm41_47, xorControlsBool_suf_cancel]
  refine ⟨st41Par, m41p, ?_, hI41p, hm41_par_86, hm41_par_85, hm41_par_52, hm41_par_81,
    hm41_par_in, ?_, ?_, ?_, ?_, ?_⟩
  · unfold s4_1PostOps
    rw [List.append_assoc, execList102_append, hex_pre, Option.bind_some,
        execList102_append, hex_inner, Option.bind_some, hex_suf]
  · dsimp only [m41p]; rw [Function.update_of_ne (by decide), hm41_2_86]
  · dsimp only [m41p]; rw [Function.update_of_ne (by decide), hm41_2_85]
  · dsimp only [m41p]; rw [Function.update_of_ne (by decide), hm41_2_52]
  · dsimp only [m41p]; rw [Function.update_of_ne (by decide), hm41_2_81]
  · intro w hnot3
    by_cases hw47 : w = ⟨47, by decide⟩
    · subst hw47; dsimp only [m41p]; rw [Function.update_self, hsuf_47]
    · dsimp only [m41p]; rw [Function.update_of_ne hw47, hm41_2_not3 w hnot3]
      dsimp only [st41a]; exact Function.update_of_ne hw47 _ _

theorem exec_s5_2PostOps_slice {bit allM : Nat}
    {m2b m3b st41Par m52c : Fin 100 → Bool} {tr3b tr52 : WTree}
    (hI3b : ParInv bit allM (fun i => if i < 16 then allM else 0) m2b tr3b m3b)
    (hI41p : ParInv bit allM (fun i => if i < 16 then allM else 0) m2b (tr41pOf tr3b) st41Par)
    (hm41_par_86 : st41Par ⟨86, by decide⟩ = false)
    (hm41_par_85 : st41Par ⟨85, by decide⟩ = false)
    (hm41_par_52 : st41Par ⟨52, by decide⟩ = false)
    (hm41_par_81 : st41Par ⟨81, by decide⟩ = xor (m3b ⟨81, by decide⟩) (m3b ⟨85, by decide⟩))
    (hm41_par_in :
      ∀ w : Fin 100, p52Inner w.val = true → w.val ∉ [52, 81, 85, 86] → st41Par w = m3b w)
    (h52_cert : runParSeq allM (fun i => if i < 16 then allM else 0) s5_2PostInnerSeq (tr41pOf tr3b)
      (fun tr => beqWTree tr tr52 &&
                 checkZeroList tr clean53Wires &&
                 checkEqList tr s52KeepWires (s52KeepWires.map (wGet tr3b))) = true)
    (hm52c_86 : m52c ⟨86, by decide⟩ = false)
    (hm52c_85 : m52c ⟨85, by decide⟩ = false)
    (hm52c_52 : m52c ⟨52, by decide⟩ = false)
    (hm52c_81 : m52c ⟨81, by decide⟩ = xor (m3b ⟨81, by decide⟩) (m3b ⟨85, by decide⟩))
    (hm52c_agree :
      ∀ w : Fin 100, 25 ≤ w.val → w.val ∉ [47, 52, 69, 70, 71, 81, 85, 86] → m52c w = m3b w)
    (hm52c_47 : xorControlsBool m3b s5_2PreControls (m52c ⟨47, by decide⟩) = m3b ⟨47, by decide⟩) :
    ∃ m52f : Fin 100 → Bool,
      execList102 s5_2PostOps m52c = some m52f ∧
      (∀ w : Fin 100, w.val < 25 → m52f w = m52c w) ∧
      (∀ w : Fin 100, w.val ∈ [47, 69, 70, 71] → m52f w = m52c w) ∧
      (∀ w : Fin 100, 25 ≤ w.val → w.val < 41 → m52f w = m3b w) ∧
      (∀ w : Fin 100, w.val ∈ clean53Wires → m52f w = false) ∧
      (∀ w : Fin 100, w.val ∈ s52KeepWires → w.val ∉ [47, 70, 71] → m52f w = m3b w) ∧
      m52f ⟨49, by decide⟩ = m3b ⟨49, by decide⟩ := by
  have hex_pre := execList102_xorControls (by decide : 47 < 100) s5_2PreControls m52c (by decide)
  change execList102 s5_2PostPreOps m52c = _ at hex_pre
  set st52a := Function.update m52c ⟨47, by decide⟩
    (xorControlsBool m52c s5_2PreControls (m52c ⟨47, by decide⟩))
  have hm52c_other : ∀ c ∈ [46, 48, 30, 80, 29, 28, 82, 27, 83, 26, 84, 25],
      ∀ hc : c < 100, m52c ⟨c, hc⟩ = m3b ⟨c, hc⟩ := by
    intro c hc hlt
    have hge25 : 25 ≤ c ∧ c ∉ [47, 52, 69, 70, 71, 81, 85, 86] := by revert c hc; decide
    exact hm52c_agree ⟨c, hlt⟩ hge25.1 hge25.2
  have hctrl_eq :
      xorControlsBool m52c s5_2PreControls (m52c ⟨47, by decide⟩) = m3b ⟨47, by decide⟩ := by
    rw [xorControlsBool_pre_piggyback (m52c ⟨47, by decide⟩) hm52c_81 hm52c_85 hm52c_other,
      hm52c_47]
  have hm52_1_in : ∀ w : Fin 100, p52Inner w.val = true → st52a w = st41Par w := by
    intro w hw
    by_cases hw47 : w = ⟨47, by decide⟩
    · subst hw47
      dsimp only [st52a]
      rw [Function.update_self, hctrl_eq, ← hm41_par_in ⟨47, by decide⟩ rfl (by decide)]
    · dsimp only [st52a]; rw [Function.update_of_ne hw47]
      by_cases hw86 : w = ⟨86, by decide⟩
      · subst hw86; rw [hm52c_86, hm41_par_86]
      · by_cases hw85 : w = ⟨85, by decide⟩
        · subst hw85; rw [hm52c_85, hm41_par_85]
        · by_cases hw81 : w = ⟨81, by decide⟩
          · subst hw81; rw [hm52c_81, hm41_par_81]
          · by_cases hw52 : w = ⟨52, by decide⟩
            · subst hw52; rw [hm52c_52, hm41_par_52]
            · have hne47 : w.val ≠ 47 := fun e => hw47 (Fin.ext e)
              have hne86 : w.val ≠ 86 := fun e => hw86 (Fin.ext e)
              have hne85 : w.val ≠ 85 := fun e => hw85 (Fin.ext e)
              have hne81 : w.val ≠ 81 := fun e => hw81 (Fin.ext e)
              have hne52 : w.val ≠ 52 := fun e => hw52 (Fin.ext e)
              have hmem102 : w.val ∈ rangeList 0 100 := mem_rangeList_iff.mpr ⟨by omega, w.isLt⟩
              have ⟨hge25, hnot_b⟩ := p52_props.1 w.val hmem102 hw hne47
              have hnot3 : w.val ∉ [52, 81, 85, 86] := by
                intro hm
                rcases (by simpa using hm : w.val = 52 ∨ w.val = 81 ∨ w.val = 85 ∨ w.val = 86)
                  with h | h | h | h
                · exact hne52 h
                · exact hne81 h
                · exact hne85 h
                · exact hne86 h
              have hnot7 : w.val ∉ [47, 52, 69, 70, 71, 81, 85, 86] := by
                intro hm
                rcases (by simpa using hm :
                    w.val = 47 ∨ w.val = 52 ∨ w.val = 69 ∨ w.val = 70 ∨
                    w.val = 71 ∨ w.val = 81 ∨ w.val = 85 ∨ w.val = 86)
                  with h | h | h | h | h | h | h | h
                · exact hnot_b (by simp [h])
                · exact hne52 h
                · exact hnot_b (by simp [h])
                · exact hnot_b (by simp [h])
                · exact hnot_b (by simp [h])
                · exact hne81 h
                · exact hne85 h
                · exact hne86 h
              rw [hm52c_agree w hge25 hnot7, ← hm41_par_in w hw hnot3]
  obtain ⟨tr52', st52Par, hex_par, _, hI52, hk52⟩ := runParSeq_sound s5_2PostInnerSeq hI41p h52_cert
  change execList102 s5_2PostInnerOps st41Par = some st52Par at hex_par
  simp only [Bool.and_eq_true] at hk52
  obtain ⟨⟨hbeq52, hz52⟩, hkeep52⟩ := hk52
  rw [beqWTree_sound _ _ hbeq52] at hI52 hz52 hkeep52
  obtain ⟨st52b, hex_inner, hout_inner, hin_inner⟩ :=
    execList102_congr_sub p52Inner s5_2PostInnerOps s5_2PostInner_inSub hex_par hm52_1_in
  have hm52_par_keep : ∀ w : Fin 100, w.val ∈ s52KeepWires → st52Par w = m3b w := by
    intro w hw
    have hpw_fm : isParWire w.val = true ∧
        (getFMask (fun i => if i < 16 then allM else 0) w.val).testBit bit = false := by
      have hall : ∀ x ∈ s52KeepWires, (41 ≤ x ∧ x < 49) ∨ (50 ≤ x ∧ x < 100) := by decide
      rcases hall w.val hw with ⟨h41, h49⟩ | ⟨h50, h102⟩
      · refine ⟨by
          unfold isParWire
          simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
          omega, ?_⟩
        unfold getFMask
        rw [ite_eq_left h49]
        change (if w.val - 25 < 16 then allM else 0).testBit bit = false
        rw [ite_eq_right (by omega), Nat.zero_testBit]
      · obtain ⟨hpw, hfm0⟩ :=
          isParWire_of_anc (fMask := fun i => if i < 16 then allM else 0) h50 h102
        exact ⟨hpw, by rw [hfm0, Nat.zero_testBit]⟩
    have h_all := checkEqList_self_all tr52 tr3b s52KeepWires hkeep52
    have hget := Nat.beq_eq.mp (List.all_eq_true.mp h_all w.val hw)
    rw [hI52.hTracked w hpw_fm.1 hpw_fm.2, hget, ← hI3b.hTracked w hpw_fm.1 hpw_fm.2]
  have hm52_2_pre : ∀ w : Fin 100, p52Pre w.val = true → st52b w = m3b w := by
    intro w hw
    cases hp : p52Inner w.val
    · rw [hout_inner w hp]
      have hne47 : w ≠ ⟨47, by decide⟩ := fun e => by subst e; cases hp
      dsimp only [st52a]; rw [Function.update_of_ne hne47]
      have hge25 : 25 ≤ w.val ∧ w.val ∉ [47, 52, 69, 70, 71, 81, 85, 86] := by
        have hmem102 : w.val ∈ rangeList 0 100 := mem_rangeList_iff.mpr ⟨by omega, w.isLt⟩
        revert w hmem102 hw hp; decide
      exact hm52c_agree w hge25.1 hge25.2
    · have hmem102 : w.val ∈ rangeList 0 100 := mem_rangeList_iff.mpr ⟨by omega, w.isLt⟩
      have hkeep : w.val ∈ s52KeepWires := p52_props.2.1 w.val hmem102 hw hp
      rw [hin_inner w hp, hm52_par_keep w hkeep]
  have hex_suf :=
    execList102_xorControls (by decide : 47 < 100) s5_2PreControls.reverse st52b (by decide)
  change execList102 s5_2PostSufOps st52b = _ at hex_suf
  set m52f := Function.update st52b ⟨47, by decide⟩
    (xorControlsBool st52b s5_2PreControls.reverse (st52b ⟨47, by decide⟩))
  have hsuf_47 :
      xorControlsBool st52b s5_2PreControls.reverse (st52b ⟨47, by decide⟩) =
        m52c ⟨47, by decide⟩ := by
    have hm52_2_47 : st52b ⟨47, by decide⟩ = m3b ⟨47, by decide⟩ := hm52_2_pre ⟨47, by decide⟩ rfl
    have hcongr : xorControlsBool st52b s5_2PreControls.reverse (m3b ⟨47, by decide⟩) =
        xorControlsBool m3b s5_2PreControls.reverse (m3b ⟨47, by decide⟩) := by
      refine xorControlsBool_congr s5_2PreControls.reverse (m3b ⟨47, by decide⟩)
        (fun c hc hclt => ?_)
      have hpre : p52Pre c = true := by revert c hc; decide
      exact hm52_2_pre ⟨c, hclt⟩ hpre
    rw [hm52_2_47, hcongr, ← hm52c_47, xorControlsBool_suf_cancel]
  refine ⟨m52f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold s5_2PostOps
    rw [List.append_assoc, execList102_append, hex_pre, Option.bind_some,
        execList102_append, hex_inner, Option.bind_some, hex_suf]
  · intro w hw
    have hmem25 : w.val ∈ rangeList 0 25 := mem_rangeList_iff.mpr ⟨by omega, hw⟩
    have ⟨_, hp2⟩ := p52_props.2.2.1 w.val hmem25
    have hne47 : w ≠ ⟨47, by decide⟩ := fun e => by have := congrArg Fin.val e; dsimp at this; omega
    dsimp only [m52f]; rw [Function.update_of_ne hne47, hout_inner w hp2]
    dsimp only [st52a]; exact Function.update_of_ne hne47 _ _
  · intro w hw
    rcases (by simpa using hw : w.val = 47 ∨ w.val = 69 ∨ w.val = 70 ∨ w.val = 71) with
      h47 | h69 | h70 | h71
    · have hfin : w = ⟨47, by decide⟩ := Fin.ext h47
      subst hfin; dsimp only [m52f]; rw [Function.update_self, hsuf_47]
    · have hne47 : w ≠ ⟨47, by decide⟩ := fun e => by
        have := congrArg Fin.val e; dsimp at this; omega
      have hp2 : p52Inner w.val = false := by rw [h69]; rfl
      dsimp only [m52f]; rw [Function.update_of_ne hne47, hout_inner w hp2]
      dsimp only [st52a]; exact Function.update_of_ne hne47 _ _
    · have hne47 : w ≠ ⟨47, by decide⟩ := fun e => by
        have := congrArg Fin.val e; dsimp at this; omega
      have hp2 : p52Inner w.val = false := by rw [h70]; rfl
      dsimp only [m52f]; rw [Function.update_of_ne hne47, hout_inner w hp2]
      dsimp only [st52a]; exact Function.update_of_ne hne47 _ _
    · have hne47 : w ≠ ⟨47, by decide⟩ := fun e => by
        have := congrArg Fin.val e; dsimp at this; omega
      have hp2 : p52Inner w.val = false := by rw [h71]; rfl
      dsimp only [m52f]; rw [Function.update_of_ne hne47, hout_inner w hp2]
      dsimp only [st52a]; exact Function.update_of_ne hne47 _ _
  · intro w hw25 hw41
    have hne47 : w ≠ ⟨47, by decide⟩ := fun e => by have := congrArg Fin.val e; dsimp at this; omega
    have hnot_b : w.val ∉ [47, 52, 69, 70, 71, 81, 85, 86] := by simp; omega
    have hmem41 : w.val ∈ rangeList 0 41 := mem_rangeList_iff.mpr ⟨by omega, hw41⟩
    have hp2 : p52Inner w.val = false := p52_props.2.2.2.1 w.val hmem41
    dsimp only [m52f]; rw [Function.update_of_ne hne47, hout_inner w hp2]
    dsimp only [st52a]; rw [Function.update_of_ne hne47]
    exact hm52c_agree w hw25 hnot_b
  · intro w hw
    have ⟨hp1, hp2, hbnd1⟩ := p52_props.2.2.2.2.1 w.val hw
    have hne47 : w ≠ ⟨47, by decide⟩ := fun e => by subst e; cases hp1
    obtain ⟨hpw, hfm0⟩ :=
      isParWire_of_anc (fMask := fun i => if i < 16 then allM else 0) hbnd1 w.isLt
    dsimp only [m52f]; rw [Function.update_of_ne hne47, hin_inner w hp2,
        hI52.hTracked w hpw (by rw [hfm0, Nat.zero_testBit]),
        checkZeroList_sound clean53Wires hz52 w.val hw, Nat.zero_testBit]
  · intro w hw hnot3
    have hne47 : w ≠ ⟨47, by decide⟩ := fun e => by
      have hval : w.val = 47 := congrArg Fin.val e
      exact hnot3 (by simp [hval])
    have hp2 : p52Inner w.val = true := p52_props.2.2.2.2.2.1 w.val hw hnot3
    dsimp only [m52f]; rw [Function.update_of_ne hne47, hin_inner w hp2, hm52_par_keep w hw]
  · dsimp only [m52f]; rw [Function.update_of_ne (by decide), hin_inner ⟨49, by decide⟩ rfl,
        hI52.hFree ⟨49, by decide⟩ (Or.inr rfl), ← hI3b.hFree ⟨49, by decide⟩ (Or.inr rfl)]







-- ============================================================================
-- Section 3: Glue Connecting Stages 1, 2, 3, 4, 5, 6, 7 & Leaf Certificates
-- ============================================================================

theorem xor_xor_cancel_right (a b : Bool) : xor (xor a b) b = a := by
  cases a <;> cases b <;> rfl

theorem xorControlsBool_mask47_s41 (m3b : Fin 100 → Bool) :
    xorControlsBool m3b s5_2PreControls
      (evalSymMask 120 (buildSymEnv 120 m3b defs_4_1) mask47_s41) = m3b ⟨47, by decide⟩ := by
  have hN : 103 ≤ 120 := by decide
  have hm : mask47_s41 =
      ((((((((((((((wMask 47 ^^^ wMask 85) ^^^ wMask 25) ^^^ wMask 84) ^^^ wMask 26) ^^^
        wMask 83) ^^^ wMask 27) ^^^ wMask 82) ^^^ wMask 28) ^^^ wMask 81) ^^^
        wMask 29) ^^^ wMask 80) ^^^ wMask 30) ^^^ wMask 48) ^^^ wMask 46) := rfl
  rw [hm]
  repeat rw [evalSymMask_xor]
  rw [evalSymMask_wMask hN (by decide : 47 < 100),
      evalSymMask_wMask hN (by decide : 46 < 100),
      evalSymMask_wMask hN (by decide : 48 < 100),
      evalSymMask_wMask hN (by decide : 30 < 100),
      evalSymMask_wMask hN (by decide : 80 < 100),
      evalSymMask_wMask hN (by decide : 29 < 100),
      evalSymMask_wMask hN (by decide : 81 < 100),
      evalSymMask_wMask hN (by decide : 28 < 100),
      evalSymMask_wMask hN (by decide : 82 < 100),
      evalSymMask_wMask hN (by decide : 27 < 100),
      evalSymMask_wMask hN (by decide : 83 < 100),
      evalSymMask_wMask hN (by decide : 26 < 100),
      evalSymMask_wMask hN (by decide : 84 < 100),
      evalSymMask_wMask hN (by decide : 25 < 100),
      evalSymMask_wMask hN (by decide : 85 < 100)]
  dsimp only [s5_2PreControls, xorControlsBool]
  simp only [dite_eq_left (by decide : 46 < 100), dite_eq_left (by decide : 48 < 100),
    dite_eq_left (by decide : 30 < 100), dite_eq_left (by decide : 80 < 100),
    dite_eq_left (by decide : 29 < 100), dite_eq_left (by decide : 81 < 100),
    dite_eq_left (by decide : 28 < 100), dite_eq_left (by decide : 82 < 100),
    dite_eq_left (by decide : 27 < 100), dite_eq_left (by decide : 83 < 100),
    dite_eq_left (by decide : 26 < 100), dite_eq_left (by decide : 84 < 100),
    dite_eq_left (by decide : 25 < 100), dite_eq_left (by decide : 85 < 100),
    xor_xor_cancel_right]

theorem cond_one_zero_eq_toNat (b : Bool) : cond b 1 0 = b.toNat := by
  cases b <;> rfl

theorem sumBits_succ_left : ∀ (M : Nat) (g : Nat → Bool),
    sumBits (M + 1) g = (g 0).toNat + 2 * sumBits M (fun k => g (1 + k))
  | 0, g => by simp [sumBits]
  | M + 1, g => by
    rw [sumBits_succ (M + 1), sumBits_succ_left M g, sumBits_succ M (fun k => g (1 + k)),
        pow_succ']
    have hM : 1 + M = M + 1 := by omega
    rw [hM]
    ring

theorem targVal_rangeList_eq_sliceVal (m : Fin 100 → Bool) :
    ∀ (M sout : Nat),
      targVal (rangeList sout M) m = sliceVal sout M m
  | 0, _ => rfl
  | M + 1, sout => by
    dsimp only [rangeList, targVal]
    rw [targVal_rangeList_eq_sliceVal m M (sout + 1)]
    conv_rhs => unfold sliceVal; rw [sumBits_succ_left]
    have h0 : cond (if h : sout < 100 then m ⟨sout, h⟩ else false) 1 0 =
        (if h : sout + 0 < 100 then m ⟨sout + 0, h⟩ else false).toNat := by
      rw [Nat.add_zero]
      exact cond_one_zero_eq_toNat _
    have h1 : sliceVal (sout + 1) M m =
        sumBits M (fun k => if h : sout + (1 + k) < 100 then m ⟨sout + (1 + k), h⟩ else false) := by
      unfold sliceVal
      refine sumBits_congr fun k _ => ?_
      have heq : sout + 1 + k = sout + (1 + k) := by omega
      simp only [heq]
    rw [h0, h1]

theorem targVal_z_w_eq_outVal102 (m : Fin 100 → Bool) :
    targVal z_w m = outVal102 m :=
  targVal_rangeList_eq_sliceVal m 25 0

theorem ParInv.m3b_tracked {bit allM : Nat} {m2b m3b : Fin 100 → Bool} {tr3b : WTree}
    (hI3b : ParInv bit allM (fun i => if i < 16 then allM else 0) m2b tr3b m3b)
    (q : Nat) (hq1 : 41 ≤ q) (hq2 : q < 100) (hq49 : q ≠ 49) :
    m3b ⟨q, hq2⟩ = (wGet tr3b q).testBit bit := by
  have hpw : isParWire q = true := by
    unfold isParWire; simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; omega
  have hfm : (getFMask (fun i => if i < 16 then allM else 0) q).testBit bit = false := by
    unfold getFMask
    split_ifs with hlt49
    · change (if q - 25 < 16 then allM else 0).testBit bit = false
      rw [ite_eq_right (by omega), Nat.zero_testBit]
    · exact Nat.zero_testBit bit
  exact hI3b.hTracked ⟨q, hq2⟩ hpw hfm

def modW54 : List Nat := [47, 69, 52, 97, 72, 56, 98, 99]
def keepW54 : List Nat := (rangeList 41 8 ++ rangeList 50 50).filter (fun w => !modW54.elem w)

theorem keepW54_props :
    (∀ q ∈ rangeList 41 8 ++ rangeList 50 50, q ∈ modW54 ∨ q ∈ keepW54) ∧
    (∀ q ∈ keepW54, q ∉ [70, 71] →
      q ∉ out_5_3 ++ extra_5_3.map Prod.fst ∧
      (q ∈ clean53Wires ∨ (q ∈ s52KeepWires ∧ q ∉ [47, 70, 71]))) ∧
    (∀ q ∈ rangeList 0 100, q ∉ badW_41_53 →
      (25 ≤ q ∧ q < 41) ∨ (q ∈ s52KeepWires ∧ q ∉ [47, 70, 71])) ∧
    (∀ q ∈ clean_5_3, q ∈ clean53Wires) := by
  decide +kernel

theorem u18_exp52_eq (b1 b2 b3 b4 b5 : Bool) :
    let t24 := b2 && b4
    let t34 := b3 && b4
    let t25 := b2 && b5
    let t35 := b3 && b5
    let t45 := b4 && b5
    xor (xor (xor t25 t35) t45)
      (b1 && xor (xor (xor (xor (xor (xor (xor (xor true b2) b3) t24) t34) b5) t25) t35) t45) =
    u18_q0 b1 b2 b3 b4 b5 := by
  revert b1 b2 b3 b4 b5; decide +kernel

theorem u18_exp97_eq (b2 b3 b4 b5 : Bool) :
    let t24 := b2 && b4
    let t34 := b3 && b4
    let t45 := b4 && b5
    xor (xor (xor (xor (xor true b3) b4) t24) t34) t45 =
    u18_q19_0 b2 b3 b4 b5 := by
  revert b2 b3 b4 b5; decide +kernel

theorem u18_exp72_eq (b1 b2 b3 b4 b5 : Bool) :
    let t45 := b4 && b5
    let t245 := b2 && t45
    let p12 := b1 && xor t45 t245
    xor (xor (xor (xor true b3) t45) t245) p12 =
    u18_q19_1 b1 b2 b3 b4 b5 := by
  revert b1 b2 b3 b4 b5; decide +kernel

theorem u18_exp56_eq (b1 b2 b3 b4 b5 : Bool) :
    let t45 := b4 && b5
    let t245 := b2 && t45
    let p12 := b1 && xor t45 t245
    xor (xor (xor (xor true b3) b4) t245) p12 =
    u18_q19_2 b1 b2 b3 b4 b5 := by
  revert b1 b2 b3 b4 b5; decide +kernel

theorem u18_exp98_eq (b3 b4 b5 : Bool) :
    let t34 := b3 && b4
    let t45 := b4 && b5
    xor (xor (xor (xor (xor true b3) b4) t34) b5) t45 =
    u18_q19_3 b3 b4 b5 := by
  revert b3 b4 b5; decide +kernel

theorem u18_exp99_eq (b3 b4 b5 : Bool) :
    let t34 := b3 && b4
    let t35 := b3 && b5
    let t45 := b4 && b5
    xor (xor (xor (xor (xor (xor true b3) b4) t34) b5) t35) t45 =
    u18_q19_4 b3 b4 b5 := by
  revert b3 b4 b5; decide +kernel

theorem checkTrS54In_sound {bit allM : Nat}
    {m2b m3b st41Par m52f m53 : Fin 100 → Bool} {tr3b tr52 tr54In : WTree}
    (hI3b : ParInv bit allM (fun i => if i < 16 then allM else 0) m2b tr3b m3b)
    (hI41p : ParInv bit allM (fun i => if i < 16 then allM else 0) m2b (tr41pOf tr3b) st41Par)
    (h52_cert : runParSeq allM (fun i => if i < 16 then allM else 0) s5_2PostInnerSeq (tr41pOf tr3b)
      (fun tr => beqWTree tr tr52 &&
                 checkZeroList tr clean53Wires &&
                 checkEqList tr s52KeepWires (s52KeepWires.map (wGet tr3b))) = true)
    (htr54 : checkTrS54In allM tr3b tr52 tr54In = true)
    (hm52f_25_41 : ∀ w : Fin 100, 25 ≤ w.val → w.val < 41 → m52f w = m3b w)
    (hm52f_clean : ∀ w : Fin 100, w.val ∈ clean53Wires → m52f w = false)
    (hm52f_keep : ∀ w : Fin 100, w.val ∈ s52KeepWires → w.val ∉ [47, 70, 71] → m52f w = m3b w)
    (hm52f_49 : m52f ⟨49, by decide⟩ = m3b ⟨49, by decide⟩)
    (hnon53 : ∀ w : Fin 100, w.val ∉ out_5_3 ++ extra_5_3.map Prod.fst → m53 w = m52f w)
    (hbit47 : m53 ⟨47, by decide⟩ = bLo4InitBit0 m3b)
    (hbit69 : m53 ⟨69, by decide⟩ = bLo4InitBit1 m3b)
    (hbit70 : m53 ⟨70, by decide⟩ = m3b ⟨70, by decide⟩)
    (hbit71 : m53 ⟨71, by decide⟩ = m3b ⟨71, by decide⟩)
    (hm52 : m53 ⟨52, by decide⟩ =
      u18_q0 (m3b ⟨45, by decide⟩) (m3b ⟨46, by decide⟩) (m3b ⟨48, by decide⟩)
        (m3b ⟨58, by decide⟩) (m3b ⟨47, by decide⟩))
    (hm97 : m53 ⟨97, by decide⟩ =
      u18_q19_0 (m3b ⟨46, by decide⟩) (m3b ⟨48, by decide⟩) (m3b ⟨58, by decide⟩)
        (m3b ⟨47, by decide⟩))
    (hm72 : m53 ⟨72, by decide⟩ =
      u18_q19_1 (m3b ⟨45, by decide⟩) (m3b ⟨46, by decide⟩) (m3b ⟨48, by decide⟩)
        (m3b ⟨58, by decide⟩) (m3b ⟨47, by decide⟩))
    (hm56 : m53 ⟨56, by decide⟩ =
      u18_q19_2 (m3b ⟨45, by decide⟩) (m3b ⟨46, by decide⟩) (m3b ⟨48, by decide⟩)
        (m3b ⟨58, by decide⟩) (m3b ⟨47, by decide⟩))
    (hm98 : m53 ⟨98, by decide⟩ =
      u18_q19_3 (m3b ⟨48, by decide⟩) (m3b ⟨58, by decide⟩) (m3b ⟨47, by decide⟩))
    (hm99 : m53 ⟨99, by decide⟩ =
      u18_q19_4 (m3b ⟨48, by decide⟩) (m3b ⟨58, by decide⟩) (m3b ⟨47, by decide⟩)) :
    ParInv bit allM (fun i => if i < 16 then allM else 0) m2b tr54In m53 := by
  obtain ⟨tr52', st52Par, _, _, _, hk52⟩ := runParSeq_sound s5_2PostInnerSeq hI41p h52_cert
  simp only [Bool.and_eq_true] at hk52
  obtain ⟨⟨hbeq52, hz52⟩, hkeep52⟩ := hk52
  rw [beqWTree_sound _ _ hbeq52] at hz52 hkeep52
  unfold checkTrS54In at htr54
  dsimp only at htr54
  simp only [Bool.and_eq_true] at htr54
  obtain ⟨⟨hwf54, hmod54⟩, hkeep54⟩ := htr54
  change checkEqList tr54In keepW54 (keepW54.map (wGet tr52)) = true at hkeep54
  refine ⟨checkWTreeWF_sound 7 tr54In hwf54, hI3b.hAll, ?_, ?_⟩
  · intro w hw
    rcases hw with ⟨h25, h49, hfm⟩ | h49_eq
    · by_cases hlt16 : w.val - 25 < 16
      · have hnot : w.val ∉ out_5_3 ++ extra_5_3.map Prod.fst := by
          have hlt41 : w.val < 41 := by omega
          clear h49 hfm hlt16
          revert w h25 hlt41; decide +kernel
        rw [hnon53 w hnot, hm52f_25_41 w h25 (by omega),
            hI3b.hFree w (Or.inl ⟨h25, h49, by rw [ite_eq_left hlt16]; exact hI3b.hAll⟩)]
      · rw [ite_eq_right hlt16, Nat.zero_testBit] at hfm; cases hfm
    · have hfin : w = ⟨49, by decide⟩ := Fin.ext h49_eq
      rw [hfin, hnon53 ⟨49, by decide⟩ (by decide), hm52f_49,
        hI3b.hFree ⟨49, by decide⟩ (Or.inr rfl)]
  · intro q hq hfm_q
    obtain ⟨hq25, hq102, hq_ne49, hq_cases⟩ := isParWire_bounds hq
    have hq_ge41 : 41 ≤ q.val := by
      rcases hq_cases with hq49_lt | hq50_le
      · unfold getFMask at hfm_q
        rw [ite_eq_left hq49_lt] at hfm_q
        dsimp only at hfm_q
        by_cases hlt16 : q.val - 25 < 16
        · rw [ite_eq_left hlt16, hI3b.hAll] at hfm_q; cases hfm_q
        · omega
      · omega
    have hq_mem : q.val ∈ rangeList 41 8 ++ rangeList 50 50 := by
      rw [List.mem_append, mem_rangeList_iff, mem_rangeList_iff]
      omega
    have htr := fun w (hw1 : 41 ≤ w) (hw2 : w < 100) (hw3 : w ≠ 49) =>
      (hI3b.m3b_tracked w hw1 hw2 hw3).symm
    rcases keepW54_props.1 q.val hq_mem with hmod | hkeep
    · simp only [modW54, List.mem_cons, List.not_mem_nil, or_false] at hmod
      rcases hmod with h47 | h69 | h52 | h97 | h72 | h56 | h98 | h99
      · have hfin : q = ⟨47, by decide⟩ := Fin.ext h47
        have hw := checkEqList_sound _ _ hmod54 0 47 _ rfl rfl
        rw [hfin, hbit47]; dsimp only; rw [hw]
        unfold bLo4InitBit0
        simp only [Nat.testBit_xor,
          htr 46 (by decide) (by decide) (by decide),
          htr 48 (by decide) (by decide) (by decide),
          htr 47 (by decide) (by decide) (by decide)]
      · have hfin : q = ⟨69, by decide⟩ := Fin.ext h69
        have hw := checkEqList_sound _ _ hmod54 1 69 _ rfl rfl
        rw [hfin, hbit69]; dsimp only; rw [hw]
        unfold bLo4InitBit1
        simp only [Nat.testBit_xor,
          htr 46 (by decide) (by decide) (by decide),
          htr 47 (by decide) (by decide) (by decide),
          htr 41 (by decide) (by decide) (by decide),
          htr 45 (by decide) (by decide) (by decide),
          htr 72 (by decide) (by decide) (by decide),
          htr 75 (by decide) (by decide) (by decide),
          htr 77 (by decide) (by decide) (by decide),
          htr 78 (by decide) (by decide) (by decide),
          htr 86 (by decide) (by decide) (by decide),
          htr 89 (by decide) (by decide) (by decide),
          htr 93 (by decide) (by decide) (by decide)]
      · have hfin : q = ⟨52, by decide⟩ := Fin.ext h52
        have hw := checkEqList_sound _ _ hmod54 2 52 _ rfl rfl
        rw [hfin, hm52]; dsimp only; rw [hw]
        simp only [Nat.testBit_xor, Nat.testBit_and, hI3b.hAll,
          htr 45 (by decide) (by decide) (by decide),
          htr 46 (by decide) (by decide) (by decide),
          htr 48 (by decide) (by decide) (by decide),
          htr 58 (by decide) (by decide) (by decide),
          htr 47 (by decide) (by decide) (by decide)]
        exact (u18_exp52_eq _ _ _ _ _).symm
      · have hfin : q = ⟨97, by decide⟩ := Fin.ext h97
        have hw := checkEqList_sound _ _ hmod54 3 97 _ rfl rfl
        rw [hfin, hm97]; dsimp only; rw [hw]
        simp only [Nat.testBit_xor, Nat.testBit_and, hI3b.hAll,
          htr 46 (by decide) (by decide) (by decide),
          htr 48 (by decide) (by decide) (by decide),
          htr 58 (by decide) (by decide) (by decide),
          htr 47 (by decide) (by decide) (by decide)]
        exact (u18_exp97_eq _ _ _ _).symm
      · have hfin : q = ⟨72, by decide⟩ := Fin.ext h72
        have hw := checkEqList_sound _ _ hmod54 4 72 _ rfl rfl
        rw [hfin, hm72]; dsimp only; rw [hw]
        simp only [Nat.testBit_xor, Nat.testBit_and, hI3b.hAll,
          htr 45 (by decide) (by decide) (by decide),
          htr 46 (by decide) (by decide) (by decide),
          htr 48 (by decide) (by decide) (by decide),
          htr 58 (by decide) (by decide) (by decide),
          htr 47 (by decide) (by decide) (by decide)]
        exact (u18_exp72_eq _ _ _ _ _).symm
      · have hfin : q = ⟨56, by decide⟩ := Fin.ext h56
        have hw := checkEqList_sound _ _ hmod54 5 56 _ rfl rfl
        rw [hfin, hm56]; dsimp only; rw [hw]
        simp only [Nat.testBit_xor, Nat.testBit_and, hI3b.hAll,
          htr 45 (by decide) (by decide) (by decide),
          htr 46 (by decide) (by decide) (by decide),
          htr 48 (by decide) (by decide) (by decide),
          htr 58 (by decide) (by decide) (by decide),
          htr 47 (by decide) (by decide) (by decide)]
        exact (u18_exp56_eq _ _ _ _ _).symm
      · have hfin : q = ⟨98, by decide⟩ := Fin.ext h98
        have hw := checkEqList_sound _ _ hmod54 6 98 _ rfl rfl
        rw [hfin, hm98]; dsimp only; rw [hw]
        simp only [Nat.testBit_xor, Nat.testBit_and, hI3b.hAll,
          htr 48 (by decide) (by decide) (by decide),
          htr 58 (by decide) (by decide) (by decide),
          htr 47 (by decide) (by decide) (by decide)]
        exact (u18_exp98_eq _ _ _).symm
      · have hfin : q = ⟨99, by decide⟩ := Fin.ext h99
        have hw := checkEqList_sound _ _ hmod54 7 99 _ rfl rfl
        rw [hfin, hm99]; dsimp only; rw [hw]
        simp only [Nat.testBit_xor, Nat.testBit_and, hI3b.hAll,
          htr 48 (by decide) (by decide) (by decide),
          htr 58 (by decide) (by decide) (by decide),
          htr 47 (by decide) (by decide) (by decide)]
        exact (u18_exp99_eq _ _ _).symm
    · have h54_eq_52 : wGet tr54In q.val = wGet tr52 q.val :=
        Nat.beq_eq.mp
          (List.all_eq_true.mp (checkEqList_self_all tr54In tr52 keepW54 hkeep54) q.val hkeep)
      rw [h54_eq_52]
      by_cases h70_71 : q.val ∈ [70, 71]
      · rcases (by simpa using h70_71 : q.val = 70 ∨ q.val = 71) with h70 | h71
        · have hfin : q = ⟨70, by decide⟩ := Fin.ext h70
          have h52_3b : wGet tr52 70 = wGet tr3b 70 :=
            Nat.beq_eq.mp
              (List.all_eq_true.mp (checkEqList_self_all tr52 tr3b s52KeepWires hkeep52)
                70 (by decide))
          rw [hfin, hbit70]; dsimp only; rw [h52_3b, ← htr 70 (by decide) (by decide) (by decide)]
        · have hfin : q = ⟨71, by decide⟩ := Fin.ext h71
          have h52_3b : wGet tr52 71 = wGet tr3b 71 :=
            Nat.beq_eq.mp
              (List.all_eq_true.mp (checkEqList_self_all tr52 tr3b s52KeepWires hkeep52)
                71 (by decide))
          rw [hfin, hbit71]; dsimp only; rw [h52_3b, ← htr 71 (by decide) (by decide) (by decide)]
      · obtain ⟨hnot_out53, hcl_or_keep⟩ := keepW54_props.2.1 q.val hkeep h70_71
        rw [hnon53 q hnot_out53]
        rcases hcl_or_keep with hcl | ⟨hkp, hnot3⟩
        · rw [hm52f_clean q hcl, checkZeroList_sound clean53Wires hz52 q.val hcl, Nat.zero_testBit]
        · have h52_3b : wGet tr52 q.val = wGet tr3b q.val :=
            Nat.beq_eq.mp
              (List.all_eq_true.mp (checkEqList_self_all tr52 tr3b s52KeepWires hkeep52)
                q.val hkp)
          rw [hm52f_keep q hkp hnot3, h52_3b, ← htr q.val hq_ge41 hq102 hq_ne49]

def checkLeafMidConst (bit s4 : Nat) (tr3a tr3b : WTree) (L : Leaf25) : Bool :=
  let tb := fun q => (wGet tr3b q).testBit bit
  let b_res19 := getBits bit (bHi19Wires.map (wGet tr3a)) 0 19
  let bLo4_0 := xor (xor (tb 46) (tb 48)) (tb 47)
  let bLo4_1 := xor (xor (xor (xor (xor (xor (xor (xor (xor (xor (tb 46) (tb 47))
    (tb 41)) (tb 45)) (tb 72)) (tb 75)) (tb 77)) (tb 78)) (tb 86)) (tb 89)) (tb 93)
  let bLo4 :=
    (cond bLo4_0 1 0) +
      2 * ((cond bLo4_1 1 0) + 2 * ((cond (tb 70) 1 0) + 2 * (cond (tb 71) 1 0)))
  let u18v := u18_val (tb 44) (tb 45) (tb 46) (tb 48) (tb 58) (tb 47)
  let q19_4 := u18_q19_4 (tb 48) (tb 58) (tb 47)
  Nat.beq L.s4 s4 &&
  ((rangeList 0 15).all fun b => tb (72 + b) == L.kv.testBit b) &&
  (xor (xor (xor (xor (tb 44 && xor (tb 46) (tb 41)) (tb 41)) (tb 48)) (tb 58)) true ==
    L.lv.testBit 0) &&
  ((rangeList 0 7).all fun j => tb (87 + j) == L.lv.testBit (1 + j)) &&
  Nat.beq (16 * b_res19 + 4194304 * u18v + bLo4 + slopeConst27 L.kv + 1024)
    (L.b_base + 536870912 * (cond q19_4 1 0))

theorem checkLeafMidConst_sound {bit allM s4 : Nat} {m1 m2b m3b : Fin 100 → Bool}
    {tr3a tr3b : WTree} {L : Leaf25}
    (hI3b : ParInv bit allM (fun i => if i < 16 then allM else 0) m2b tr3b m3b)
    (hm2b_16 : ∀ k : Nat, (hk : k < 16) → m2b ⟨25 + k, by omega⟩ = uRotBit (sliceVal 25 24 m1) s4 k)
    (hok : checkLeafMidConst bit s4 tr3a tr3b L = true) :
    (∀ (k : Nat) (hk : k < 16), m3b ⟨25 + k, by omega⟩ = uRotBit (sliceVal 25 24 m1) L.s4 k) ∧
    (∀ (b : Nat) (hb : b < 15), m3b ⟨72 + b, by omega⟩ = L.kv.testBit b) ∧
    xor (xor (xor (xor (m3b ⟨44, by decide⟩ && xor (m3b ⟨46, by decide⟩) (m3b ⟨41, by decide⟩))
      (m3b ⟨41, by decide⟩)) (m3b ⟨48, by decide⟩)) (m3b ⟨58, by decide⟩)) true = L.lv.testBit 0 ∧
    (∀ (j : Nat) (hj : j < 7), m3b ⟨87 + j, by omega⟩ = L.lv.testBit (1 + j)) ∧
    16 * getBits bit (bHi19Wires.map (wGet tr3a)) 0 19 +
      4194304 * u18_val (m3b ⟨44, by decide⟩) (m3b ⟨45, by decide⟩)
        (m3b ⟨46, by decide⟩) (m3b ⟨48, by decide⟩)
        (m3b ⟨58, by decide⟩) (m3b ⟨47, by decide⟩) +
      bLo4InitVal m3b + slopeConst27 L.kv + 1024 =
    L.b_base +
      536870912 *
        (cond (u18_q19_4 (m3b ⟨48, by decide⟩) (m3b ⟨58, by decide⟩) (m3b ⟨47, by decide⟩))
          1 0) := by
  unfold checkLeafMidConst at hok
  dsimp only at hok
  simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨hs4_eq, hkv_all⟩, hlv0_eq⟩, hlv_all⟩, hbase_eq⟩ := hok
  have htr := fun w (hw1 : 41 ≤ w) (hw2 : w < 100) (hw3 : w ≠ 49) =>
    hI3b.m3b_tracked w hw1 hw2 hw3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hs4_eq, ← hm2b_16 k hk]
    exact hI3b.hFree ⟨25 + k, by omega⟩
      (Or.inl ⟨by dsimp; omega, by dsimp; omega,
        by dsimp; rw [Nat.add_sub_cancel_left, ite_eq_left hk]; exact hI3b.hAll⟩)
  · intro b hb
    have h1 := List.all_eq_true.mp hkv_all b (mem_rangeList_iff.mpr ⟨by omega, by omega⟩)
    rw [htr (72 + b) (by omega) (by omega) (by omega)]
    exact beq_iff_eq.mp h1
  · rw [htr 44 (by decide) (by decide) (by decide),
        htr 46 (by decide) (by decide) (by decide),
        htr 41 (by decide) (by decide) (by decide),
        htr 48 (by decide) (by decide) (by decide),
        htr 58 (by decide) (by decide) (by decide)]
    exact hlv0_eq
  · intro j hj
    have h1 := List.all_eq_true.mp hlv_all j (mem_rangeList_iff.mpr ⟨by omega, by omega⟩)
    rw [htr (87 + j) (by omega) (by omega) (by omega)]
    exact beq_iff_eq.mp h1
  · unfold bLo4InitVal bLo4InitBit0 bLo4InitBit1
    rw [htr 41 (by decide) (by decide) (by decide),
        htr 44 (by decide) (by decide) (by decide),
        htr 45 (by decide) (by decide) (by decide),
        htr 46 (by decide) (by decide) (by decide),
        htr 47 (by decide) (by decide) (by decide),
        htr 48 (by decide) (by decide) (by decide),
        htr 58 (by decide) (by decide) (by decide),
        htr 70 (by decide) (by decide) (by decide),
        htr 71 (by decide) (by decide) (by decide),
        htr 72 (by decide) (by decide) (by decide),
        htr 75 (by decide) (by decide) (by decide),
        htr 77 (by decide) (by decide) (by decide),
        htr 78 (by decide) (by decide) (by decide),
        htr 86 (by decide) (by decide) (by decide),
        htr 89 (by decide) (by decide) (by decide),
        htr 93 (by decide) (by decide) (by decide)]
    exact hbase_eq

def checkLeafCover (cur end_ : Nat) : List Leaf25 → Bool
  | [] => Nat.beq cur end_
  | L :: rest =>
      cond (Nat.beq cur L.us && Nat.blt L.us L.ue)
        (checkLeafCover L.ue end_ rest) false

def checkCubeLeaves (bit s4 us ue : Nat) (tr3a tr3b : WTree) : List Leaf25 → Bool
  | [] => true
  | L :: rest =>
      let overlap := Nat.blt (max us L.us) (min ue L.ue)
      let ok := if overlap then checkLeafMidConst bit s4 tr3a tr3b L else true
      cond ok (checkCubeLeaves bit s4 us ue tr3a tr3b rest) false

def checkSliceLeavesAux (bit : Nat) (tr3a tr3b : WTree) (leaves : List Leaf25) :
    List (Nat × Nat × Nat × Nat) → Bool
  | [] => true
  | (us, ue, _, s4) :: rest =>
      cond (checkCubeLeaves bit s4 us ue tr3a tr3b leaves)
        (checkSliceLeavesAux (bit + 1) tr3a tr3b leaves rest) false

def checkSliceLeafMidConst (start end_ j0 cnt : Nat)
    (cubes : List (Nat × Nat × Nat × Nat)) (tr3a tr3b : WTree) : Bool :=
  let sub := (leafData25.drop j0).take cnt
  checkLeafCover start end_ sub &&
  checkSliceLeavesAux 0 tr3a tr3b sub cubes

def findLeaf (u : Nat) : List Leaf25 → Option Leaf25
  | [] => none
  | L :: rest => if Nat.blt u L.ue then some L else findLeaf u rest

theorem findLeaf_sound :
    ∀ (cur end_ u : Nat) (leaves : List Leaf25),
      checkLeafCover cur end_ leaves = true →
      cur ≤ u → u < end_ →
      ∃ L, findLeaf u leaves = some L ∧ L ∈ leaves ∧ L.us ≤ u ∧ u < L.ue
  | cur, end_, u, [], hcov, hcur, hu => by
      dsimp only [checkLeafCover] at hcov
      have := Nat.beq_eq.mp hcov; omega
  | cur, end_, u, L :: rest, hcov, hcur, hu => by
      dsimp only [checkLeafCover] at hcov
      cases hc : (Nat.beq cur L.us && Nat.blt L.us L.ue)
      · rw [hc, Bool.cond_false] at hcov; cases hcov
      rw [hc, Bool.cond_true] at hcov
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hc
      dsimp only [findLeaf]
      cases hlt : Nat.blt u L.ue
      · have hue_le : L.ue ≤ u := (blt_false_iff u L.ue).1 hlt
        obtain ⟨L', hf, hmem, hus', hue'⟩ := findLeaf_sound L.ue end_ u rest hcov hue_le hu
        exact ⟨L', hf, List.mem_cons_of_mem _ hmem, hus', hue'⟩
      · have hu_lt : u < L.ue := Nat.blt_eq.mp hlt
        exact ⟨L, rfl, List.mem_cons_self .., by omega, hu_lt⟩

theorem checkCubeLeaves_sound {bit s4 us ue : Nat} {tr3a tr3b : WTree} :
    ∀ (leaves : List Leaf25) (L : Leaf25),
      checkCubeLeaves bit s4 us ue tr3a tr3b leaves = true →
      L ∈ leaves →
      max us L.us < min ue L.ue →
      checkLeafMidConst bit s4 tr3a tr3b L = true
  | [], _, _, hmem, _ => absurd hmem List.not_mem_nil
  | L0 :: rest, L, hok, hmem, hov => by
      dsimp only [checkCubeLeaves] at hok
      set overlap := Nat.blt (max us L0.us) (min ue L0.ue)
      set ok := if overlap then checkLeafMidConst bit s4 tr3a tr3b L0 else true
      cases hc : ok
      · rw [hc, Bool.cond_false] at hok; cases hok
      rw [hc, Bool.cond_true] at hok
      rcases List.mem_cons.mp hmem with rfl | htail
      · have hov_b : overlap = true := Nat.blt_eq.mpr hov
        dsimp only [ok] at hc
        rwa [hov_b, ite_eq_left rfl] at hc
      · exact checkCubeLeaves_sound rest L hok htail hov

theorem checkSliceLeavesAux_sound :
    ∀ (bit : Nat) (cubes : List (Nat × Nat × Nat × Nat)) (tr3a tr3b : WTree)
      (leaves : List Leaf25) (u bit' us ue w s4 : Nat),
      checkSliceLeavesAux bit tr3a tr3b leaves cubes = true →
      findCube4 bit cubes u = some (bit', us, ue, w, s4) →
      checkCubeLeaves bit' s4 us ue tr3a tr3b leaves = true
  | _, [], _, _, _, _, _, _, _, _, _, _, hf => by cases hf
  | bit, (us0, ue0, w0, s4_0) :: rest, tr3a, tr3b, leaves, u, bit', us, ue, w, s4, hok, hf => by
      dsimp only [checkSliceLeavesAux] at hok
      cases hc : checkCubeLeaves bit s4_0 us0 ue0 tr3a tr3b leaves
      · rw [hc, Bool.cond_false] at hok; cases hok
      rw [hc, Bool.cond_true] at hok
      dsimp only [findCube4] at hf
      split_ifs at hf with hlt
      · injection hf with htuple
        injection htuple with h1 h2
        injection h2 with h2 h3
        injection h3 with h3 h4
        injection h4 with h4 h5
        subst h1; subst h2; subst h3; subst h5
        exact hc
      · exact checkSliceLeavesAux_sound (bit + 1) rest tr3a tr3b leaves u bit' us ue w s4 hok hf

theorem checkSliceLeafMidConst_sound {start end_ j0 cnt : Nat}
    {cubes : List (Nat × Nat × Nat × Nat)} {tr3a tr3b : WTree}
    (hok : checkSliceLeafMidConst start end_ j0 cnt cubes tr3a tr3b = true)
    {u bit us ue w s4 : Nat}
    (hstart : start ≤ u) (hend : u < end_)
    (hf : findCube4 0 cubes u = some (bit, us, ue, w, s4))
    (hus : us ≤ u) (hue : u < ue) :
    ∃ L,
      findLeaf u ((leafData25.drop j0).take cnt) = some L ∧
      L ∈ leafData25 ∧ L.us ≤ u ∧ u < L.ue ∧
      checkLeafMidConst bit s4 tr3a tr3b L = true := by
  unfold checkSliceLeafMidConst at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hcov, haux⟩ := hok
  obtain ⟨L, hfl, hmem_sub, hLus, hLue⟩ := findLeaf_sound start end_ u _ hcov hstart hend
  have hmem_all : L ∈ leafData25 := mem_leafData25_of_slice hmem_sub
  have hcl := checkSliceLeavesAux_sound 0 cubes tr3a tr3b _ u bit us ue w s4 haux hf
  have hov : max us L.us < min ue L.ue := by omega
  exact ⟨L, hfl, hmem_all, hLus, hLue, checkCubeLeaves_sound _ L hcl hmem_sub hov⟩

theorem phaseList102_append_eq {l1 l2 : List Op102} {m1 m2 : Fin 100 → Bool}
    (h1 : execList102 l1 m1 = some m2)
    (hp1 : phaseList102 l1 m1 = false)
    (hp2 : phaseList102 l2 m2 = false) :
    phaseList102 (l1 ++ l2) m1 = false := by
  rw [phaseList102_append _ _ h1, hp1, hp2, Bool.false_xor]

theorem leafMid_0_cert :
    checkSliceLeafMidConst 0 3670016 0 243 cubes_0 trS3a_0 trS3b_0 = true := by
  decide +kernel
theorem leafMid_1_cert :
    checkSliceLeafMidConst 3670016 5767168 243 206 cubes_1 trS3a_1 trS3b_1 = true := by
  decide +kernel
theorem leafMid_2_cert :
    checkSliceLeafMidConst 5767168 7208960 449 141 cubes_2 trS3a_2 trS3b_2 = true := by
  decide +kernel
theorem leafMid_3_cert :
    checkSliceLeafMidConst 7208960 7995392 590 157 cubes_3 trS3a_3 trS3b_3 = true := by
  decide +kernel
theorem leafMid_4_cert :
    checkSliceLeafMidConst 7995392 8290304 747 125 cubes_4 trS3a_4 trS3b_4 = true := by
  decide +kernel
theorem leafMid_5_cert :
    checkSliceLeafMidConst 8290304 8376320 872 88 cubes_5 trS3a_5 trS3b_5 = true := by
  decide +kernel
theorem leafMid_6_cert :
    checkSliceLeafMidConst 8376320 8388096 960 56 cubes_6 trS3a_6 trS3b_6 = true := by
  decide +kernel
theorem leafMid_7_cert :
    checkSliceLeafMidConst 8388096 8388608 1016 48 cubes_7 trS3a_7 trS3b_7 = true := by
  decide +kernel

def rawMidDelta25Slice (j0 cnt u : Nat) : Nat :=
  match findLeaf u ((leafData25.drop j0).take cnt) with
  | some L => (33554432 - u + deltaPos25 L.b_base L.kv L.lv L.s4 u) % 33554432
  | none => 0

def rawMidDelta25 (u : Nat) : Nat :=
  if u < 3670016 then rawMidDelta25Slice 0 243 u
  else if u < 5767168 then rawMidDelta25Slice 243 206 u
  else if u < 7208960 then rawMidDelta25Slice 449 141 u
  else if u < 7995392 then rawMidDelta25Slice 590 157 u
  else if u < 8290304 then rawMidDelta25Slice 747 125 u
  else if u < 8376320 then rawMidDelta25Slice 872 88 u
  else if u < 8388096 then rawMidDelta25Slice 960 56 u
  else rawMidDelta25Slice 1016 48 u

theorem exec_midOps102_slice {start end_ cs_end j0 cnt allM : Nat}
    {cs : List (Nat × Nat × Nat × Nat)} {fmList : List Nat}
    {tr0 tr2a tr2b tr2c tr3a tr3b tr52 tr54In tr54Out tr6a tr6cIn : WTree}
    {m_in : Fin 100 → Bool}
    (hcubes : checkCubeSlice start cs_end cs allM fmList tr0 tr2a tr2b tr6a = true)
    (hleaf : checkSliceLeafMidConst start end_ j0 cnt cs tr3a tr3b = true)
    (h2a : runParSeq allM (fun i => fmList.getD i 0) [s2aCertOps] tr0
      (fun tr => beqWTree tr tr2a && checkU24Restored tr0 tr && Nat.beq (wGet tr 62) 0) = true)
    (htr2b : (checkWTreeWF 7 tr2b &&
              checkEqList tr2b [47, 48] [wGet tr2a 47, wGet tr2a 48] &&
              checkEqList tr2b (rangeList 50 50) ((rangeList 50 50).map (wGet tr2a))) = true)
    (h2c : runParSeq allM (fun i => if i < 16 then allM else 0) [s2cOps] tr2b
      (fun tr => beqWTree tr tr2c) = true)
    (h3a : runParPhaseSeq allM (fun i => if i < 16 then allM else 0) s3aAllSeq tr2c
      (fun tr => beqWTree tr tr3a && checkZeroList tr
        [70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 87, 88, 89, 90,
         94, 95, 96, 97, 98]) = true)
    (h3bPost : runParPhaseSeq allM (fun i => if i < 16 then allM else 0) [s3bPostOps] tr3a
      (fun tr => beqWTree tr tr3b && checkZeroList tr clean3bOut) = true)
    (h41p : runParSeq allM (fun i => if i < 16 then allM else 0) [s4_1PostInnerOps] tr3b
      (fun tr => beqWTree tr (tr41pOf tr3b) &&
                 Nat.beq (wGet tr 86) 0 &&
                 Nat.beq (wGet tr 85) 0 &&
                 Nat.beq (wGet tr 52) 0 &&
                 Nat.beq (wGet tr 81) (wGet tr3b 81 ^^^ wGet tr3b 85) &&
                 checkEqList tr s41KeepWires (s41KeepWires.map (wGet tr3b))) = true)
    (h52 : runParSeq allM (fun i => if i < 16 then allM else 0) s5_2PostInnerSeq (tr41pOf tr3b)
      (fun tr => beqWTree tr tr52 &&
                 checkZeroList tr clean53Wires &&
                 checkEqList tr s52KeepWires (s52KeepWires.map (wGet tr3b))) = true)
    (htr54In : checkTrS54In allM tr3b tr52 tr54In = true)
    (h54 : runParSeq allM (fun i => if i < 16 then allM else 0) s5_4Seq tr54In
      (fun tr => beqWTree tr tr54Out) = true)
    (h6a : runParSeq allM (fun i => if i < 16 then allM else 0) [s6aOps] tr54Out
      (fun tr => beqWTree tr tr6a &&
                 Nat.beq (wGet tr 62) 0 &&
                 checkEqList tr (rangeList 41 6) ((rangeList 41 6).map (wGet tr2b)) &&
                 checkEqList tr [47, 48] [wGet tr0 47, wGet tr0 48]) = true)
    (htr6cIn : (checkWTreeWF 7 tr6cIn &&
                checkEqList tr6cIn (rangeList 25 24) ((rangeList 25 24).map (wGet tr0)) &&
                checkEqList tr6cIn (rangeList 50 50) ((rangeList 50 50).map (wGet tr6a))) = true)
    (h6c : runParSeq allM (fun i => fmList.getD i 0) [s6cOps] tr6cIn
      (fun tr => beqWTree tr tr0 &&
                 checkU24Restored tr0 tr &&
                 checkZeroList tr zAnc52) = true)
    (hm_in_anc : ∀ i : Nat, (hi : i < 50) → m_in ⟨50 + i, by omega⟩ = false)
    (hstart : start ≤ sliceVal 25 24 (Function.update m_in ⟨48, by decide⟩ false))
    (hend : sliceVal 25 24 (Function.update m_in ⟨48, by decide⟩ false) < end_)
    (hend_cs : end_ ≤ cs_end) :
    ∃ m_out : Fin 100 → Bool,
      execList102 midPhysicalOps m_in = some m_out ∧
      phaseList102 midPhysicalOps m_in = false ∧
      (∀ w : Fin 100, 25 ≤ w.val → m_out w = m_in w) ∧
      outVal102 m_out =
        (outVal102 m_in +
          rawMidDelta25Slice j0 cnt
            (sliceVal 25 24 (Function.update m_in ⟨48, by decide⟩ false))) % 33554432 := by
  set m1 : Fin 100 → Bool := Function.update m_in ⟨48, by decide⟩ false
  have hm1_anc : ∀ i : Nat, (hi : i < 50) → m1 ⟨50 + i, by omega⟩ = false := by
    intro i hi; dsimp only [m1]
    rw [Function.update_of_ne (fun e => by have := congrArg Fin.val e; dsimp at this; omega),
      hm_in_anc i hi]
  set u := sliceVal 25 24 m1
  have hu_lt24 : u < 16777216 := sumBits_lt 24 _
  obtain ⟨bit, us, ue, w, s4, hf, _, _, hus, hue, hs4, _, hfm_hi, hs4_bits, hrot16, hrot6, hI0⟩ :=
    checkCubeSlice_sound hcubes hm1_anc hstart (by omega)
  obtain ⟨L, hfl, hmem, hLus, hLue, hok_L⟩ :=
    checkSliceLeafMidConst_sound hleaf hstart hend hf hus hue
  obtain ⟨_, hz_le, hd_lt⟩ := ptPosOK25_all L hmem u hLus hLue
  obtain ⟨m2b, m3b, hex_pre, hph_pre, hm2b_49, hm2b_k, hm2b_16, hm3b_clean, hI3b, hout3b⟩ :=
    exec_preOps102_slice hs4 hI0 (fun _ _ => rfl) hfm_hi (fun b hb => (hs4_bits b hb).1)
      hrot16 hrot6 h2a htr2b h2c h3a h3bPost
  obtain ⟨hu_3b, hkv_3b, hlv0_3b, hlv_3b, hbase_eq⟩ :=
    checkLeafMidConst_sound hI3b hm2b_16 hok_L
  obtain ⟨m41, hex41, hnon41, h47_41, hval41⟩ := exec_s4_1Ops_init hm3b_clean
  have hm41_47 :
      xorControlsBool m3b s5_2PreControls (m41 ⟨47, by decide⟩) = m3b ⟨47, by decide⟩ := by
    rw [h47_41]; exact xorControlsBool_mask47_s41 m3b
  obtain ⟨st41Par, m41p, hex41p, hI41p, hm41_par_86, hm41_par_85, hm41_par_52, hm41_par_81,
      hm41_par_in, hm41p_86, hm41p_85, hm41p_52, hm41p_81, hm41p_ne86⟩ :=
    exec_s4_1PostOps_slice hI3b h41p hnon41 hm41_47
  obtain ⟨m52c, hex42_52c, hge25_52c, N_val, hN_narrow, hz52c⟩ :=
    exec_stages4_2_to_5_2Core hm3b_clean hnon41 hm41p_52 hm41p_85 hm41p_86 hm41p_ne86
      hu_3b (fun b hb => hkv_3b b (by omega)) hlv0_3b hlv_3b
  have hm52c_86 : m52c ⟨86, by decide⟩ = false :=
    (hge25_52c ⟨86, by decide⟩ (by decide)).trans hm41p_86
  have hm52c_85 : m52c ⟨85, by decide⟩ = false :=
    (hge25_52c ⟨85, by decide⟩ (by decide)).trans hm41p_85
  have hm52c_52 : m52c ⟨52, by decide⟩ = false :=
    (hge25_52c ⟨52, by decide⟩ (by decide)).trans hm41p_52
  have hm52c_81 : m52c ⟨81, by decide⟩ = xor (m3b ⟨81, by decide⟩) (m3b ⟨85, by decide⟩) :=
    (hge25_52c ⟨81, by decide⟩ (by decide)).trans hm41p_81
  have hm52c_agree :
      ∀ w : Fin 100, 25 ≤ w.val → w.val ∉ [47, 52, 69, 70, 71, 81, 85, 86] →
        m52c w = m3b w := by
    intro w hw25 hnot
    have hnot3 : w.val ∉ [52, 81, 85, 86] := by
      intro hm
      rcases (by simpa using hm : w.val = 52 ∨ w.val = 81 ∨ w.val = 85 ∨ w.val = 86)
        with h | h | h | h <;> exact hnot (by simp [h])
    have hsub : ∀ x ∈ [47, 69, 70, 71], x ∈ [47, 52, 69, 70, 71, 81, 85, 86] := by decide
    have hnot_b : w.val ∉ [47, 69, 70, 71] := fun h => hnot (hsub w.val h)
    exact (hge25_52c w hw25).trans ((hm41p_ne86 w hnot3).trans (hnon41 w hnot_b))
  have hm52c_47 :
      xorControlsBool m3b s5_2PreControls (m52c ⟨47, by decide⟩) = m3b ⟨47, by decide⟩ := by
    rw [hge25_52c ⟨47, by decide⟩ (by decide), hm41p_ne86 ⟨47, by decide⟩ (by decide), h47_41]
    exact xorControlsBool_mask47_s41 m3b
  obtain ⟨m52f, hex52p, hm52f_lt25, hm52f_blo4, hm52f_25_41, hm52f_clean, hm52f_keep, hm52f_49⟩ :=
    exec_s5_2PostOps_slice hI3b hI41p hm41_par_86 hm41_par_85 hm41_par_52 hm41_par_81
      hm41_par_in h52 hm52c_86 hm52c_85 hm52c_52 hm52c_81 hm52c_agree hm52c_47
  have hz3b : targVal z_w m3b =
      (outVal102 m1 + (33554432 - u) + u + getBits bit (bHi19Wires.map (wGet tr3a)) 0 19) %
        33554432 := by
    rw [targVal_z_w_eq_outVal102, hout3b]
    omega
  have hz52f : targVal z_w m52f =
      (targVal z_w m3b + (targVal b_lo4_w m41 + N_val) / 16) % 33554432 := by
    rw [targVal_z_w_eq_outVal102, outVal102_congr hm52f_lt25, ← targVal_z_w_eq_outVal102, hz52c]
  have hb52f : ∀ w : Fin 100, w.val ∈ b_lo4_w → m52f w = m41 w := by
    intro w hw
    have hge25 : 25 ≤ w.val ∧ w.val ∉ [52, 81, 85, 86] := by revert w hw; decide +kernel
    exact (hm52f_blo4 w hw).trans ((hge25_52c w hge25.1).trans (hm41p_ne86 w hge25.2))
  have hkeep52f : ∀ w : Fin 100, w.val ∉ badW_41_53 → m52f w = m3b w := by
    intro w hw
    have hmem102 : w.val ∈ rangeList 0 100 := mem_rangeList_iff.mpr ⟨by omega, w.isLt⟩
    rcases keepW54_props.2.2.1 w.val hmem102 hw with ⟨h25, h41⟩ | ⟨hkp, hnot3⟩
    · exact hm52f_25_41 w h25 h41
    · exact hm52f_keep w hkp hnot3
  have hcl53 : ∀ w : Fin 100, w.val ∈ clean_5_3 → m52f w = false :=
    fun w hw => hm52f_clean w (keepW54_props.2.2.2 w.val hw)
  obtain ⟨m53, hex53, hnon53, hbit47, hbit69, hbit70, hbit71,
      hm52, hm97, hm72, hm56, hm98, hm99, hz53⟩ :=
    exec_stage5_3_combine hz_le hd_lt hu_3b (fun b _ hb2 => hkv_3b b hb2)
      hN_narrow hbase_eq h47_41 hval41 hz3b hz52f hb52f hkeep52f hcl53
  have hI53 : ParInv bit allM (fun i => if i < 16 then allM else 0) m2b tr54In m53 :=
    checkTrS54In_sound hI3b hI41p h52 htr54In hm52f_25_41 hm52f_clean hm52f_keep hm52f_49
      hnon53 hbit47 hbit69 hbit70 hbit71 hm52 hm97 hm72 hm56 hm98 hm99
  obtain ⟨m6c, hex_post, hm6c_ge25, hout6c⟩ :=
    exec_postOps102_slice hs4 hI0 hfm_hi hm2b_49 hm2b_k (fun b hb => (hs4_bits b hb).2)
      hrot6 hI53 h54 h6a htr6cIn h6c
  let s_pre : Fin 100 := ⟨stash_pre, by decide⟩
  let s_41 : Fin 100 := ⟨stash_41, by decide⟩
  let s_41p : Fin 100 := ⟨stash_41p, by decide⟩
  let s_42_52c : Fin 100 := ⟨stash_42_52c, by decide⟩
  let s_52p : Fin 100 := ⟨stash_52p, by decide⟩
  let s_53 : Fin 100 := ⟨stash_53, by decide⟩
  let s_post : Fin 100 := ⟨stash_post, by decide⟩
  have hs_in_pre : m_in s_pre = false := by
    have h50 : 50 ≤ stash_pre ∧ stash_pre - 50 < 50 := by decide
    have hfin : (⟨50 + (stash_pre - 50), by omega⟩ : Fin 100) = s_pre :=
      Fin.ext (by dsimp [s_pre]; omega)
    rw [← hfin]; exact hm_in_anc (stash_pre - 50) h50.2
  obtain ⟨mp0, hex_h0, hinv0⟩ := exec_swap48_relay (s0 := s_pre) (by decide) hs_in_pre
  obtain ⟨mp1, hex_c1, hinv1⟩ := exec_chunk_relay hinv0 inNoStash_pre hex_pre
  have hs_41_ok : s_pre = s_41 ∨ m3b s_41 = false := Or.inr (hm3b_clean s_41 (by decide))
  obtain ⟨mp1h, hex_h1, hinv1h⟩ := exec_hop_relay hinv1 hs_41_ok
  obtain ⟨mp2, hex_c2, hinv2⟩ := exec_chunk_relay hinv1h inNoStash_41 hex41
  have hs_41p_ok : s_41 = s_41p ∨ m41 s_41p = false := Or.inl rfl
  obtain ⟨mp2h, hex_h2, hinv2h⟩ := exec_hop_relay hinv2 hs_41p_ok
  obtain ⟨mp3, hex_c3, hinv3⟩ := exec_chunk_relay hinv2h inNoStash_41p hex41p
  have hs_42_ok : s_41p = s_42_52c ∨ m41p s_42_52c = false := Or.inr hm41p_86
  obtain ⟨mp3h, hex_h3, hinv3h⟩ := exec_hop_relay hinv3 hs_42_ok
  obtain ⟨mp4, hex_c4, hinv4⟩ := exec_chunk_relay hinv3h inNoStash_42_52c hex42_52c
  have hs_52p_ok : s_42_52c = s_52p ∨ m52c s_52p = false :=
    Or.inr ((hge25_52c s_52p (by decide)).trans
      ((hm41p_ne86 s_52p (by decide)).trans
        ((hnon41 s_52p (by decide)).trans (hm3b_clean s_52p (by decide)))))
  obtain ⟨mp4h, hex_h4, hinv4h⟩ := exec_hop_relay hinv4 hs_52p_ok
  obtain ⟨mp5, hex_c5, hinv5⟩ := exec_chunk_relay hinv4h inNoStash_52p hex52p
  have hs_53_ok : s_52p = s_53 ∨ m52f s_53 = false := Or.inl rfl
  obtain ⟨mp5h, hex_h5, hinv5h⟩ := exec_hop_relay hinv5 hs_53_ok
  obtain ⟨mp6, hex_c6, hinv6⟩ := exec_chunk_relay hinv5h inNoStash_53 hex53
  have hs_post_ok : s_53 = s_post ∨ m53 s_post = false := Or.inl rfl
  obtain ⟨mp6h, hex_h6, hinv6h⟩ := exec_hop_relay hinv6 hs_post_ok
  obtain ⟨mp7, hex_c7, hinv7⟩ := exec_chunk_relay hinv6h inNoStash_post hex_post
  have hm6c_48 : m6c ⟨48, by decide⟩ = false := by
    rw [hm6c_ge25 ⟨48, by decide⟩ (by decide)]
    dsimp only [m1]; exact Function.update_self ..
  have hex_end := exec_unswap48_relay hinv7 (by decide) hm6c_48
  set m_out := Function.update m6c ⟨48, by decide⟩ (m_in ⟨48, by decide⟩)
  have hmid_eq : midPhysicalOps =
      hopOps 48 stash_pre ++ (preOps102 ++ (hopOps stash_pre stash_41 ++ (s4_1Ops ++
      (hopOps stash_41 stash_41p ++ (s4_1PostOps ++ (hopOps stash_41p stash_42_52c ++
      (stages4_2_to_5_2Core ++ (hopOps stash_42_52c stash_52p ++ (s5_2PostOps ++
      (hopOps stash_52p stash_53 ++ (s5_3Ops ++ (hopOps stash_53 stash_post ++
      (postOps102 ++ hopOps stash_post 48))))))))))))) := by
    rw [midPhysicalOps_eq_hops]
    simp only [List.append_assoc]
  have hex_mid_phys : execList102 midPhysicalOps m_in = some m_out := by
    rw [hmid_eq]
    exact execList102_append_eq hex_h0 (execList102_append_eq hex_c1
      (execList102_append_eq hex_h1 (execList102_append_eq hex_c2
      (execList102_append_eq hex_h2 (execList102_append_eq hex_c3
      (execList102_append_eq hex_h3 (execList102_append_eq hex_c4
      (execList102_append_eq hex_h4 (execList102_append_eq hex_c5
      (execList102_append_eq hex_h5 (execList102_append_eq hex_c6
      (execList102_append_eq hex_h6 (execList102_append_eq hex_c7 hex_end)))))))))))))
  have hph_mid_phys : phaseList102 midPhysicalOps m_in = false := by
    rw [hmid_eq]
    exact phaseList102_append_eq hex_h0 (phaseList102_hopOps _ _ _)
      (phaseList102_append_eq hex_c1
        ((phaseList102_chunk_relay hinv0 inNoStash_pre hex_pre).trans hph_pre)
      (phaseList102_append_eq hex_h1 (phaseList102_hopOps _ _ _)
      (phaseList102_append_eq hex_c2 (phaseList102_of_noPhase _ _ noPhase_s4_1)
      (phaseList102_append_eq hex_h2 (phaseList102_hopOps _ _ _)
      (phaseList102_append_eq hex_c3 (phaseList102_of_noPhase _ _ noPhase_s4_1Post)
      (phaseList102_append_eq hex_h3 (phaseList102_hopOps _ _ _)
      (phaseList102_append_eq hex_c4 (phaseList102_of_noPhase _ _ noPhase_42_52c)
      (phaseList102_append_eq hex_h4 (phaseList102_hopOps _ _ _)
      (phaseList102_append_eq hex_c5 (phaseList102_of_noPhase _ _ noPhase_52p)
      (phaseList102_append_eq hex_h5 (phaseList102_hopOps _ _ _)
      (phaseList102_append_eq hex_c6 (phaseList102_of_noPhase _ _ noPhase_53)
      (phaseList102_append_eq hex_h6 (phaseList102_hopOps _ _ _)
      (phaseList102_append_eq hex_c7 (phaseList102_of_noPhase _ _ noPhase_post)
        (phaseList102_hopOps _ _ _))))))))))))))
  have hm_out_ge25 : ∀ w : Fin 100, 25 ≤ w.val → m_out w = m_in w := by
    intro w hw
    by_cases hw48 : w = ⟨48, by decide⟩
    · subst hw48; dsimp only [m_out]; exact Function.update_self ..
    · dsimp only [m_out]
      rw [Function.update_of_ne hw48, hm6c_ge25 w hw]
      dsimp only [m1]; exact Function.update_of_ne hw48 ..
  have hout_m1 : outVal102 m1 = outVal102 m_in :=
    outVal102_congr (fun j hj =>
      Function.update_of_ne (fun e => by have := congrArg Fin.val e; dsimp at this; omega) _ _)
  have hout_mout : outVal102 m_out = outVal102 m6c :=
    outVal102_congr (fun j hj =>
      Function.update_of_ne (fun e => by have := congrArg Fin.val e; dsimp at this; omega) _ _)
  refine ⟨m_out, hex_mid_phys, hph_mid_phys, hm_out_ge25, ?_⟩
  unfold rawMidDelta25Slice
  rw [hfl, hout_mout, hout6c, ← targVal_z_w_eq_outVal102 m53, hz53, ← hout_m1]
  dsimp only
  omega

theorem exec_midOps102 {m_in : Fin 100 → Bool}
    (hm1_anc : ∀ i : Nat, (hi : i < 50) → m_in ⟨50 + i, by omega⟩ = false)
    (hu_lt : sliceVal 25 24 (Function.update m_in ⟨48, by decide⟩ false) < 8388608) :
    ∃ m_out : Fin 100 → Bool,
      execList102 midPhysicalOps m_in = some m_out ∧
      phaseList102 midPhysicalOps m_in = false ∧
      (∀ w : Fin 100, 25 ≤ w.val → m_out w = m_in w) ∧
      outVal102 m_out =
        (outVal102 m_in +
          rawMidDelta25 (sliceVal 25 24 (Function.update m_in ⟨48, by decide⟩ false))) %
            33554432 := by
  set u := sliceVal 25 24 (Function.update m_in ⟨48, by decide⟩ false)
  unfold rawMidDelta25
  by_cases h0 : u < 3670016
  · rw [ite_eq_left h0]
    exact exec_midOps102_slice cubesSlice_0_cert leafMid_0_cert s2a_0_cert trS2b_0_cert s2c_0_cert
      s3a_0_cert s3bPost_0_cert s4_1PostInner_0_cert s5_2PostInner_0_cert
      trS54In_0_cert s5_4_0_cert s6a_0_cert
      trS6cIn_0_cert s6c_0_cert hm1_anc (Nat.zero_le _) h0 (le_rfl)
  rw [ite_eq_right h0]
  by_cases h1 : u < 5767168
  · rw [ite_eq_left h1]
    exact exec_midOps102_slice cubesSlice_1_cert leafMid_1_cert s2a_1_cert trS2b_1_cert s2c_1_cert
      s3a_1_cert s3bPost_1_cert s4_1PostInner_1_cert s5_2PostInner_1_cert
      trS54In_1_cert s5_4_1_cert s6a_1_cert
      trS6cIn_1_cert s6c_1_cert hm1_anc (by omega) h1 (le_rfl)
  rw [ite_eq_right h1]
  by_cases h2 : u < 7208960
  · rw [ite_eq_left h2]
    exact exec_midOps102_slice cubesSlice_2_cert leafMid_2_cert s2a_2_cert trS2b_2_cert s2c_2_cert
      s3a_2_cert s3bPost_2_cert s4_1PostInner_2_cert s5_2PostInner_2_cert
      trS54In_2_cert s5_4_2_cert s6a_2_cert
      trS6cIn_2_cert s6c_2_cert hm1_anc (by omega) h2 (le_rfl)
  rw [ite_eq_right h2]
  by_cases h3 : u < 7995392
  · rw [ite_eq_left h3]
    exact exec_midOps102_slice cubesSlice_3_cert leafMid_3_cert s2a_3_cert trS2b_3_cert s2c_3_cert
      s3a_3_cert s3bPost_3_cert s4_1PostInner_3_cert s5_2PostInner_3_cert
      trS54In_3_cert s5_4_3_cert s6a_3_cert
      trS6cIn_3_cert s6c_3_cert hm1_anc (by omega) h3 (le_rfl)
  rw [ite_eq_right h3]
  by_cases h4 : u < 8290304
  · rw [ite_eq_left h4]
    exact exec_midOps102_slice cubesSlice_4_cert leafMid_4_cert s2a_4_cert trS2b_4_cert s2c_4_cert
      s3a_4_cert s3bPost_4_cert s4_1PostInner_4_cert s5_2PostInner_4_cert
      trS54In_4_cert s5_4_4_cert s6a_4_cert
      trS6cIn_4_cert s6c_4_cert hm1_anc (by omega) h4 (le_rfl)
  rw [ite_eq_right h4]
  by_cases h5 : u < 8376320
  · rw [ite_eq_left h5]
    exact exec_midOps102_slice cubesSlice_5_cert leafMid_5_cert s2a_5_cert trS2b_5_cert s2c_5_cert
      s3a_5_cert s3bPost_5_cert s4_1PostInner_5_cert s5_2PostInner_5_cert
      trS54In_5_cert s5_4_5_cert s6a_5_cert
      trS6cIn_5_cert s6c_5_cert hm1_anc (by omega) h5 (le_rfl)
  rw [ite_eq_right h5]
  by_cases h6 : u < 8388096
  · rw [ite_eq_left h6]
    exact exec_midOps102_slice cubesSlice_6_cert leafMid_6_cert s2a_6_cert trS2b_6_cert s2c_6_cert
      s3a_6_cert s3bPost_6_cert s4_1PostInner_6_cert s5_2PostInner_6_cert
      trS54In_6_cert s5_4_6_cert s6a_6_cert
      trS6cIn_6_cert s6c_6_cert hm1_anc (by omega) h6 (le_rfl)
  rw [ite_eq_right h6]
  exact exec_midOps102_slice cubesSlice_7_cert leafMid_7_cert s2a_7_cert trS2b_7_cert s2c_7_cert
    s3a_7_cert s3bPost_7_cert s4_1PostInner_7_cert s5_2PostInner_7_cert
    trS54In_7_cert s5_4_7_cert s6a_7_cert
    trS6cIn_7_cert s6c_7_cert hm1_anc (by omega) hu_lt (by decide)

def rawDelta25 (u : Nat) : Nat :=
  (s1AddVal u + rawMidDelta25 (u % 8388608)) % 33554432

theorem rawDelta25_lt (u : Nat) : rawDelta25 u < 33554432 :=
  Nat.mod_lt _ (by decide)

theorem rawDelta25_8388608 : rawDelta25 8388608 = 13176795 := by decide +kernel

theorem rawMidDelta25Slice_pos {start end_ j0 cnt : Nat}
    {cubes : List (Nat × Nat × Nat × Nat)} {tr3a tr3b : WTree}
    (hok : checkSliceLeafMidConst start end_ j0 cnt cubes tr3a tr3b = true)
    {u : Nat} (hstart : start ≤ u) (hend : u < end_) (hu8M : u < 8388608) :
    ∃ L ∈ leafData25, L.us ≤ u ∧ u < L.ue ∧
      (u + rawMidDelta25Slice j0 cnt u) % 33554432 = deltaPos25 L.b_base L.kv L.lv L.s4 u := by
  unfold checkSliceLeafMidConst at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨L, hfl, hmem_sub, hLus, hLue⟩ := findLeaf_sound start end_ u _ hok.1 hstart hend
  have hmem : L ∈ leafData25 := mem_leafData25_of_slice hmem_sub
  obtain ⟨_, _, hd_lt⟩ := ptPosOK25_all L hmem u hLus hLue
  refine ⟨L, hmem, hLus, hLue, ?_⟩
  unfold rawMidDelta25Slice
  rw [hfl]
  dsimp only
  omega

theorem rawDelta25_pos_lt8388608 (u : Nat) (hu : u < 8388608) :
    ∃ L ∈ leafData25, L.us ≤ u ∧ u < L.ue ∧
      rawDelta25 u = deltaPos25 L.b_base L.kv L.lv L.s4 u := by
  unfold rawDelta25
  rw [s1AddVal_of_lt hu, Nat.mod_eq_of_lt hu]
  unfold rawMidDelta25
  by_cases h0 : u < 3670016
  · rw [ite_eq_left h0]; exact rawMidDelta25Slice_pos leafMid_0_cert (Nat.zero_le _) h0 hu
  rw [ite_eq_right h0]
  by_cases h1 : u < 5767168
  · rw [ite_eq_left h1]; exact rawMidDelta25Slice_pos leafMid_1_cert (by omega) h1 hu
  rw [ite_eq_right h1]
  by_cases h2 : u < 7208960
  · rw [ite_eq_left h2]; exact rawMidDelta25Slice_pos leafMid_2_cert (by omega) h2 hu
  rw [ite_eq_right h2]
  by_cases h3 : u < 7995392
  · rw [ite_eq_left h3]; exact rawMidDelta25Slice_pos leafMid_3_cert (by omega) h3 hu
  rw [ite_eq_right h3]
  by_cases h4 : u < 8290304
  · rw [ite_eq_left h4]; exact rawMidDelta25Slice_pos leafMid_4_cert (by omega) h4 hu
  rw [ite_eq_right h4]
  by_cases h5 : u < 8376320
  · rw [ite_eq_left h5]; exact rawMidDelta25Slice_pos leafMid_5_cert (by omega) h5 hu
  rw [ite_eq_right h5]
  by_cases h6 : u < 8388096
  · rw [ite_eq_left h6]; exact rawMidDelta25Slice_pos leafMid_6_cert (by omega) h6 hu
  rw [ite_eq_right h6]
  exact rawMidDelta25Slice_pos leafMid_7_cert (by omega) hu hu

def z25Delta (y : Nat) : Nat :=
  if y.testBit 24 then
    (33554432 - rawDelta25 ((33554432 - y) % 16777216)) % 33554432
  else
    rawDelta25 (y % 16777216)

theorem z25Delta_lt (y : Nat) : z25Delta y < 33554432 := by
  unfold z25Delta
  split_ifs
  · exact Nat.mod_lt _ (by decide)
  · exact rawDelta25_lt _

theorem sub_mod_sub_eq {b D Q : Nat} (hb : b < Q) (hD : D < Q) :
    (Q - 1) - ((Q - 1 - b + D) % Q) = (b + (Q - D) % Q) % Q := by
  by_cases hD0 : D = 0
  · subst hD0
    rw [Nat.sub_zero, Nat.mod_self, Nat.add_zero, Nat.add_zero,
        Nat.mod_eq_of_lt (by omega : Q - 1 - b < Q),
        Nat.mod_eq_of_lt hb]
    omega
  · rw [Nat.mod_eq_of_lt (by omega : Q - D < Q)]
    by_cases hle : D ≤ b
    · have h1 : Q - 1 - b + D < Q := by omega
      have h2 : b + (Q - D) = Q + (b - D) := by omega
      rw [Nat.mod_eq_of_lt h1, h2, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : b - D < Q)]
      omega
    · have h1 : Q - 1 - b + D = Q + (D - b - 1) := by omega
      rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : D - b - 1 < Q),
          Nat.mod_eq_of_lt (by omega : b + (Q - D) < Q)]
      omega

theorem sliceVal_update48_false (m : Fin 100 → Bool) :
    sliceVal 25 24 (Function.update m ⟨48, by decide⟩ false) = sliceVal 25 24 m % 8388608 := by
  have hsp1 : sliceVal 25 24 (Function.update m ⟨48, by decide⟩ false) =
      sliceVal 25 23 (Function.update m ⟨48, by decide⟩ false) := by
    unfold sliceVal
    change sumBits (23 + 1) _ = _
    rw [sumBits_succ, dite_eq_left (by decide)]
    have h48 : (Function.update m ⟨48, by decide⟩ false) ⟨25 + 23, by decide⟩ = false :=
      Function.update_self ..
    rw [h48, Bool.toNat_false, mul_zero, add_zero]
  have hsp2 : sliceVal 25 24 m = sliceVal 25 23 m + 8388608 * (m ⟨48, by decide⟩).toNat := by
    unfold sliceVal
    simp [sumBits]
  have hlo_eq : sliceVal 25 23 (Function.update m ⟨48, by decide⟩ false) = sliceVal 25 23 m := by
    unfold sliceVal
    refine sumBits_congr fun k hk => ?_
    have hk102 : 25 + k < 100 := by omega
    rw [dite_eq_left hk102, dite_eq_left hk102]
    exact Function.update_of_ne (fun e => by have := congrArg Fin.val e; dsimp at this; omega) _ _
  have hlt : sliceVal 25 23 m < 8388608 := sumBits_lt 23 _
  rw [hsp1, hlo_eq, hsp2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem exec_fullK25Ops {m0 : Fin 100 → Bool}
    (hy_in : ∀ i : Nat, (hi : i < 25) → m0 ⟨25 + i, by omega⟩ = (sliceVal 25 25 m0).testBit i)
    (hanc : ∀ i : Nat, (hi : i < 50) → m0 ⟨50 + i, by omega⟩ = false) :
    ∃ m7 : Fin 100 → Bool,
      execList102 fullK25Ops m0 = some m7 ∧
      phaseList102 fullK25Ops m0 = false ∧
      (∀ w : Fin 100, 25 ≤ w.val → w.val < 50 → m7 w = m0 w) ∧
      (∀ w : Fin 100, 50 ≤ w.val → m7 w = false) ∧
      outVal102 m7 = (outVal102 m0 + z25Delta (sliceVal 25 25 m0)) % 33554432 := by
  obtain ⟨mB, m1, m1a, hexB, hexY, hexA, hex1, hmB_ge25, hm1a_ge25, hm1_49,
      hm1_anc, hm1_u24, hout1a⟩ :=
    exec_s1Ops hanc
  have hm1a_anc : ∀ i : Nat, (hi : i < 50) → m1a ⟨50 + i, by omega⟩ = false :=
    fun i hi => (hm1a_ge25 ⟨50 + i, by omega⟩ (by dsimp; omega)).trans (hm1_anc i hi)
  have hm1a_u : sliceVal 25 24 m1a = sliceVal 25 24 m1 := by
    unfold sliceVal
    refine sumBits_congr fun k hk => ?_
    have hkq : 25 + k < 100 := by omega
    rw [dite_eq_left hkq, dite_eq_left hkq]
    exact hm1a_ge25 ⟨25 + k, hkq⟩ (by dsimp; omega)
  have hm1b_u :
      sliceVal 25 24 (Function.update m1a ⟨48, by decide⟩ false) =
        sliceVal 25 24 m1 % 8388608 := by
    rw [sliceVal_update48_false, hm1a_u]
  have hm1b_lt : sliceVal 25 24 (Function.update m1a ⟨48, by decide⟩ false) < 8388608 := by
    rw [hm1b_u]; exact Nat.mod_lt _ (by decide)
  obtain ⟨m6d, hex_mid, hph_mid, hm6d_ge25_a, hout6d⟩ := exec_midOps102 hm1a_anc hm1b_lt
  have hm6d_ge25 : ∀ w : Fin 100, 25 ≤ w.val → m6d w = m1 w :=
    fun w hw => (hm6d_ge25_a w hw).trans (hm1a_ge25 w hw)
  obtain ⟨m7, hex7, hm7_ge25, hout7⟩ := exec_s7Ops hanc hmB_ge25 hexY hm6d_ge25
  have hex_full : execList102 fullK25Ops m0 = some m7 := by
    unfold fullK25Ops
    rw [List.append_assoc]
    exact execList102_append_eq hex1 (execList102_append_eq hex_mid hex7)
  have hph_full : phaseList102 fullK25Ops m0 = false := by
    unfold fullK25Ops
    rw [List.append_assoc]
    exact phaseList102_append_eq hex1 (phaseList102_of_noPhase _ _ noPhase_s1)
      (phaseList102_append_eq hex_mid hph_mid (phaseList102_of_noPhase _ _ noPhase_s7))
  refine ⟨m7, hex_full, hph_full, fun w hw1 _ => hm7_ge25 w hw1, fun w hw50 => ?_, ?_⟩
  · rw [hm7_ge25 w (by omega)]
    have := hanc (w.val - 50) (by omega)
    simpa [show 50 + (w.val - 50) = w.val by omega] using this
  · set y := sliceVal 25 25 m0
    have hm0_49 : m0 ⟨49, by decide⟩ = y.testBit 24 := hy_in 24 (by decide)
    rw [hout7, hout6d, hout1a, hm1b_u, hm1_u24, hm0_49]
    have hcomb : (((if y.testBit 24 then 33554431 - outVal102 m0 else outVal102 m0) +
        s1AddVal (u24OfY y)) % 33554432 + rawMidDelta25 (u24OfY y % 8388608)) % 33554432 =
        ((if y.testBit 24 then 33554431 - outVal102 m0 else outVal102 m0) +
        rawDelta25 (u24OfY y)) % 33554432 := by
      unfold rawDelta25; omega
    rw [hcomb]
    unfold z25Delta u24OfY
    have hb_lt : outVal102 m0 < 33554432 := sumBits_lt 25 _
    have hD_lt : ∀ u, rawDelta25 u < 33554432 := rawDelta25_lt
    cases hs : y.testBit 24
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hu24_lt : u24OfY y < 16777216 := u24OfY_lt (sumBits_lt 25 _)
      unfold u24OfY at hu24_lt
      rw [ite_eq_right (by rw [hs]; exact Bool.false_ne_true)] at hu24_lt
      rw [Nat.mod_eq_of_lt hu24_lt]
    · simp only [↓reduceIte]
      exact sub_mod_sub_eq hb_lt (hD_lt _)

-- ============================================================================
-- Section 4: Step 100 Compilation Bridge & QuantumComputation.Specs Cost Theorem
-- ============================================================================

@[inline] def w25 {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n) (i : Nat) : Fin n :=
  if hi : i < 50 then rData ⟨i, hi⟩
  else if ha : i - 50 < 50 then rAnc ⟨i - 50, ha⟩
  else rData ⟨0, by decide⟩

theorem hw25_inj {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) {i j : Nat} (hi : i < 100) (hj : j < 100)
    (heq : w25 rData rAnc i = w25 rData rAnc j) : i = j := by
  unfold w25 at heq
  by_cases h1 : i < 50 <;> by_cases h2 : j < 50
  · simp only [h1, h2, ↓reduceDIte] at heq
    exact congrArg Fin.val (rData.wires.injective heq)
  · have h3 : j - 50 < 50 := by omega
    simp only [h1, h2, h3, ↓reduceDIte] at heq
    exact False.elim (hdisj.ne_of_mem ⟨⟨i, h1⟩, rfl⟩ ⟨⟨j - 50, h3⟩, rfl⟩ heq)
  · have h3 : i - 50 < 50 := by omega
    simp only [h1, h2, h3, ↓reduceDIte] at heq
    exact False.elim (hdisj.ne_of_mem ⟨⟨j, h2⟩, rfl⟩ ⟨⟨i - 50, h3⟩, rfl⟩ heq.symm)
  · have h3 : i - 50 < 50 := by omega
    have h4 : j - 50 < 50 := by omega
    simp only [h1, h2, h3, h4, ↓reduceDIte] at heq
    have hv := congrArg Fin.val (rAnc.wires.injective heq)
    dsimp only at hv
    omega

@[inline] def Op102.toStep {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n) : Op102 → Step n
  | .x q => .x (w25 rData rAnc q)
  | .cx c t => .cnot (w25 rData rAnc c) (w25 rData rAnc t)
  | .and4t c1 c2 t => .and4t (w25 rData rAnc c1) (w25 rData rAnc c2) (w25 rData rAnc t)
  | .rccx0 c1 c2 t => .rccx0 (w25 rData rAnc c1) (w25 rData rAnc c2) (w25 rData rAnc t)
  | .rccx1 c1 c2 t => .rccx1 (w25 rData rAnc c1) (w25 rData rAnc c2) (w25 rData rAnc t)
  | .unand c1 c2 t => .unand (w25 rData rAnc c1) (w25 rData rAnc c2) (w25 rData rAnc t)
  | .unquad qs ls t =>
      .unquad (qs.map fun p => (w25 rData rAnc p.1, w25 rData rAnc p.2))
        (ls.map (w25 rData rAnc)) (w25 rData rAnc t)
  | _ => .x (w25 rData rAnc 0)

theorem Op102.andCount_toStep {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n) (g : Op102) :
    (g.toStep rData rAnc).andCount = g.andCount := by
  cases g <;> rfl

theorem map_andCount_toStep {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (L : List Op102) :
    ((L.map (Op102.toStep rData rAnc)).map Step.andCount).sum = (L.map Op102.andCount).sum := by
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun g _ => Op102.andCount_toStep rData rAnc g

def k25Steps {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n) : List (Step n) :=
  fullK25Ops.map (Op102.toStep rData rAnc)

theorem andCount_k25Steps {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n) :
    ((k25Steps rData rAnc).map Step.andCount).sum = 773 := by
  unfold k25Steps
  rw [map_andCount_toStep, andCount_fullK25Ops]

noncomputable def lift102 {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (β : BitAssignment n) (s : Fin 100 → ZMod 2) : BitAssignment n :=
  writeReg (writeReg β rAnc (fun k : Fin 50 => s ⟨50 + k.val, by omega⟩))
    rData (fun i : Fin 50 => s ⟨i.val, by omega⟩)

theorem lift102_apply_w25 {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n) (s : Fin 100 → ZMod 2)
    {i : Nat} (hi : i < 100) :
    lift102 rData rAnc β s (w25 rData rAnc i) = s ⟨i, hi⟩ := by
  unfold lift102 w25
  by_cases h1 : i < 50
  · simp only [h1, ↓reduceDIte, writeReg_apply_reg]
  · have h2 : i - 50 < 50 := by omega
    simp only [h1, h2, ↓reduceDIte]
    have hnot : rAnc ⟨i - 50, h2⟩ ∉ Set.range rData.wires :=
      fun ⟨k, hk⟩ => hdisj.ne_of_mem ⟨k, rfl⟩ ⟨⟨i - 50, h2⟩, rfl⟩ hk
    rw [writeReg_apply_of_not_mem _ _ _ _ hnot, writeReg_apply_reg]
    congr 1; ext; dsimp; omega

theorem update_lift102 {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n) (s : Fin 100 → ZMod 2)
    {i : Nat} (hi : i < 100) (v : ZMod 2) :
    Function.update (lift102 rData rAnc β s) (w25 rData rAnc i) v =
      lift102 rData rAnc β (Function.update s ⟨i, hi⟩ v) := by
  funext w
  by_cases hw : w = w25 rData rAnc i
  · subst hw
    rw [Function.update_self, lift102_apply_w25 rData rAnc hdisj β _ hi, Function.update_self]
  · rw [Function.update_of_ne hw]
    by_cases hD : w ∈ Set.range rData.wires
    · obtain ⟨k, rfl⟩ := hD
      unfold lift102
      rw [writeReg_apply_reg, writeReg_apply_reg, Function.update_of_ne]
      intro hk; apply hw; unfold w25
      have hk' : k.val = i := by simpa using congrArg Fin.val hk
      subst hk'; simp only [k.isLt, ↓reduceDIte]
    · by_cases hA : w ∈ Set.range rAnc.wires
      · obtain ⟨k, rfl⟩ := hA
        unfold lift102
        rw [writeReg_apply_of_not_mem _ _ _ _ hD, writeReg_apply_of_not_mem _ _ _ _ hD,
            writeReg_apply_reg, writeReg_apply_reg, Function.update_of_ne]
        intro hk; apply hw; unfold w25
        have hk' : 50 + k.val = i := by simpa using congrArg Fin.val hk
        have hnot50 : ¬ i < 50 := by omega
        have hsub : i - 50 < 50 := by omega
        simp only [hnot50, hsub, ↓reduceDIte]
        congr 1; ext; dsimp; omega
      · unfold lift102
        rw [writeReg_apply_of_not_mem _ _ _ _ hD, writeReg_apply_of_not_mem _ _ _ _ hD,
            writeReg_apply_of_not_mem _ _ _ _ hA, writeReg_apply_of_not_mem _ _ _ _ hA]

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2z_false : b2z false = 0 := rfl

theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_update (m : Fin 100 → Bool) (q : Fin 100) (v : Bool) :
    Function.update (fun k => b2z (m k)) q (b2z v) = fun k => b2z (Function.update m q v k) := by
  funext k; by_cases h : k = q <;> simp [h]

theorem b2z_evalQuadBool102 {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n) (m : Fin 100 → Bool) :
    ∀ (qs : List (Nat × Nat)),
      (∀ p ∈ qs, p.1 < 100 ∧ p.2 < 100) →
      b2z (evalQuadBool102 m qs) =
        ((qs.map fun p => (w25 rData rAnc p.1, w25 rData rAnc p.2)).map
          (fun p => lift102 rData rAnc β (fun k => b2z (m k)) p.1 *
                    lift102 rData rAnc β (fun k => b2z (m k)) p.2)).sum
  | [], _ => rfl
  | p :: qs, hqs => by
    have hp : p.1 < 100 ∧ p.2 < 100 := hqs p (List.mem_cons_self ..)
    have hrest : ∀ q ∈ qs, q.1 < 100 ∧ q.2 < 100 := fun q hq => hqs q (List.mem_cons_of_mem _ hq)
    dsimp only [evalQuadBool102]; simp only [List.map_cons, List.sum_cons]
    rw [dite_eq_left hp, b2z_xor, b2z_and,
        b2z_evalQuadBool102 rData rAnc hdisj β m qs hrest,
        lift102_apply_w25 rData rAnc hdisj β _ hp.1,
        lift102_apply_w25 rData rAnc hdisj β _ hp.2]

theorem b2z_evalLinBool102 {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n) (m : Fin 100 → Bool) :
    ∀ (ls : List Nat),
      (∀ c ∈ ls, c < 100) →
      b2z (evalLinBool102 m ls) =
        ((ls.map (w25 rData rAnc)).map (lift102 rData rAnc β (fun k => b2z (m k)))).sum
  | [], _ => rfl
  | c :: ls, hls => by
    have hc : c < 100 := hls c (List.mem_cons_self ..)
    have hrest : ∀ x ∈ ls, x < 100 := fun x hx => hls x (List.mem_cons_of_mem _ hx)
    dsimp only [evalLinBool102]; simp only [List.map_cons, List.sum_cons]
    rw [dite_eq_left hc, b2z_xor,
        b2z_evalLinBool102 rData rAnc hdisj β m ls hrest,
        lift102_apply_w25 rData rAnc hdisj β _ hc]

theorem execOp102_to_run {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n)
    {op : Op102} (hnp : op.noPhase = true) {m m' : Fin 100 → Bool} (h : execOp102 m op = some m') :
    Step.run (op.toStep rData rAnc) (lift102 rData rAnc β (fun k => b2z (m k))) =
      some (lift102 rData rAnc β (fun k => b2z (m' k))) := by
  cases op with
  | z _ => cases hnp
  | cz _ _ => cases hnp
  | hGadget _ _ _ _ _ => cases hnp
  | x q =>
    dsimp only [execOp102] at h
    split_ifs at h with hq
    injection h with hm'; subst hm'
    dsimp only [Op102.toStep, Step.run]
    rw [lift102_apply_w25 rData rAnc hdisj β _ hq,
        show b2z (m ⟨q, hq⟩) + 1 = b2z (!m ⟨q, hq⟩) by cases m ⟨q, hq⟩ <;> decide,
        update_lift102 rData rAnc hdisj β _ hq, b2z_update]
  | cx c t =>
    dsimp only [execOp102] at h
    split_ifs at h with hc
    injection h with hm'; subst hm'
    obtain ⟨hc102, ht102, hne⟩ := hc
    have hw_ne : w25 rData rAnc c ≠ w25 rData rAnc t :=
      fun e => hne (hw25_inj rData rAnc hdisj hc102 ht102 e)
    dsimp only [Op102.toStep, Step.run]
    rw [ite_eq_left hw_ne, lift102_apply_w25 rData rAnc hdisj β _ ht102,
        lift102_apply_w25 rData rAnc hdisj β _ hc102,
        show b2z (m ⟨t, ht102⟩) + b2z (m ⟨c, hc102⟩) = b2z (xor (m ⟨t, ht102⟩) (m ⟨c, hc102⟩)) by
          cases m ⟨t, ht102⟩ <;> cases m ⟨c, hc102⟩ <;> decide,
        update_lift102 rData rAnc hdisj β _ ht102, b2z_update]
  | and4t c1 c2 t =>
    dsimp only [execOp102] at h
    split_ifs at h with hc hmt
    injection h with hm'; subst hm'
    obtain ⟨hc1, hc2, ht, h12, h1t, h2t⟩ := hc
    have hw12 : w25 rData rAnc c1 ≠ w25 rData rAnc c2 :=
      fun e => h12 (hw25_inj rData rAnc hdisj hc1 hc2 e)
    have hw1t : w25 rData rAnc c1 ≠ w25 rData rAnc t :=
      fun e => h1t (hw25_inj rData rAnc hdisj hc1 ht e)
    have hw2t : w25 rData rAnc c2 ≠ w25 rData rAnc t :=
      fun e => h2t (hw25_inj rData rAnc hdisj hc2 ht e)
    dsimp only [Op102.toStep, Step.run]
    rw [ite_eq_left ⟨hw12, hw1t, hw2t⟩, lift102_apply_w25 rData rAnc hdisj β _ ht, hmt,
        ite_eq_left b2z_false, lift102_apply_w25 rData rAnc hdisj β _ hc1,
        lift102_apply_w25 rData rAnc hdisj β _ hc2,
        show b2z (m ⟨c1, hc1⟩) * b2z (m ⟨c2, hc2⟩) = b2z (m ⟨c1, hc1⟩ && m ⟨c2, hc2⟩) by
          cases m ⟨c1, hc1⟩ <;> cases m ⟨c2, hc2⟩ <;> decide,
        update_lift102 rData rAnc hdisj β _ ht, b2z_update]
  | rccx0 c1 c2 t =>
    dsimp only [execOp102] at h
    split_ifs at h with hc hmt
    injection h with hm'; subst hm'
    obtain ⟨hc1, hc2, ht, h12, h1t, h2t⟩ := hc
    have hw12 : w25 rData rAnc c1 ≠ w25 rData rAnc c2 :=
      fun e => h12 (hw25_inj rData rAnc hdisj hc1 hc2 e)
    have hw1t : w25 rData rAnc c1 ≠ w25 rData rAnc t :=
      fun e => h1t (hw25_inj rData rAnc hdisj hc1 ht e)
    have hw2t : w25 rData rAnc c2 ≠ w25 rData rAnc t :=
      fun e => h2t (hw25_inj rData rAnc hdisj hc2 ht e)
    have hguard : b2z (m ⟨c1, hc1⟩) * b2z (m ⟨c2, hc2⟩) * b2z (m ⟨t, ht⟩) = 0 := by
      rw [← b2z_and, ← b2z_and, hmt, b2z_false]
    dsimp only [Op102.toStep, Step.run]
    rw [ite_eq_left ⟨hw12, hw1t, hw2t⟩,
        lift102_apply_w25 rData rAnc hdisj β _ hc1,
        lift102_apply_w25 rData rAnc hdisj β _ hc2,
        lift102_apply_w25 rData rAnc hdisj β _ ht,
        ite_eq_left hguard,
        show b2z (m ⟨t, ht⟩) + b2z (m ⟨c1, hc1⟩) * b2z (m ⟨c2, hc2⟩) =
          b2z (xor (m ⟨t, ht⟩) (m ⟨c1, hc1⟩ && m ⟨c2, hc2⟩)) by
          rw [← b2z_and, ← b2z_xor],
        update_lift102 rData rAnc hdisj β _ ht, b2z_update]
  | rccx1 c1 c2 t =>
    dsimp only [execOp102] at h
    split_ifs at h with hc hmt
    injection h with hm'; subst hm'
    obtain ⟨hc1, hc2, ht, h12, h1t, h2t⟩ := hc
    have hw12 : w25 rData rAnc c1 ≠ w25 rData rAnc c2 :=
      fun e => h12 (hw25_inj rData rAnc hdisj hc1 hc2 e)
    have hw1t : w25 rData rAnc c1 ≠ w25 rData rAnc t :=
      fun e => h1t (hw25_inj rData rAnc hdisj hc1 ht e)
    have hw2t : w25 rData rAnc c2 ≠ w25 rData rAnc t :=
      fun e => h2t (hw25_inj rData rAnc hdisj hc2 ht e)
    have hnot : b2z (m ⟨t, ht⟩) + 1 = b2z (!m ⟨t, ht⟩) := by cases m ⟨t, ht⟩ <;> decide
    have hguard : b2z (m ⟨c1, hc1⟩) * b2z (m ⟨c2, hc2⟩) * (b2z (m ⟨t, ht⟩) + 1) = 0 := by
      rw [hnot, ← b2z_and, ← b2z_and, hmt, b2z_false]
    dsimp only [Op102.toStep, Step.run]
    rw [ite_eq_left ⟨hw12, hw1t, hw2t⟩,
        lift102_apply_w25 rData rAnc hdisj β _ hc1,
        lift102_apply_w25 rData rAnc hdisj β _ hc2,
        lift102_apply_w25 rData rAnc hdisj β _ ht,
        ite_eq_left hguard,
        show b2z (m ⟨t, ht⟩) + b2z (m ⟨c1, hc1⟩) * b2z (m ⟨c2, hc2⟩) =
          b2z (xor (m ⟨t, ht⟩) (m ⟨c1, hc1⟩ && m ⟨c2, hc2⟩)) by
          rw [← b2z_and, ← b2z_xor],
        update_lift102 rData rAnc hdisj β _ ht, b2z_update]
  | unand c1 c2 t =>
    dsimp only [execOp102] at h
    split_ifs at h with hc hmt
    injection h with hm'; subst hm'
    obtain ⟨hc1, hc2, ht, h12, h1t, h2t⟩ := hc
    have hw12 : w25 rData rAnc c1 ≠ w25 rData rAnc c2 :=
      fun e => h12 (hw25_inj rData rAnc hdisj hc1 hc2 e)
    have hw1t : w25 rData rAnc c1 ≠ w25 rData rAnc t :=
      fun e => h1t (hw25_inj rData rAnc hdisj hc1 ht e)
    have hw2t : w25 rData rAnc c2 ≠ w25 rData rAnc t :=
      fun e => h2t (hw25_inj rData rAnc hdisj hc2 ht e)
    dsimp only [Op102.toStep, Step.run]
    rw [ite_eq_left ⟨hw12, hw1t, hw2t⟩, lift102_apply_w25 rData rAnc hdisj β _ ht,
        lift102_apply_w25 rData rAnc hdisj β _ hc1,
        lift102_apply_w25 rData rAnc hdisj β _ hc2, hmt,
        show b2z (m ⟨c1, hc1⟩ && m ⟨c2, hc2⟩) = b2z (m ⟨c1, hc1⟩) * b2z (m ⟨c2, hc2⟩) by
          cases m ⟨c1, hc1⟩ <;> cases m ⟨c2, hc2⟩ <;> decide,
        ite_eq_left rfl, update_lift102 rData rAnc hdisj β _ ht,
        show (0 : ZMod 2) = b2z false from rfl, b2z_update]
  | unquad qs ls t =>
    dsimp only [execOp102] at h
    split_ifs at h with hc hmt
    injection h with hm'; subst hm'
    obtain ⟨hqs_v, hls_v, ht102⟩ := hc
    have hcond : (∀ p ∈ qs.map (fun p => (w25 rData rAnc p.1, w25 rData rAnc p.2)),
        p.1 ≠ p.2 ∧ p.1 ≠ w25 rData rAnc t ∧ p.2 ≠ w25 rData rAnc t) ∧
        w25 rData rAnc t ∉ ls.map (w25 rData rAnc) := by
      refine ⟨fun p hp => ?_, fun hmem => ?_⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        obtain ⟨hq1, hq2, h12, h1t, h2t⟩ := hqs_v q hq
        exact ⟨fun e => h12 (hw25_inj rData rAnc hdisj hq1 hq2 e),
               fun e => h1t (hw25_inj rData rAnc hdisj hq1 ht102 e),
               fun e => h2t (hw25_inj rData rAnc hdisj hq2 ht102 e)⟩
      · obtain ⟨c, hc_mem, hce⟩ := List.mem_map.mp hmem
        obtain ⟨hc102, hct⟩ := hls_v c hc_mem
        exact hct (hw25_inj rData rAnc hdisj hc102 ht102 hce)
    dsimp only [Op102.toStep, Step.run]
    rw [ite_eq_left hcond, lift102_apply_w25 rData rAnc hdisj β _ ht102, hmt]
    have hev : b2z (evalUnquad102 m qs ls) =
        (((qs.map fun p => (w25 rData rAnc p.1, w25 rData rAnc p.2)).map
          (fun p => lift102 rData rAnc β (fun k => b2z (m k)) p.1 *
                    lift102 rData rAnc β (fun k => b2z (m k)) p.2)).sum +
         ((ls.map (w25 rData rAnc)).map (lift102 rData rAnc β (fun k => b2z (m k)))).sum) := by
      unfold evalUnquad102
      rw [b2z_xor,
          b2z_evalQuadBool102 rData rAnc hdisj β m qs
            (fun p hp => ⟨(hqs_v p hp).1, (hqs_v p hp).2.1⟩),
          b2z_evalLinBool102 rData rAnc hdisj β m ls (fun c hc => (hls_v c hc).1)]
    rw [hev, ite_eq_left rfl, update_lift102 rData rAnc hdisj β _ ht102,
        show (0 : ZMod 2) = b2z false from rfl, b2z_update]

def compileLinWires {n : ℕ} (w : Nat → Wire n) (t : Nat) : List Nat → Circuit n
  | [] => .identity
  | c :: cs =>
      if h : w c ≠ w t then
        .seq (Circuit.CNOT (w c) (w t) h) (compileLinWires w t cs)
      else
        compileLinWires w t cs

def compileLinStep {n : ℕ} (w : Nat → Wire n) (t : Nat) (xc : Bool) (ls : List Nat) : Circuit n :=
  .seq (if xc then Circuit.X (w t) else .identity) (compileLinWires w t ls)

def compileHPosSteps {n : ℕ} (w : Nat → Wire n) (t : Nat) : List (Bool × List Nat) → Circuit n
  | [] => .identity
  | (xc, ls) :: rest =>
      .seq (compileLinStep w t xc ls)
        (.seq (Circuit.T (w t)) (compileHPosSteps w t rest))

def compileHNegSteps {n : ℕ} (w : Nat → Wire n) (t : Nat) : List (Bool × List Nat) → Circuit n
  | [] => .identity
  | (xc, ls) :: rest =>
      .seq (compileLinStep w t xc ls)
        (.seq (T_dag (w t)) (compileHNegSteps w t rest))

def hGadgetCircuit {n : ℕ} (w : Nat → Wire n) (t : Nat)
    (pos neg : List (Bool × List Nat)) (uc : Bool) (ul : List Nat) : Circuit n :=
  .seq (Circuit.H (w t))
    (.seq (compileHPosSteps w t pos)
      (.seq (compileHNegSteps w t neg)
        (.seq (compileLinStep w t uc ul)
          (.seq (Circuit.H (w t))
            (.seq (Circuit.S (w t)) (Circuit.Z (w t)))))))

theorem count_T_compileLinWires {n : ℕ} (w : Nat → Wire n) (t : Nat) :
    ∀ (ls : List Nat), (compileLinWires w t ls).count PrimitiveGate.T = 0
  | [] => rfl
  | c :: cs => by
    dsimp only [compileLinWires]
    split_ifs <;> simp [count_T_compileLinWires w t cs]

theorem count_TOFF_compileLinWires {n : ℕ} (w : Nat → Wire n) (t : Nat) :
    ∀ (ls : List Nat), (compileLinWires w t ls).count PrimitiveGate.TOFF = 0
  | [] => rfl
  | c :: cs => by
    dsimp only [compileLinWires]
    split_ifs <;> simp [count_TOFF_compileLinWires w t cs]

theorem count_T_compileLinStep {n : ℕ} (w : Nat → Wire n) (t : Nat) (xc : Bool) (ls : List Nat) :
    (compileLinStep w t xc ls).count PrimitiveGate.T = 0 := by
  unfold compileLinStep
  cases xc <;> simp [count_T_compileLinWires]

theorem count_TOFF_compileLinStep {n : ℕ} (w : Nat → Wire n) (t : Nat) (xc : Bool) (ls : List Nat) :
    (compileLinStep w t xc ls).count PrimitiveGate.TOFF = 0 := by
  unfold compileLinStep
  cases xc <;> simp [count_TOFF_compileLinWires]

theorem count_T_compileHPosSteps {n : ℕ} (w : Nat → Wire n) (t : Nat) :
    ∀ (steps : List (Bool × List Nat)),
      (compileHPosSteps w t steps).count PrimitiveGate.T = steps.length
  | [] => rfl
  | (xc, ls) :: rest => by
    dsimp only [compileHPosSteps, List.length_cons]
    rw [Circuit.count_seq, Circuit.count_seq, count_T_compileLinStep,
        show (Circuit.T (w t)).count PrimitiveGate.T = 1 from rfl,
        count_T_compileHPosSteps w t rest]
    omega

theorem count_TOFF_compileHPosSteps {n : ℕ} (w : Nat → Wire n) (t : Nat) :
    ∀ (steps : List (Bool × List Nat)),
      (compileHPosSteps w t steps).count PrimitiveGate.TOFF = 0
  | [] => rfl
  | (xc, ls) :: rest => by
    dsimp only [compileHPosSteps]
    rw [Circuit.count_seq, Circuit.count_seq, count_TOFF_compileLinStep,
        show (Circuit.T (w t)).count PrimitiveGate.TOFF = 0 from rfl,
        count_TOFF_compileHPosSteps w t rest]

theorem count_T_compileHNegSteps {n : ℕ} (w : Nat → Wire n) (t : Nat) :
    ∀ (steps : List (Bool × List Nat)),
      (compileHNegSteps w t steps).count PrimitiveGate.T = steps.length
  | [] => rfl
  | (xc, ls) :: rest => by
    dsimp only [compileHNegSteps, List.length_cons]
    rw [Circuit.count_seq, Circuit.count_seq, count_T_compileLinStep,
        show (T_dag (w t)).count PrimitiveGate.T = 1 from rfl,
        count_T_compileHNegSteps w t rest]
    omega

theorem count_TOFF_compileHNegSteps {n : ℕ} (w : Nat → Wire n) (t : Nat) :
    ∀ (steps : List (Bool × List Nat)),
      (compileHNegSteps w t steps).count PrimitiveGate.TOFF = 0
  | [] => rfl
  | (xc, ls) :: rest => by
    dsimp only [compileHNegSteps]
    rw [Circuit.count_seq, Circuit.count_seq, count_TOFF_compileLinStep,
        show (T_dag (w t)).count PrimitiveGate.TOFF = 0 from rfl,
        count_TOFF_compileHNegSteps w t rest]

theorem count_T_hGadgetCircuit {n : ℕ} (w : Nat → Wire n) (t : Nat)
    (pos neg : List (Bool × List Nat)) (uc : Bool) (ul : List Nat) :
    (hGadgetCircuit w t pos neg uc ul).count PrimitiveGate.T = pos.length + neg.length := by
  unfold hGadgetCircuit
  simp only [Circuit.count_seq, count_T_compileHPosSteps, count_T_compileHNegSteps,
    count_T_compileLinStep]
  change 0 + (pos.length + (neg.length + (0 + (0 + (0 + 0))))) = pos.length + neg.length
  omega

theorem count_TOFF_hGadgetCircuit {n : ℕ} (w : Nat → Wire n) (t : Nat)
    (pos neg : List (Bool × List Nat)) (uc : Bool) (ul : List Nat) :
    (hGadgetCircuit w t pos neg uc ul).count PrimitiveGate.TOFF = 0 := by
  unfold hGadgetCircuit
  simp only [Circuit.count_seq, count_TOFF_compileHPosSteps, count_TOFF_compileHNegSteps,
    count_TOFF_compileLinStep]
  rfl

def Op102.compile {Var : Type} {n : ℕ} (v : Var) (rData : QRegister 50 n) (rAnc : QRegister 50 n) :
    Op102 → DynamicCircuit Var n
  | .z q =>
      if q < 100 then .circuit (Circuit.Z (w25 rData rAnc q)) else .identity
  | .cz c1 c2 =>
      if c1 < 100 ∧ c2 < 100 ∧ c1 ≠ c2 then
        .circuit (fixupCZ (w25 rData rAnc c1) (w25 rData rAnc c2))
      else .identity
  | .hGadget t pos neg uc ul =>
      if checkHGadgetStatic t pos neg uc ul then
        .circuit (hGadgetCircuit (w25 rData rAnc) t pos neg uc ul)
      else .identity
  | g => (g.toStep rData rAnc).compile v

def compileList102 {Var : Type} {n : ℕ} (v : Var) (rData : QRegister 50 n) (rAnc : QRegister 50 n) :
    List Op102 → DynamicCircuit Var n
  | [] => .identity
  | g :: gs => .seq (g.compile v rData rAnc) (compileList102 v rData rAnc gs)

theorem Op102.count_T_compile {Var : Type} {n : ℕ} (v : Var)
    (rData : QRegister 50 n) (rAnc : QRegister 50 n) (g : Op102) :
    (g.compile v rData rAnc).count PrimitiveGate.T ≤ g.tCount := by
  cases g with
  | z q =>
    dsimp only [Op102.compile, Op102.tCount]
    split_ifs <;> rfl
  | cz c1 c2 =>
    dsimp only [Op102.compile, Op102.tCount]
    split_ifs <;> simp [DynamicCircuit.count, count_T_fixupCZ]
  | hGadget t pos neg uc ul =>
    dsimp only [Op102.compile, Op102.tCount]
    split_ifs
    · simp [DynamicCircuit.count, count_T_hGadgetCircuit]
    · exact Nat.zero_le _
  | x q => exact Step.count_T_compile v (.x (w25 rData rAnc q))
  | cx c t => exact Step.count_T_compile v (.cnot (w25 rData rAnc c) (w25 rData rAnc t))
  | and4t c1 c2 t =>
    exact Step.count_T_compile v
      (.and4t (w25 rData rAnc c1) (w25 rData rAnc c2) (w25 rData rAnc t))
  | rccx0 c1 c2 t =>
    exact Step.count_T_compile v
      (.rccx0 (w25 rData rAnc c1) (w25 rData rAnc c2) (w25 rData rAnc t))
  | rccx1 c1 c2 t =>
    exact Step.count_T_compile v
      (.rccx1 (w25 rData rAnc c1) (w25 rData rAnc c2) (w25 rData rAnc t))
  | unand c1 c2 t =>
    exact Step.count_T_compile v
      (.unand (w25 rData rAnc c1) (w25 rData rAnc c2) (w25 rData rAnc t))
  | unquad qs ls t =>
    exact Step.count_T_compile v
      (.unquad (qs.map fun p => (w25 rData rAnc p.1, w25 rData rAnc p.2))
        (ls.map (w25 rData rAnc)) (w25 rData rAnc t))

theorem Op102.count_TOFF_compile {Var : Type} {n : ℕ} (v : Var)
    (rData : QRegister 50 n) (rAnc : QRegister 50 n) (g : Op102) :
    (g.compile v rData rAnc).count PrimitiveGate.TOFF = 0 := by
  cases g with
  | z q =>
    dsimp only [Op102.compile]
    split_ifs <;> rfl
  | cz c1 c2 =>
    dsimp only [Op102.compile]
    split_ifs <;> simp [DynamicCircuit.count, count_TOFF_fixupCZ]
  | hGadget t pos neg uc ul =>
    dsimp only [Op102.compile]
    split_ifs <;> simp [DynamicCircuit.count, count_TOFF_hGadgetCircuit]
  | x q => exact Step.count_TOFF_compile v (.x (w25 rData rAnc q))
  | cx c t => exact Step.count_TOFF_compile v (.cnot (w25 rData rAnc c) (w25 rData rAnc t))
  | and4t c1 c2 t =>
    exact Step.count_TOFF_compile v
      (.and4t (w25 rData rAnc c1) (w25 rData rAnc c2) (w25 rData rAnc t))
  | rccx0 c1 c2 t =>
    exact Step.count_TOFF_compile v
      (.rccx0 (w25 rData rAnc c1) (w25 rData rAnc c2) (w25 rData rAnc t))
  | rccx1 c1 c2 t =>
    exact Step.count_TOFF_compile v
      (.rccx1 (w25 rData rAnc c1) (w25 rData rAnc c2) (w25 rData rAnc t))
  | unand c1 c2 t =>
    exact Step.count_TOFF_compile v
      (.unand (w25 rData rAnc c1) (w25 rData rAnc c2) (w25 rData rAnc t))
  | unquad qs ls t =>
    exact Step.count_TOFF_compile v
      (.unquad (qs.map fun p => (w25 rData rAnc p.1, w25 rData rAnc p.2))
        (ls.map (w25 rData rAnc)) (w25 rData rAnc t))

theorem count_T_compileList102 {Var : Type} {n : ℕ} (v : Var)
    (rData : QRegister 50 n) (rAnc : QRegister 50 n) :
    ∀ (ops : List Op102),
      (compileList102 v rData rAnc ops).count PrimitiveGate.T ≤ (ops.map Op102.tCount).sum
  | [] => le_rfl
  | g :: gs => by
    simp only [compileList102, DynamicCircuit.count, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (g.count_T_compile v rData rAnc) (count_T_compileList102 v rData rAnc gs)

theorem count_TOFF_compileList102 {Var : Type} {n : ℕ} (v : Var)
    (rData : QRegister 50 n) (rAnc : QRegister 50 n) :
    ∀ (ops : List Op102),
      (compileList102 v rData rAnc ops).count PrimitiveGate.TOFF = 0
  | [] => rfl
  | g :: gs => by
    simp only [compileList102, DynamicCircuit.count,
      g.count_TOFF_compile v rData rAnc, count_TOFF_compileList102 v rData rAnc gs]

def k25DynCircuit {Var : Type} {n : ℕ} (v : Var) (rData : QRegister 50 n) (rAnc : QRegister 50 n) :
    DynamicCircuit Var n :=
  compileList102 v rData rAnc fullK25Ops

theorem count_T_k25DynCircuit {Var : Type} {n : ℕ} (v : Var)
    (rData : QRegister 50 n) (rAnc : QRegister 50 n) :
    (k25DynCircuit v rData rAnc).count PrimitiveGate.T ≤ 3662 := by
  unfold k25DynCircuit
  exact (count_T_compileList102 v rData rAnc fullK25Ops).trans (le_of_eq tCount_fullK25Ops)

theorem count_TOFF_k25DynCircuit {Var : Type} {n : ℕ} (v : Var)
    (rData : QRegister 50 n) (rAnc : QRegister 50 n) :
    (k25DynCircuit v rData rAnc).count PrimitiveGate.TOFF = 0 :=
  count_TOFF_compileList102 v rData rAnc fullK25Ops

noncomputable def mFull {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (β : BitAssignment n) (k : Fin 100) : Bool :=
  decide (β (w25 rData rAnc k.val) = 1)

theorem mFull_lift102 {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n) (m : Fin 100 → Bool) :
    mFull rData rAnc (lift102 rData rAnc β (fun k => b2z (m k))) = m := by
  funext k
  dsimp only [mFull]
  rw [lift102_apply_w25 rData rAnc hdisj β _ k.isLt]
  cases m k <;> decide

noncomputable def omega8 : ℂ := (1 + Complex.I) / (Real.sqrt 2 : ℂ)
noncomputable def omega8_inv : ℂ := (1 - Complex.I) / (Real.sqrt 2 : ℂ)

noncomputable def phase3 (b0 b1 b2 : Bool) : ℂ :=
  bitSign (b2z b2) * bitPhaseI (b2z b1) * bitPhaseT (b2z b0)

noncomputable def phase3_inv (b0 b1 b2 : Bool) : ℂ :=
  bitSign (b2z b2) * (bitSign (b2z b1) * bitPhaseI (b2z b1)) * (if b0 then omega8_inv else 1)

noncomputable def twoBranch {n : ℕ} (β : BitAssignment n) (wt : Wire n)
    (c1 : ℂ) (dt b0 b1 b2 : Bool) : Fin (2 ^ n) → ℂ :=
  phase3 b0 b1 b2 • ket (Function.update β wt (b2z dt)) +
    (c1 * phase3_inv b0 b1 b2) • ket (Function.update β wt (b2z (!dt)))

noncomputable def hGadgetPhase (bt b1 b2 : Bool) : ℂ :=
  bitSign (b2z b2) *
    (if bt then (if b1 then Complex.I else -Complex.I) else 1)

theorem omega8_mul_omega8_inv : omega8 * omega8_inv = 1 := by
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow]; norm_cast; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  unfold omega8 omega8_inv
  ring_nf
  simp only [h2, hi2]
  ring

theorem phase3_mul_T (b0 b1 b2 dt : Bool) :
    let r := add1Bools b0 b1 b2 dt
    phase3 b0 b1 b2 * bitPhaseT (b2z dt) = phase3 r.1 r.2.1 r.2.2 := by
  dsimp only
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow]; norm_cast; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hi3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * hi2
  rcases b0 <;> rcases b1 <;> rcases b2 <;> rcases dt <;>
    simp only [add1Bools, phase3, bitSign, bitPhaseI, bitPhaseT, b2z,
      bne_self_eq_false, Bool.bne_false, Bool.false_bne,
      Bool.and_self, Bool.true_and, Bool.false_and,
      Bool.false_eq_true, one_ne_zero, ↓reduceIte] <;>
    (try ring_nf) <;> (try simp only [h2, hi2, hi3]) <;> ring

theorem phase3_inv_mul_T (b0 b1 b2 dt : Bool) :
    let r := add1Bools b0 b1 b2 dt
    phase3_inv b0 b1 b2 * bitPhaseT (b2z (!dt)) = omega8 * phase3_inv r.1 r.2.1 r.2.2 := by
  dsimp only
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow]; norm_cast; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hi3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * hi2
  rcases b0 <;> rcases b1 <;> rcases b2 <;> rcases dt <;>
    simp only [add1Bools, phase3_inv, omega8, omega8_inv, bitSign, bitPhaseI, bitPhaseT, b2z,
      bne_self_eq_false, Bool.bne_false, Bool.false_bne,
      Bool.and_self, Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, one_ne_zero, ↓reduceIte] <;>
    (try ring_nf) <;> (try simp only [h2, hi2, hi3]) <;> ring

theorem phase3_mul_T_dag (b0 b1 b2 dt : Bool) :
    let r := add7Bools b0 b1 b2 dt
    phase3 b0 b1 b2 * (bitSign (b2z dt) * (bitPhaseI (b2z dt) * bitPhaseT (b2z dt))) =
      phase3 r.1 r.2.1 r.2.2 := by
  dsimp only
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow]; norm_cast; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hi3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * hi2
  have hi4 : Complex.I ^ 4 = 1 := by linear_combination (Complex.I ^ 2 - 1) * hi2
  rcases b0 <;> rcases b1 <;> rcases b2 <;> rcases dt <;>
    simp only [add7Bools, phase3, bitSign, bitPhaseI, bitPhaseT, b2z,
      bne_self_eq_false, Bool.bne_false, Bool.false_bne,
      Bool.and_self, Bool.true_and, Bool.false_and,
      Bool.false_eq_true, one_ne_zero, ↓reduceIte] <;>
    (try ring_nf) <;> (try simp only [h2, hi2, hi3, hi4]) <;> ring

theorem phase3_inv_mul_T_dag (b0 b1 b2 dt : Bool) :
    let r := add7Bools b0 b1 b2 dt
    phase3_inv b0 b1 b2 * (bitSign (b2z (!dt)) * (bitPhaseI (b2z (!dt)) * bitPhaseT (b2z (!dt)))) =
      omega8_inv * phase3_inv r.1 r.2.1 r.2.2 := by
  dsimp only
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow]; norm_cast; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hi3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * hi2
  have hi4 : Complex.I ^ 4 = 1 := by linear_combination (Complex.I ^ 2 - 1) * hi2
  rcases b0 <;> rcases b1 <;> rcases b2 <;> rcases dt <;>
    simp only [add7Bools, phase3_inv, omega8_inv, bitSign, bitPhaseI, bitPhaseT, b2z,
      bne_self_eq_false, Bool.bne_false, Bool.false_bne,
      Bool.and_self, Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, one_ne_zero, ↓reduceIte] <;>
    (try ring_nf) <;> (try simp only [h2, hi2, hi3, hi4]) <;> ring

theorem b2z_decide_eq (z : ZMod 2) : b2z (decide (z = 1)) = z := by
  rcases bit_cases z with rfl | rfl <;> decide

theorem compileLinWires_mulVec_ket {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n) {t : Nat} (ht : t < 100) (v : ZMod 2) :
    ∀ (ls : List Nat),
      (∀ c ∈ ls, c < 100 ∧ c ≠ t) →
      (compileLinWires (w25 rData rAnc) t ls).eval.1.mulVec
          (ket (Function.update β (w25 rData rAnc t) v)) =
        ket (Function.update β (w25 rData rAnc t)
          (v + b2z (evalLinBool102 (mFull rData rAnc β) ls)))
  | [], _ => by
    dsimp only [compileLinWires, evalLinBool102]
    rw [b2z_false, add_zero]
    exact Matrix.one_mulVec _
  | c :: cs, hls => by
    obtain ⟨hc, hct⟩ := hls c (List.mem_cons_self ..)
    have hcs : ∀ x ∈ cs, x < 100 ∧ x ≠ t := fun x hx => hls x (List.mem_cons_of_mem _ hx)
    have hw_ne : w25 rData rAnc c ≠ w25 rData rAnc t :=
      fun e => hct (hw25_inj rData rAnc hdisj hc ht e)
    dsimp only [compileLinWires, evalLinBool102]
    rw [dite_eq_left hw_ne, dite_eq_left hc, seq_mulVec, ket_CNOT,
        Function.update_self, Function.update_of_ne hw_ne, Function.update_idem,
        compileLinWires_mulVec_ket rData rAnc hdisj β ht _ cs hcs]
    congr 2
    have hmc : β (w25 rData rAnc c) = b2z (mFull rData rAnc β ⟨c, hc⟩) :=
      (b2z_decide_eq _).symm
    rw [hmc, b2z_xor, add_assoc]

theorem compileLinStep_mulVec_ket {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n) {t : Nat} (ht : t < 100)
    (d xc : Bool) {ls : List Nat} (hls : ∀ c ∈ ls, c < 100 ∧ c ≠ t) :
    (compileLinStep (w25 rData rAnc) t xc ls).eval.1.mulVec
        (ket (Function.update β (w25 rData rAnc t) (b2z d))) =
      ket (Function.update β (w25 rData rAnc t)
        (b2z (xor d (xor xc (evalLinBool102 (mFull rData rAnc β) ls))))) := by
  unfold compileLinStep
  rw [seq_mulVec]
  cases xc
  · rw [ite_eq_right Bool.false_ne_true, Bool.false_xor]
    change (compileLinWires (w25 rData rAnc) t ls).eval.1.mulVec
      ((1 : Matrix _ _ ℂ).mulVec (ket (Function.update β (w25 rData rAnc t) (b2z d)))) = _
    rw [Matrix.one_mulVec,
        compileLinWires_mulVec_ket rData rAnc hdisj β ht (b2z d) ls hls, ← b2z_xor]
  · simp only [↓reduceIte, Bool.true_xor, ket_X, Function.update_self, Function.update_idem,
      show b2z d + 1 = b2z (!d) by cases d <;> decide,
      compileLinWires_mulVec_ket rData rAnc hdisj β ht (b2z (!d)) ls hls, ← b2z_xor]
    have hbx : ∀ a b : Bool, xor (!a) b = xor a (!b) := by decide
    rw [hbx]

theorem xor_not_left (a b : Bool) : xor (!a) b = !(xor a b) := by
  cases a <;> cases b <;> rfl

theorem compileLinStep_mulVec_twoBranch {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n) {t : Nat} (ht : t < 100)
    (c1 : ℂ) (dt b0 b1 b2 xc : Bool) {ls : List Nat} (hls : ∀ c ∈ ls, c < 100 ∧ c ≠ t) :
    (compileLinStep (w25 rData rAnc) t xc ls).eval.1.mulVec
        (twoBranch β (w25 rData rAnc t) c1 dt b0 b1 b2) =
      twoBranch β (w25 rData rAnc t) c1
        (xor dt (xor xc (evalLinBool102 (mFull rData rAnc β) ls))) b0 b1 b2 := by
  unfold twoBranch
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      compileLinStep_mulVec_ket rData rAnc hdisj β ht dt xc hls,
      compileLinStep_mulVec_ket rData rAnc hdisj β ht (!dt) xc hls,
      xor_not_left]

theorem compileHPosSteps_mulVec_twoBranch {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n) {t : Nat} (ht : t < 100) :
    ∀ (steps : List (Bool × List Nat)) (c1 : ℂ) (st : Bool × Bool × Bool × Bool),
      (∀ p ∈ steps, ∀ c ∈ p.2, c < 100 ∧ c ≠ t) →
      let st' := evalHPosBool (mFull rData rAnc β) steps st
      (compileHPosSteps (w25 rData rAnc) t steps).eval.1.mulVec
          (twoBranch β (w25 rData rAnc t) c1 st.1 st.2.1 st.2.2.1 st.2.2.2) =
        twoBranch β (w25 rData rAnc t) (c1 * omega8 ^ steps.length)
          st'.1 st'.2.1 st'.2.2.1 st'.2.2.2
  | [], c1, st, _ => by
    simp [compileHPosSteps, evalHPosBool]
  | (xc, ls) :: rest, c1, (dt, b0, b1, b2), hs => by
    have hls : ∀ c ∈ ls, c < 100 ∧ c ≠ t := hs (xc, ls) (List.mem_cons_self ..)
    have hrest : ∀ p ∈ rest, ∀ c ∈ p.2, c < 100 ∧ c ≠ t :=
      fun p hp => hs p (List.mem_cons_of_mem _ hp)
    dsimp only [compileHPosSteps, evalHPosBool]
    rw [seq_mulVec, seq_mulVec,
        compileLinStep_mulVec_twoBranch rData rAnc hdisj β ht c1 dt b0 b1 b2 xc hls]
    set dt' := xor dt (xor xc (evalLinBool102 (mFull rData rAnc β) ls))
    set r := add1Bools b0 b1 b2 dt'
    have hT_step : (Circuit.T (w25 rData rAnc t)).eval.1.mulVec
        (twoBranch β (w25 rData rAnc t) c1 dt' b0 b1 b2) =
        twoBranch β (w25 rData rAnc t) (c1 * omega8) dt' r.1 r.2.1 r.2.2 := by
      unfold twoBranch
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
          ket_T, ket_T, Function.update_self, Function.update_self,
          smul_smul, smul_smul, phase3_mul_T b0 b1 b2 dt',
          mul_assoc c1, phase3_inv_mul_T b0 b1 b2 dt', ← mul_assoc c1]
    rw [hT_step,
        compileHPosSteps_mulVec_twoBranch rData rAnc hdisj β ht rest (c1 * omega8)
          (dt', r.1, r.2.1, r.2.2) hrest]
    simp [List.length_cons, pow_succ', mul_assoc]

theorem compileHNegSteps_mulVec_twoBranch {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n) {t : Nat} (ht : t < 100) :
    ∀ (steps : List (Bool × List Nat)) (c1 : ℂ) (st : Bool × Bool × Bool × Bool),
      (∀ p ∈ steps, ∀ c ∈ p.2, c < 100 ∧ c ≠ t) →
      let st' := evalHNegBool (mFull rData rAnc β) steps st
      (compileHNegSteps (w25 rData rAnc) t steps).eval.1.mulVec
          (twoBranch β (w25 rData rAnc t) c1 st.1 st.2.1 st.2.2.1 st.2.2.2) =
        twoBranch β (w25 rData rAnc t) (c1 * omega8_inv ^ steps.length)
          st'.1 st'.2.1 st'.2.2.1 st'.2.2.2
  | [], c1, st, _ => by
    simp [compileHNegSteps, evalHNegBool]
  | (xc, ls) :: rest, c1, (dt, b0, b1, b2), hs => by
    have hls : ∀ c ∈ ls, c < 100 ∧ c ≠ t := hs (xc, ls) (List.mem_cons_self ..)
    have hrest : ∀ p ∈ rest, ∀ c ∈ p.2, c < 100 ∧ c ≠ t :=
      fun p hp => hs p (List.mem_cons_of_mem _ hp)
    dsimp only [compileHNegSteps, evalHNegBool]
    rw [seq_mulVec, seq_mulVec,
        compileLinStep_mulVec_twoBranch rData rAnc hdisj β ht c1 dt b0 b1 b2 xc hls]
    set dt' := xor dt (xor xc (evalLinBool102 (mFull rData rAnc β) ls))
    set r := add7Bools b0 b1 b2 dt'
    have hT_step : (T_dag (w25 rData rAnc t)).eval.1.mulVec
        (twoBranch β (w25 rData rAnc t) c1 dt' b0 b1 b2) =
        twoBranch β (w25 rData rAnc t) (c1 * omega8_inv) dt' r.1 r.2.1 r.2.2 := by
      unfold twoBranch
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
          ket_T_dag, ket_T_dag, Function.update_self, Function.update_self,
          smul_smul, smul_smul, phase3_mul_T_dag b0 b1 b2 dt',
          mul_assoc c1, phase3_inv_mul_T_dag b0 b1 b2 dt', ← mul_assoc c1]
    rw [hT_step,
        compileHNegSteps_mulVec_twoBranch rData rAnc hdisj β ht rest (c1 * omega8_inv)
          (dt', r.1, r.2.1, r.2.2) hrest]
    simp [List.length_cons, pow_succ', mul_assoc]

theorem hGadgetSuffix_mulVec_twoBranch {n : ℕ} (β : BitAssignment n) (wt : Wire n)
    (bt b1 b2 : Bool) :
    (Circuit.seq (Circuit.H wt) (Circuit.seq (Circuit.S wt) (Circuit.Z wt))).eval.1.mulVec
        ((Real.sqrt (1 / 2) : ℂ) • twoBranch β wt (bitSign (b2z bt)) false false b1 b2) =
      hGadgetPhase bt b1 b2 • ket (Function.update β wt (b2z (xor bt b1))) := by
  have hs2 : (Real.sqrt (1 / 2) : ℂ) ^ 2 = 1 / 2 := by
    norm_cast
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  unfold twoBranch
  simp only [seq_mulVec, ket_H, ket_S, ket_Z, Matrix.mulVec_smul, Matrix.mulVec_add,
    smul_add, smul_smul, Function.update_self, Function.update_idem]
  rcases bt <;> rcases b1 <;> rcases b2 <;>
    simp only [phase3, phase3_inv, hGadgetPhase, bitSign, bitPhaseI, bitPhaseT, b2z,
      bne_self_eq_false, Bool.bne_false, Bool.false_bne, Bool.not_false,
      Bool.false_eq_true, one_ne_zero, ↓reduceIte] <;>
    match_scalars <;> (try ring_nf) <;> (try simp only [hs2, hi2]) <;> ring

theorem hGadgetCircuit_mulVec_ket {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc)
    {t : Nat} {pos neg : List (Bool × List Nat)} {uc : Bool} {ul : List Nat}
    (hc : checkHGadgetStatic t pos neg uc ul = true) (β : BitAssignment n) :
    let res := evalHGadgetBool (mFull rData rAnc β) pos neg uc ul
    (hGadgetCircuit (w25 rData rAnc) t pos neg uc ul).eval.1.mulVec (ket β) =
      hGadgetPhase (mFull rData rAnc β ⟨t, checkHGadgetStatic_lt hc⟩) res.2.2.1 res.2.2.2 •
        ket (Function.update β (w25 rData rAnc t)
          (β (w25 rData rAnc t) + b2z res.2.2.1)) := by
  obtain ⟨ht, hlen, hpos, hneg, hul, hdt_f, hb0_f⟩ :=
    checkHGadgetStatic_sound (mFull rData rAnc β) hc
  set wt := w25 rData rAnc t
  set bt := mFull rData rAnc β ⟨t, ht⟩
  have hbt : β wt = b2z bt := (b2z_decide_eq _).symm
  have hH_init : (Circuit.H wt).eval.1.mulVec (ket β) =
      (Real.sqrt (1 / 2) : ℂ) • twoBranch β wt (bitSign (b2z bt)) false false false false := by
    rw [ket_H, hbt]
    unfold twoBranch phase3 phase3_inv
    simp [b2z, bitSign, bitPhaseI, bitPhaseT]
  unfold hGadgetCircuit
  rw [seq_mulVec, hH_init, seq_mulVec, Matrix.mulVec_smul,
      compileHPosSteps_mulVec_twoBranch rData rAnc hdisj β ht pos (bitSign (b2z bt))
        (false, false, false, false) hpos,
      seq_mulVec, Matrix.mulVec_smul,
      compileHNegSteps_mulVec_twoBranch rData rAnc hdisj β ht neg
        (bitSign (b2z bt) * omega8 ^ pos.length) _ hneg,
      seq_mulVec, Matrix.mulVec_smul,
      compileLinStep_mulVec_twoBranch rData rAnc hdisj β ht _ _ _ _ _ uc hul]
  have hpow :
      bitSign (b2z bt) * omega8 ^ pos.length * omega8_inv ^ neg.length = bitSign (b2z bt) := by
    rw [mul_assoc, ← hlen, ← mul_pow, omega8_mul_omega8_inv, one_pow, mul_one]
  set res := evalHGadgetBool (mFull rData rAnc β) pos neg uc ul
  change (Circuit.seq (Circuit.H wt) (Circuit.seq (Circuit.S wt) (Circuit.Z wt))).eval.1.mulVec
      ((Real.sqrt (1 / 2) : ℂ) • twoBranch β wt
        (bitSign (b2z bt) * omega8 ^ pos.length * omega8_inv ^ neg.length)
        res.1 res.2.1 res.2.2.1 res.2.2.2) = _
  rw [hpow, hdt_f, hb0_f, hGadgetSuffix_mulVec_twoBranch, hbt, b2z_xor]

noncomputable def rawRunOp102 {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n) :
    Op102 → BitAssignment n → Option (BitAssignment n)
  | .z _, β => some β
  | .cz _ _, β => some β
  | .hGadget t pos neg uc ul, β =>
      if checkHGadgetStatic t pos neg uc ul then
        let b1 := (evalHGadgetBool (mFull rData rAnc β) pos neg uc ul).2.2.1
        some (Function.update β (w25 rData rAnc t) (β (w25 rData rAnc t) + b2z b1))
      else some β
  | g, β => (g.toStep rData rAnc).rawRun β

noncomputable def rawRunList102 {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n) :
    List Op102 → BitAssignment n → Option (BitAssignment n)
  | [], β => some β
  | g :: gs, β => (rawRunOp102 rData rAnc g β).bind (rawRunList102 rData rAnc gs)

theorem rawRunOp102_of_exec {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n)
    {op : Op102} {m m' : Fin 100 → Bool} (h : execOp102 m op = some m') :
    rawRunOp102 rData rAnc op (lift102 rData rAnc β (fun k => b2z (m k))) =
      some (lift102 rData rAnc β (fun k => b2z (m' k))) := by
  cases op with
  | z q =>
    dsimp only [execOp102] at h
    split_ifs at h
    injection h with hm'; subst hm'
    rfl
  | cz c1 c2 =>
    dsimp only [execOp102] at h
    split_ifs at h
    injection h with hm'; subst hm'
    rfl
  | hGadget t pos neg uc ul =>
    dsimp only [execOp102] at h
    split_ifs at h with hc hmt
    injection h with hm'; subst hm'
    have ht : t < 100 := checkHGadgetStatic_lt hc
    dsimp only [rawRunOp102]
    rw [ite_eq_left hc, mFull_lift102 rData rAnc hdisj β m,
        lift102_apply_w25 rData rAnc hdisj β _ ht, hmt, b2z_false, zero_add,
        update_lift102 rData rAnc hdisj β _ ht, b2z_update]
  | x q => exact Step.rawRun_of_run (execOp102_to_run rData rAnc hdisj β rfl h)
  | cx c t => exact Step.rawRun_of_run (execOp102_to_run rData rAnc hdisj β rfl h)
  | and4t c1 c2 t => exact Step.rawRun_of_run (execOp102_to_run rData rAnc hdisj β rfl h)
  | rccx0 c1 c2 t => exact Step.rawRun_of_run (execOp102_to_run rData rAnc hdisj β rfl h)
  | rccx1 c1 c2 t => exact Step.rawRun_of_run (execOp102_to_run rData rAnc hdisj β rfl h)
  | unand c1 c2 t => exact Step.rawRun_of_run (execOp102_to_run rData rAnc hdisj β rfl h)
  | unquad qs ls t => exact Step.rawRun_of_run (execOp102_to_run rData rAnc hdisj β rfl h)

theorem rawRunList102_of_execList {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n) :
    ∀ (ops : List Op102) {m m' : Fin 100 → Bool},
      execList102 ops m = some m' →
      rawRunList102 rData rAnc ops (lift102 rData rAnc β (fun k => b2z (m k))) =
        some (lift102 rData rAnc β (fun k => b2z (m' k)))
  | [], _, _, h => by injection h with h'; subst h'; rfl
  | op :: ops, m, m', h => by
    dsimp only [execList102] at h
    cases hop : execOp102 m op with
    | none => rw [hop] at h; cases h
    | some m1 =>
      rw [hop] at h
      simp only [rawRunList102, rawRunOp102_of_exec rData rAnc hdisj β hop, Option.bind_some]
      exact rawRunList102_of_execList rData rAnc hdisj β ops h

theorem all_pNoStash_of_ne {t : Nat} {steps : List (Bool × List Nat)}
    (hs : ∀ p ∈ steps, ∀ c ∈ p.2, c < 100 ∧ c ≠ t) :
    (steps.all fun s => s.2.all (pNoStash t)) = true := by
  refine List.all_eq_true.mpr fun p hp => List.all_eq_true.mpr fun c hc => ?_
  unfold pNoStash
  rw [Bool.not_eq_true', beq_false_iff]
  exact (hs p hp c hc).2

theorem rawRunOp102_injective {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) {op : Op102} {β β' γ : BitAssignment n}
    (h : rawRunOp102 rData rAnc op β = some γ)
    (h' : rawRunOp102 rData rAnc op β' = some γ) : β = β' := by
  cases op with
  | z _ => exact (Option.some.inj h).trans (Option.some.inj h').symm
  | cz _ _ => exact (Option.some.inj h).trans (Option.some.inj h').symm
  | hGadget t pos neg uc ul =>
    dsimp only [rawRunOp102] at h h'
    by_cases hc : checkHGadgetStatic t pos neg uc ul = true
    · rw [ite_eq_left hc] at h h'
      simp only [Option.some.injEq] at h h'
      rw [← h'] at h
      obtain ⟨ht, _, hpos, hneg, hul, _, _⟩ :=
        checkHGadgetStatic_sound (mFull rData rAnc β) hc
      have hin : ∀ w : Fin 100, pNoStash t w.val = true →
          mFull rData rAnc β' w = mFull rData rAnc β w := by
        intro w hw
        unfold pNoStash at hw
        simp only [Bool.not_eq_true', beq_false_iff] at hw
        have hw_ne : w25 rData rAnc w.val ≠ w25 rData rAnc t :=
          fun e => hw (hw25_inj rData rAnc hdisj w.isLt ht e)
        dsimp only [mFull]
        rw [Step.update_apply_eq h hw_ne]
      have hul_b : (ul.all (pNoStash t)) = true := by
        refine List.all_eq_true.mpr fun c hc_mem => ?_
        unfold pNoStash
        rw [Bool.not_eq_true', beq_false_iff]
        exact (hul c hc_mem).2
      have hev : evalHGadgetBool (mFull rData rAnc β') pos neg uc ul =
          evalHGadgetBool (mFull rData rAnc β) pos neg uc ul :=
        evalHGadgetBool_congr_sub (pNoStash t) hin
          (all_pNoStash_of_ne hpos) (all_pNoStash_of_ne hneg) hul_b
      have hwt := congrFun h (w25 rData rAnc t)
      simp only [Function.update_self, hev] at hwt
      exact Step.eq_of_update_eq h (add_right_cancel hwt)
    · rw [ite_eq_right hc] at h h'
      exact (Option.some.inj h).trans (Option.some.inj h').symm
  | x q => exact Step.rawRun_injective (s := Op102.toStep rData rAnc (.x q)) h h'
  | cx c t => exact Step.rawRun_injective (s := Op102.toStep rData rAnc (.cx c t)) h h'
  | and4t c1 c2 t =>
    exact Step.rawRun_injective (s := Op102.toStep rData rAnc (.and4t c1 c2 t)) h h'
  | rccx0 c1 c2 t =>
    exact Step.rawRun_injective (s := Op102.toStep rData rAnc (.rccx0 c1 c2 t)) h h'
  | rccx1 c1 c2 t =>
    exact Step.rawRun_injective (s := Op102.toStep rData rAnc (.rccx1 c1 c2 t)) h h'
  | unand c1 c2 t =>
    exact Step.rawRun_injective (s := Op102.toStep rData rAnc (.unand c1 c2 t)) h h'
  | unquad qs ls t =>
    exact Step.rawRun_injective (s := Op102.toStep rData rAnc (.unquad qs ls t)) h h'

theorem rawRunList102_injective {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) :
    ∀ {ops : List Op102} {β β' γ : BitAssignment n},
      rawRunList102 rData rAnc ops β = some γ →
      rawRunList102 rData rAnc ops β' = some γ →
      β = β'
  | [], _, _, _, h, h' => (Option.some.inj h).trans (Option.some.inj h').symm
  | op :: ops, β, β', γ, h, h' => by
    simp only [rawRunList102, Option.bind_eq_some_iff] at h h'
    obtain ⟨δ, hδ, hγ⟩ := h
    obtain ⟨δ', hδ', hγ'⟩ := h'
    exact rawRunOp102_injective rData rAnc hdisj hδ
      ((rawRunList102_injective rData rAnc hdisj hγ hγ') ▸ hδ')

theorem exists_lowerKraus_toStep {Var : Type} [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (op : Op102)
    (hnp : op.noPhase = true)
    (hcomp : op.compile v rData rAnc = (op.toStep rData rAnc).compile v)
    (hraw : rawRunOp102 rData rAnc op = (op.toStep rData rAnc).rawRun) :
    ∃ R, LowerKraus (op.compile v rData rAnc).compile R ∧
      (∀ β (m m' : Fin 100 → Bool),
        execOp102 m op = some m' →
        R.mulVec (ket (lift102 rData rAnc β (fun k => b2z (m k)))) =
          bitSign (b2z (phaseOp102 m op)) • ket (lift102 rData rAnc β (fun k => b2z (m' k)))) ∧
      (∀ β, ∃ z : ℂ, R.mulVec (ket β) = z • optKet (rawRunOp102 rData rAnc op β)) := by
  rw [hcomp, hraw]
  obtain ⟨R, hK, hR, hRaw⟩ := (op.toStep rData rAnc).exists_lowerKraus v
  refine ⟨R, hK, fun β m m' hex => ?_, hRaw⟩
  rw [phaseOp102_of_noPhase m hnp, b2z_false, bitSign, ite_eq_left rfl, one_smul]
  exact hR _ _ (execOp102_to_run rData rAnc hdisj β hnp hex)

theorem exists_lowerKraus_op102 {Var : Type} [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (op : Op102) :
    ∃ R, LowerKraus (op.compile v rData rAnc).compile R ∧
      (∀ β (m m' : Fin 100 → Bool),
        execOp102 m op = some m' →
        R.mulVec (ket (lift102 rData rAnc β (fun k => b2z (m k)))) =
          bitSign (b2z (phaseOp102 m op)) • ket (lift102 rData rAnc β (fun k => b2z (m' k)))) ∧
      (∀ β, ∃ z : ℂ, R.mulVec (ket β) = z • optKet (rawRunOp102 rData rAnc op β)) := by
  cases op with
  | z q =>
    dsimp only [Op102.compile, rawRunOp102]
    by_cases hq : q < 100
    · rw [ite_eq_left hq]
      refine ⟨_, lowerKraus_circuit _, ?_, fun β => ⟨bitSign (β (w25 rData rAnc q)), ket_Z _ β⟩⟩
      intro β m m' hex
      dsimp only [execOp102] at hex
      rw [ite_eq_left hq] at hex
      injection hex with hm'; subst hm'
      dsimp only [phaseOp102]
      rw [dite_eq_left hq, ket_Z, lift102_apply_w25 rData rAnc hdisj β _ hq]
    · rw [ite_eq_right hq]
      refine ⟨1, lowerKraus_skip, ?_, fun β => ⟨1, by rw [one_smul, optKet, Matrix.one_mulVec]⟩⟩
      intro β m m' hex
      dsimp only [execOp102] at hex
      rw [ite_eq_right hq] at hex; cases hex
  | cz c1 c2 =>
    dsimp only [Op102.compile, rawRunOp102]
    by_cases hc : c1 < 100 ∧ c2 < 100 ∧ c1 ≠ c2
    · rw [ite_eq_left hc]
      have hw12 : w25 rData rAnc c1 ≠ w25 rData rAnc c2 :=
        fun e => hc.2.2 (hw25_inj rData rAnc hdisj hc.1 hc.2.1 e)
      refine ⟨_, lowerKraus_circuit _, ?_,
        fun β => ⟨bitSign (β (w25 rData rAnc c1) * β (w25 rData rAnc c2)),
          fixupCZ_mulVec_ket _ _ hw12 β⟩⟩
      intro β m m' hex
      dsimp only [execOp102] at hex
      rw [ite_eq_left hc] at hex
      injection hex with hm'; subst hm'
      dsimp only [phaseOp102]
      rw [dite_eq_left ⟨hc.1, hc.2.1⟩, fixupCZ_mulVec_ket _ _ hw12,
          lift102_apply_w25 rData rAnc hdisj β _ hc.1,
          lift102_apply_w25 rData rAnc hdisj β _ hc.2.1, ← b2z_and]
    · rw [ite_eq_right hc]
      refine ⟨1, lowerKraus_skip, ?_, fun β => ⟨1, by rw [one_smul, optKet, Matrix.one_mulVec]⟩⟩
      intro β m m' hex
      dsimp only [execOp102] at hex
      rw [ite_eq_right hc] at hex; cases hex
  | hGadget t pos neg uc ul =>
    dsimp only [Op102.compile, rawRunOp102]
    by_cases hc : checkHGadgetStatic t pos neg uc ul = true
    · rw [ite_eq_left hc]
      have ht : t < 100 := checkHGadgetStatic_lt hc
      refine ⟨_, lowerKraus_circuit _, ?_, fun β => ?_⟩
      · intro β m m' hex
        dsimp only [execOp102] at hex
        rw [dite_eq_left hc] at hex
        split_ifs at hex with hmt
        injection hex with hm'; subst hm'
        have hmain := hGadgetCircuit_mulVec_ket rData rAnc hdisj hc
          (lift102 rData rAnc β (fun k => b2z (m k)))
        dsimp only at hmain
        rw [mFull_lift102 rData rAnc hdisj β m] at hmain
        rw [hmain, hmt, lift102_apply_w25 rData rAnc hdisj β _ ht, hmt, b2z_false, zero_add,
            update_lift102 rData rAnc hdisj β _ ht, b2z_update]
        dsimp only [hGadgetPhase, phaseOp102]
        rw [ite_eq_right Bool.false_ne_true, mul_one]
      · rw [ite_eq_left hc]
        exact ⟨_, hGadgetCircuit_mulVec_ket rData rAnc hdisj hc β⟩
    · rw [ite_eq_right hc]
      refine ⟨1, lowerKraus_skip, ?_, fun β => ?_⟩
      · intro β m m' hex
        dsimp only [execOp102] at hex
        rw [dite_eq_right hc] at hex; cases hex
      · rw [ite_eq_right hc]
        exact ⟨1, by rw [one_smul, optKet, Matrix.one_mulVec]⟩
  | x q => exact exists_lowerKraus_toStep v rData rAnc hdisj (.x q) rfl rfl rfl
  | cx c t => exact exists_lowerKraus_toStep v rData rAnc hdisj (.cx c t) rfl rfl rfl
  | and4t c1 c2 t => exact exists_lowerKraus_toStep v rData rAnc hdisj (.and4t c1 c2 t) rfl rfl rfl
  | rccx0 c1 c2 t => exact exists_lowerKraus_toStep v rData rAnc hdisj (.rccx0 c1 c2 t) rfl rfl rfl
  | rccx1 c1 c2 t => exact exists_lowerKraus_toStep v rData rAnc hdisj (.rccx1 c1 c2 t) rfl rfl rfl
  | unand c1 c2 t => exact exists_lowerKraus_toStep v rData rAnc hdisj (.unand c1 c2 t) rfl rfl rfl
  | unquad qs ls t =>
    exact exists_lowerKraus_toStep v rData rAnc hdisj (.unquad qs ls t) rfl rfl rfl

theorem exists_lowerKraus_compileList102 {Var : Type} [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) :
    ∀ (ops : List Op102),
      ∃ R, LowerKraus (compileList102 v rData rAnc ops).compile R ∧
        (∀ β (m m' : Fin 100 → Bool),
          execList102 ops m = some m' →
          R.mulVec (ket (lift102 rData rAnc β (fun k => b2z (m k)))) =
            bitSign (b2z (phaseList102 ops m)) • ket (lift102 rData rAnc β (fun k => b2z (m' k)))) ∧
        (∀ β, ∃ z : ℂ, R.mulVec (ket β) = z • optKet (rawRunList102 rData rAnc ops β))
  | [] => by
    refine ⟨1, lowerKraus_skip, ?_,
      fun β => ⟨1, by rw [one_smul, rawRunList102, optKet, Matrix.one_mulVec]⟩⟩
    intro β m m' h
    injection h with hm'; subst hm'
    rw [Matrix.one_mulVec]
    simp [phaseList102, b2z_false, bitSign]
  | op :: ops => by
    obtain ⟨R₁, hK₁, hR₁, hRaw₁⟩ := exists_lowerKraus_op102 v rData rAnc hdisj op
    obtain ⟨R₂, hK₂, hR₂, hRaw₂⟩ := exists_lowerKraus_compileList102 v rData rAnc hdisj ops
    refine ⟨R₂ * R₁, hK₁.qSeq hK₂, ?_, ?_⟩
    · intro β m m' h
      dsimp only [execList102, phaseList102] at h ⊢
      cases hop : execOp102 m op with
      | none => rw [hop] at h; cases h
      | some m1 =>
        rw [hop] at h
        dsimp only at h ⊢
        rw [← Matrix.mulVec_mulVec, hR₁ β m m1 hop, Matrix.mulVec_smul,
            hR₂ β m1 m' h, smul_smul, b2z_xor, bitSign_add]
    · intro β
      obtain ⟨z₁, hz₁⟩ := hRaw₁ β
      rw [← Matrix.mulVec_mulVec, hz₁, Matrix.mulVec_smul]
      rcases hraw : rawRunOp102 rData rAnc op β with _ | δ
      · exact ⟨0, by simp [rawRunList102, hraw, optKet]⟩
      · obtain ⟨z₂, hz₂⟩ := hRaw₂ δ
        refine ⟨z₁ * z₂, ?_⟩
        simp only [rawRunList102, hraw, Option.bind_some, optKet, hz₂, smul_smul]



def z25 (y : Fin (2 ^ 25)) : Fin (2 ^ 25) :=
  ⟨z25Delta y.val, z25Delta_lt y.val⟩


theorem equalTableAddPerm_val_of_eq {k : ℕ} (f : Fin (2 ^ k) → Fin (2 ^ k))
    (j : Fin (2 ^ (2 * k))) (b x : Fin (2 ^ k))
    (hb : j.val % 2 ^ k = b.val) (hx : j.val / 2 ^ k = x.val) :
    ((equalTableAddPerm f) j : ℕ) = (b.val + (f x).val) % 2 ^ k + 2 ^ k * x.val := by
  have hjx : (Fin.cast (by rw [two_mul, pow_add]) j).divNat = x :=
    Fin.ext (by simp [Fin.divNat, hx])
  simp [equalTableAddPerm, splitEqualBasisEquiv, splitBasisEquiv, addRightShear,
    finProdFinEquiv_symm_apply, hjx, Fin.modNat, hb, Fin.val_add]

def m0OfBeta {n : ℕ} (rData : QRegister 50 n) (β : BitAssignment n) (w : Fin 100) : Bool :=
  if h : w.val < 50 then decide (β (rData ⟨w.val, h⟩) = 1) else false

theorem lift102_m0OfBeta {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (_ : rData.DisjointWires rAnc) (β : BitAssignment n)
    (hβ : localIdx rAnc β = 0) :
    lift102 rData rAnc β (fun w => b2z (m0OfBeta rData β w)) = β := by
  funext w
  unfold lift102
  by_cases hD : w ∈ Set.range rData.wires
  · obtain ⟨k, rfl⟩ := hD
    rw [writeReg_apply_reg]
    unfold m0OfBeta
    simp only [k.isLt, ↓reduceDIte, b2z_decide_eq]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hD]
    by_cases hA : w ∈ Set.range rAnc.wires
    · obtain ⟨k, rfl⟩ := hA
      rw [writeReg_apply_reg]
      unfold m0OfBeta
      dsimp only
      rw [dite_eq_right (by omega), eq_zero_of_localIdx_eq_zero rAnc β hβ k]
      rfl
    · rw [writeReg_apply_of_not_mem _ _ _ _ hA]

theorem lift102_apply_data {n : ℕ} (rData : QRegister 50 n) (rAnc52 : QRegister 50 n)
    (β : BitAssignment n) (s : Fin 100 → ZMod 2) (k : Fin 50) :
    lift102 rData rAnc52 β s (rData k) = s ⟨k.val, by omega⟩ := by
  unfold lift102
  rw [writeReg_apply_reg]

theorem lift102_apply_not_data {n : ℕ} (rData : QRegister 50 n) (rAnc : QRegister 50 n)
    (β : BitAssignment n) (s : Fin 100 → ZMod 2) {w : Wire n}
    (hD : w ∉ Set.range rData.wires)
    (hs : ∀ k : Fin 50, s ⟨50 + k.val, by omega⟩ = 0)
    (hβ : localIdx rAnc β = 0) :
    lift102 rData rAnc β s w = β w := by
  unfold lift102
  rw [writeReg_apply_of_not_mem _ _ _ _ hD]
  by_cases hA : w ∈ Set.range rAnc.wires
  · obtain ⟨k, rfl⟩ := hA
    rw [writeReg_apply_reg, hs k, eq_zero_of_localIdx_eq_zero rAnc β hβ k]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hA]

theorem realizesCleanSubroutine_compileList102 {Var : Type} [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (ops : List Op102)
    (rData : QRegister (2 * 25) n) (rAnc : QRegister 50 n)
    (hdisj : rData.DisjointWires rAnc) (σ : Equiv.Perm (Fin (2 ^ (2 * 25))))
    (hex : ∀ β, localIdx rAnc β = 0 →
      ∃ mf, execList102 ops (m0OfBeta rData β) = some mf ∧
        phaseList102 ops (m0OfBeta rData β) = false ∧
        lift102 rData rAnc β (fun k => b2z (mf k)) =
          writeReg β rData (basisBits (2 * 25) (σ (localIdx rData β)))) :
    RealizesCleanSubroutine rData rAnc hdisj (permutationUnitary σ)
      (compileList102 v rData rAnc ops).compile := by
  obtain ⟨R, hK, hR, hRaw⟩ := exists_lowerKraus_compileList102 v rData rAnc hdisj ops
  refine realizesCleanSubroutine_of_lowerKraus rData rAnc hdisj _ hK
    (matrix_ext_ket fun β => ?_)
  have hE : ∀ γ, (rData.embedUnitary (permutationUnitary σ)).1.mulVec (ket γ) =
      ket (writeReg γ rData (basisBits (2 * 25) (σ (localIdx rData γ)))) := fun γ => by
    have h := embedMatrix_permMatrix_mulVec_ket rData σ⁻¹ γ
    rw [Equiv.Perm.inv_def, Equiv.symm_symm] at h
    rw [QRegister.embedUnitary_val]
    exact h
  have hanc : ∀ γ δ, localIdx rAnc (writeReg γ rData δ) = localIdx rAnc γ :=
    fun γ δ => localIdx_writeReg_of_disjoint γ rData rAnc hdisj δ
  simp only [← Matrix.mulVec_mulVec, basisOutcomeProjector_mulVec_ket]
  by_cases hβ : localIdx rAnc β = 0
  · obtain ⟨mf, hex_β, hph_β, hwrite_β⟩ := hex β hβ
    have hR_β := hR β (m0OfBeta rData β) mf hex_β
    rw [lift102_m0OfBeta rData rAnc hdisj β hβ, hph_β, b2z_false, bitSign, ite_eq_left rfl,
        one_smul, hwrite_β] at hR_β
    rw [hR_β, ite_eq_left hβ, hE, basisOutcomeProjector_mulVec_ket, hanc, ite_eq_left hβ]
  · rw [ite_eq_right hβ, Matrix.mulVec_zero, Matrix.mulVec_zero]
    obtain ⟨z, hz⟩ := hRaw β
    rw [hz, Matrix.mulVec_smul]
    rcases hγ : rawRunList102 rData rAnc ops β with _ | γ
    · simp [optKet]
    · rw [optKet, basisOutcomeProjector_mulVec_ket, ite_eq_right, smul_zero]
      intro hγ0
      have h0 :
          localIdx rAnc
            (writeReg γ rData (basisBits (2 * 25) (σ.symm (localIdx rData γ)))) = 0 := by
        rw [hanc]; exact hγ0
      set β_pre := writeReg γ rData (basisBits (2 * 25) (σ.symm (localIdx rData γ)))
      obtain ⟨mf, hex_pre, _, hwrite_pre⟩ := hex β_pre h0
      have hraw_pre := rawRunList102_of_execList rData rAnc hdisj β_pre ops hex_pre
      rw [lift102_m0OfBeta rData rAnc hdisj β_pre h0, hwrite_pre] at hraw_pre
      simp only [β_pre, localIdx_writeReg, basisBitsEquiv_symm_basisBits, Equiv.apply_symm_apply,
        writeReg_writeReg, writeReg_self] at hraw_pre
      exact hβ (rawRunList102_injective rData rAnc hdisj hγ hraw_pre ▸ h0)

attribute [irreducible] lift102 k25DynCircuit

theorem localIdx_eq_sumBits : ∀ {m n : ℕ} (r : QRegister m n) (β : BitAssignment n),
    (localIdx r β : ℕ) = sumBits m (fun k => if h : k < m then decide (β (r ⟨k, h⟩) = 1) else false)
  | 0, _, _, _ => by simp [sumBits]
  | m + 1, n, r, β => by
      have h1 := localIdx_val_split r m 1 (by omega) β
      have hsl0 : (localIdx (r.slice 0 m (by omega)) β : ℕ) =
          sumBits m (fun k => if h : k < m + 1 then decide (β (r ⟨k, h⟩) = 1) else false) := by
        rw [localIdx_eq_sumBits]
        refine sumBits_congr fun k hk => ?_
        rw [dite_eq_left hk, dite_eq_left (by omega)]
        have hrw : (r.slice 0 m (by omega)).wires ⟨k, hk⟩ = r.wires ⟨k, by omega⟩ := by
          simp [QRegister.slice, QRegister.block]
        rw [hrw]
      have hsl1 : (localIdx (r.slice m 1 (by omega)) β : ℕ) =
          (decide (β (r ⟨m, by omega⟩) = 1)).toNat := by
        have hv := localIdx_val_succ (r.slice m 1 (by omega)) β
        have htail : (localIdx (regTail (r.slice m 1 (by omega))) β : ℕ) = 0 :=
          Nat.lt_one_iff.mp (localIdx _ _).isLt
        rw [htail, mul_zero, add_zero] at hv
        have hr0 : (r.slice m 1 (by omega)) 0 = r ⟨m, by omega⟩ := by
          simpa using QRegister.slice_apply r m 1 (by omega) 0
        rw [hr0] at hv
        rcases bit_cases (β (r ⟨m, by omega⟩)) with h0 | h1'
        · rw [h0, ZMod.val_zero] at hv; simp [h0, hv]
        · rw [h1', ZMod.val_one] at hv; simp [h1', hv]
      rw [h1, hsl0, hsl1, sumBits_succ, dite_eq_left (by omega)]

theorem outVal102_testBit (m : Fin 100 → Bool) {k : Nat} (hk : k < 25) :
    m ⟨k, by omega⟩ = (outVal102 m).testBit k := by
  have htb := sumBits_testBit 25 (fun j => if h : 0 + j < 100 then m ⟨0 + j, h⟩ else false) k hk
  rw [dite_eq_left (by omega)] at htb
  exact (congrArg m (Fin.ext (Nat.zero_add k).symm)).trans htb.symm

theorem m0OfBeta_in {n : ℕ} (rData : QRegister (2 * 25) n) (β : BitAssignment n)
    (i : Nat) (hi : i < 25) :
    m0OfBeta rData β ⟨25 + i, by omega⟩ =
      (localIdx (rData.slice 25 25 (by omega)) β).val.testBit i := by
  rw [localIdx_eq_sumBits _ β, sumBits_testBit 25 _ i hi, dite_eq_left hi]
  dsimp only [m0OfBeta]
  rw [dite_eq_left (by omega)]
  have hrw : (rData.slice 25 25 (by omega)).wires ⟨i, hi⟩ = rData.wires ⟨25 + i, by omega⟩ :=
    QRegister.slice_apply rData 25 25 (by omega) ⟨i, hi⟩
  rw [hrw]

theorem sliceVal25_m0OfBeta {n : ℕ} (rData : QRegister (2 * 25) n) (β : BitAssignment n) :
    sliceVal 25 25 (m0OfBeta rData β) = (localIdx (rData.slice 25 25 (by omega)) β : ℕ) := by
  rw [localIdx_eq_sumBits _ β]
  unfold sliceVal
  refine sumBits_congr fun k hk => ?_
  rw [dite_eq_left (by omega : 25 + k < 100), dite_eq_left hk]
  dsimp only [m0OfBeta]
  rw [dite_eq_left (by omega)]
  have hrw : (rData.slice 25 25 (by omega)).wires ⟨k, hk⟩ = rData.wires ⟨25 + k, by omega⟩ :=
    QRegister.slice_apply rData 25 25 (by omega) ⟨k, hk⟩
  rw [hrw]

theorem m0OfBeta_clean {n : ℕ} (rData : QRegister 50 n) (β : BitAssignment n)
    (w : Fin 100) (hw : 50 ≤ w.val) :
    m0OfBeta rData β w = false := by
  dsimp only [m0OfBeta]; rw [dite_eq_right (by omega)]

theorem outVal102_m0OfBeta {n : ℕ} (rData : QRegister (2 * 25) n) (β : BitAssignment n) :
    outVal102 (m0OfBeta rData β) = (localIdx (rData.slice 0 25 (by omega)) β : ℕ) := by
  rw [localIdx_eq_sumBits _ β]
  unfold outVal102 sliceVal
  refine sumBits_congr fun k hk => ?_
  rw [dite_eq_left (by omega : 0 + k < 100), dite_eq_left hk]
  dsimp only [m0OfBeta]
  rw [dite_eq_left (by omega)]
  have hrw : (rData.slice 0 25 (by omega)).wires ⟨k, hk⟩ = rData.wires ⟨0 + k, by omega⟩ :=
    QRegister.slice_apply rData 0 25 (by omega) ⟨k, hk⟩
  rw [hrw]

attribute [local irreducible] outVal102 m0OfBeta

theorem mod2_eq_zero_or_one (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := by omega

theorem mod_pow25_eq (n : ℕ) : n % 2 ^ 25 = n % 33554432 :=
  congrArg (n % ·) (by norm_num : 2 ^ 25 = 33554432)

theorem mul_pow25_eq (n : ℕ) : 2 ^ 25 * n = 33554432 * n :=
  congrArg (· * n) (by norm_num : 2 ^ 25 = 33554432)

theorem bench_step_eq_perm_bit {n : ℕ}
    (rData : QRegister (2 * 25) n) (rAnc : QRegister 50 n)
    (β : BitAssignment n) (hβ : localIdx rAnc β = 0)
    (m0 m7 : Fin 100 → Bool)
    (y outV : ℕ)
    (hm0_in : ∀ i : Nat, (hi : i < 25) → m0 ⟨25 + i, by omega⟩ = y.testBit i)
    (hm0_out : outVal102 m0 = outV)
    (hIn7 : ∀ w : Fin 100, 25 ≤ w.val → w.val < 50 → m7 w = m0 w)
    (hClean7 : ∀ w : Fin 100, 50 ≤ w.val → m7 w = false)
    (hout7 : outVal102 m7 = (outVal102 m0 + z25Delta y) % 33554432)
    (hperm_val : ((equalTableAddPerm z25) (localIdx rData β)).val =
      (outV + z25Delta y) % 33554432 + 33554432 * y) :
    lift102 rData rAnc β (fun k => b2z (m7 k)) =
      writeReg β rData (basisBits (q := 2 * 25) ((equalTableAddPerm z25) (localIdx rData β))) := by
  funext w
  by_cases hD : w ∈ Set.range rData.wires
  · obtain ⟨k, rfl⟩ := hD
    rw [lift102_apply_data, writeReg_apply_reg, basisBits_eq_div_mod, hperm_val]
    by_cases hk25 : k.val < 25
    · rw [outVal102_testBit m7 hk25, hout7, hm0_out, Nat.testBit_eq_decide_div_mod_eq]
      have hmul25 : 33554432 = 2 ^ k.val * (2 * 2 ^ (24 - k.val)) := by
        rw [show (33554432 : ℕ) = 2 ^ 25 by norm_num, ← mul_assoc, ← pow_succ, ← pow_add,
            show k.val + 1 + (24 - k.val) = 25 by omega]
      rw [show (outV + z25Delta y) % 33554432 + 33554432 * y =
            (outV + z25Delta y) % 33554432 + 2 ^ k.val * (2 * (2 ^ (24 - k.val) * y)) from
          congrArg ((outV + z25Delta y) % 33554432 + ·) (by rw [hmul25]; ring),
        Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
      rcases mod2_eq_zero_or_one (((outV + z25Delta y) % 33554432) / 2 ^ k.val) with h0 | h1
      · simp [h0, b2z]
      · simp [h1, b2z]
    · have hm0_k : m0 ⟨k.val, by omega⟩ = y.testBit (k.val - 25) := by
        have h1 := hm0_in (k.val - 25) (by omega)
        have hfin : (⟨25 + (k.val - 25), by omega⟩ : Fin 100) = ⟨k.val, by omega⟩ :=
          Fin.ext (by dsimp only; omega)
        rwa [hfin] at h1
      rw [hIn7 ⟨k.val, by omega⟩ (by dsimp only; omega) (by dsimp only; omega),
          hm0_k, Nat.testBit_eq_decide_div_mod_eq]
      have hpowk : 2 ^ k.val = 33554432 * 2 ^ (k.val - 25) := by
        rw [show (33554432 : ℕ) = 2 ^ 25 by norm_num, ← pow_add,
          show 25 + (k.val - 25) = k.val by omega]
      rw [hpowk, ← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_left _ _ (by positivity),
          Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity)), zero_add]
      rcases mod2_eq_zero_or_one (y / 2 ^ (k.val - 25)) with h0 | h1
      · simp [h0, b2z]
      · simp [h1, b2z]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hD]
    exact lift102_apply_not_data rData rAnc β _ hD
      (fun k => by rw [hClean7 ⟨50 + k.val, by omega⟩ (by dsimp only; omega)]; rfl) hβ

end ArcsinImpl

end QuantumComputation.Specs
