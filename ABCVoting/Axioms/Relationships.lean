import ABCVoting.Axioms.JRAxioms
import ABCVoting.Axioms.Core

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- IMPLICATIONS BETWEEN AXIOMS
-- ============================================================================

/--
EJR+ implies EJR: If a committee satisfies EJR+ (the stronger condition),
then it automatically satisfies EJR (the weaker condition).

**Proof sketch:**
Suppose W satisfies EJR+ and S is ℓ-cohesive.
- If all common approvals are in W, then any voter in S has ≥ ℓ approved candidates.
- Otherwise, some common approval c is not in W. Since S is ℓ-large and all voters
  in S approve c, EJR+ applies and gives us a voter with ≥ ℓ approved candidates.
-/
theorem ejr_plus_implies_ejr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_ejr_plus W → inst.is_ejr W := by
  intro h_ejr_plus S l h_S_subset hl_pos ⟨h_large, h_common⟩
  -- Either all common approvals are in W, or some is missing
  by_cases h_sub : inst.common_approvals S ⊆ W
  -- Case 1: All common approvals in W → any voter in S has ≥ l in W
  · obtain ⟨i, hi⟩ := l_large_nonempty inst S l hl_pos h_large
    refine ⟨i, hi, h_common.trans (Finset.card_le_card ?_)⟩
    exact fun c hc => Finset.mem_inter.mpr
      ⟨h_sub hc, (mem_common_approvals_iff inst S c).mp hc |>.2 i hi⟩
  -- Case 2: Some common approval c ∉ W → apply EJR+
  · obtain ⟨c, hc_common, hc_not_in_W⟩ := Finset.not_subset.mp h_sub
    have hc := (mem_common_approvals_iff inst S c).mp hc_common
    exact h_ejr_plus S l h_S_subset hl_pos
      ⟨h_large, c, Finset.mem_sdiff.mpr ⟨hc.1, hc_not_in_W⟩, hc.2⟩

/--
EJR implies JR: JR is the special case of EJR with ℓ = 1.
-/
theorem ejr_implies_jr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_ejr W → inst.is_jr W := by
  intro h_ejr S h_S_subset h_cond
  exact h_ejr S 1 h_S_subset (le_refl 1) h_cond

/--
EJR implies PJR: If some voter has utility ≥ ℓ, then the coalition's
coverage is also ≥ ℓ (since that voter's approved candidates are in the union).
-/
theorem ejr_implies_pjr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_ejr W → inst.is_pjr W := by
  intro h_ejr S l h_S_subset hl_pos h_cond
  obtain ⟨i, hi_in_S, hi_util⟩ := h_ejr S l h_S_subset hl_pos h_cond
  -- The voter i's approved candidates in W are a subset of the coalition's coverage
  calc (W ∩ inst.union_approvals S).card
      ≥ (W ∩ inst.approves i).card := by
        apply Finset.card_le_card
        intro c hc
        simp only [mem_inter, union_approvals, mem_biUnion] at hc ⊢
        exact ⟨hc.1, i, hi_in_S, hc.2⟩
    _ ≥ l := hi_util

/--
PJR+ implies PJR: Same structure as EJR+ implies EJR.
-/
theorem pjr_plus_implies_pjr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_pjr_plus W → inst.is_pjr W := by
  intro h_pjr_plus S l h_S_subset hl_pos ⟨h_large, h_common⟩
  by_cases h_sub : inst.common_approvals S ⊆ W
  -- Case 1: All common approvals in W → coalition coverage ≥ l
  · obtain ⟨i, hi⟩ := l_large_nonempty inst S l hl_pos h_large
    have h_common_subset_union : inst.common_approvals S ⊆ inst.union_approvals S := by
      intro c hc
      simp only [union_approvals, mem_biUnion]
      exact ⟨i, hi, (mem_common_approvals_iff inst S c).mp hc |>.2 i hi⟩
    calc (W ∩ inst.union_approvals S).card
        ≥ (inst.common_approvals S).card := by
          apply Finset.card_le_card
          intro c hc
          exact mem_inter.mpr ⟨h_sub hc, h_common_subset_union hc⟩
      _ ≥ l := h_common
  -- Case 2: Some common approval c ∉ W → apply PJR+
  · obtain ⟨c, hc_common, hc_not_in_W⟩ := Finset.not_subset.mp h_sub
    have hc := (mem_common_approvals_iff inst S c).mp hc_common
    exact h_pjr_plus S l h_S_subset hl_pos
      ⟨h_large, c, Finset.mem_sdiff.mpr ⟨hc.1, hc_not_in_W⟩, hc.2⟩

/--
Core implies FJR: If u_i(W) ≥ u_i(T) for some voter, and all voters have u_i(T) ≥ β,
then that voter has u_i(W) ≥ β.
-/
theorem core_implies_fjr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_in_core W → inst.is_fjr W := by
  intro h_core S T l β h_S_subset h_T_subset hl_pos hβ_pos ⟨h_large, h_T_small, h_all_β⟩
  obtain ⟨i, hi_in_S, hi_pref⟩ := h_core S T l h_S_subset h_T_subset hl_pos ⟨h_large, h_T_small⟩
  refine ⟨i, hi_in_S, ?_⟩
  calc (W ∩ inst.approves i).card
      ≥ (T ∩ inst.approves i).card := hi_pref
    _ = (inst.approves i ∩ T).card := by rw [inter_comm]
    _ ≥ β := h_all_β i hi_in_S

/--
FJR implies EJR: EJR is a special case of FJR where T is the common approvals
and β = ℓ. Since every voter in S approves all of common_approvals(S), each has
u_i(T) ≥ ℓ.
-/
theorem fjr_implies_ejr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_fjr W → inst.is_ejr W := by
  intro h_fjr S l h_S_subset hl_pos ⟨h_large, h_common⟩
  -- Take T to be a subset of common_approvals of size exactly l
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq h_common
  have hT_cand : T ⊆ inst.candidates := by
    intro c hc
    exact ((mem_common_approvals_iff inst S c).mp (hT_sub hc)).1
  have hT_all_l : ∀ i ∈ S, (inst.approves i ∩ T).card ≥ l := by
    intro i hi
    have : T ⊆ inst.approves i := by
      intro c hc
      exact ((mem_common_approvals_iff inst S c).mp (hT_sub hc)).2 i hi
    simp only [inter_eq_right.mpr this, hT_card, le_refl]
  exact h_fjr S T l l h_S_subset hT_cand hl_pos hl_pos ⟨h_large, hT_card.le, hT_all_l⟩

/--
FJR implies FPJR: Same argument as EJR implies PJR.
-/
theorem fjr_implies_fpjr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_fjr W → inst.is_fpjr W := by
  intro h_fjr S T l β h_S_subset h_T_subset hl_pos hβ_pos h_cond
  obtain ⟨i, hi_in_S, hi_util⟩ := h_fjr S T l β h_S_subset h_T_subset hl_pos hβ_pos h_cond
  calc (W ∩ inst.union_approvals S).card
      ≥ (W ∩ inst.approves i).card := by
        apply Finset.card_le_card
        intro c hc
        simp only [mem_inter, union_approvals, mem_biUnion] at hc ⊢
        exact ⟨hc.1, i, hi_in_S, hc.2⟩
    _ ≥ β := hi_util

/--
FPJR implies PJR: PJR is a special case of FPJR where T is the common approvals
and β = ℓ.
-/
theorem fpjr_implies_pjr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_fpjr W → inst.is_pjr W := by
  intro h_fpjr S l h_S_subset hl_pos ⟨h_large, h_common⟩
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq h_common
  have hT_cand : T ⊆ inst.candidates := by
    intro c hc
    exact ((mem_common_approvals_iff inst S c).mp (hT_sub hc)).1
  have hT_all_l : ∀ i ∈ S, (inst.approves i ∩ T).card ≥ l := by
    intro i hi
    have : T ⊆ inst.approves i := by
      intro c hc
      exact ((mem_common_approvals_iff inst S c).mp (hT_sub hc)).2 i hi
    simp only [inter_eq_right.mpr this, hT_card, le_refl]
  exact h_fpjr S T l l h_S_subset hT_cand hl_pos hl_pos ⟨h_large, hT_card.le, hT_all_l⟩

end ABCInstance
