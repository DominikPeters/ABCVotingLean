import ABCVoting.Axioms.JRAxioms

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
  intro h_ejr_plus
  intro S l h_S_subset hl_pos ⟨h_large, h_common⟩
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

end ABCInstance
