import ABCVoting.Rules.PAV.Defs
import ABCVoting.Axioms.Pareto

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C]

-- ============================================================================
-- PAV SATISFIES PARETO OPTIMALITY
-- ============================================================================

/--
Key lemma: If W' Pareto dominates W, then the PAV score of W' is strictly higher
than the PAV score of W.

**Proof:** Use harmonic monotonicity for weak inequalities and harmonic strict
monotonicity for the voter with strict preference improvement.
-/
lemma pareto_dominates_implies_higher_score (inst : ABCInstance V C) (W W' : Finset C)
    (h_dom : inst.pareto_dominates W' W) :
    inst.pav_score W < inst.pav_score W' := by
  obtain ⟨h_all_weak, j, hj_voter, hj_strict⟩ := h_dom
  unfold pav_score
  apply Finset.sum_lt_sum
  · exact fun i hi => harmonic_mono (h_all_weak i hi)
  · exact ⟨j, hj_voter, harmonic_strict_mono hj_strict⟩

/--
**Main Theorem: PAV winners are Pareto optimal.**

If a committee W is a PAV winner, then no other committee of size k Pareto dominates it.

**Proof sketch:** Suppose W is a PAV winner but some W' of size k Pareto dominates W.
By `pareto_dominates_implies_higher_score`, we have pav_score(W') > pav_score(W).
But W being a PAV winner means pav_score(W') ≤ pav_score(W) for all W' of size k.
This is a contradiction.
-/
theorem pav_winner_is_pareto_optimal (inst : ABCInstance V C) (W : Finset C)
    (h_winner : inst.is_pav_winner W) : inst.is_pareto_optimal W := by
  obtain ⟨h_card, h_max⟩ := h_winner
  refine ⟨h_card, ?_⟩
  intro W' h_card' h_dom
  have h_score_strict : inst.pav_score W < inst.pav_score W' :=
    pareto_dominates_implies_higher_score inst W W' h_dom
  have h_score_le : inst.pav_score W' ≤ inst.pav_score W := h_max W' h_card'
  exact absurd h_score_strict (not_lt_of_ge h_score_le)

end ABCInstance
