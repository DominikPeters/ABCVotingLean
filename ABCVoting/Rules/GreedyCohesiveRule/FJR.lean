import ABCVoting.Rules.GreedyCohesiveRule.Defs
import ABCVoting.Axioms.JRAxioms

/-!
# GCR Satisfies FJR

This file proves that any committee produced by the Greedy Cohesive Rule
satisfies Full Justified Representation (FJR).

## Main Result

* `gcr_satisfies_fjr`: If W is produced by a GCRWitness, then W satisfies FJR.

## Proof Strategy

The proof is by contradiction, following the argument from:
Peters, Pierczyński, Skowron: "Proportional Participatory Budgeting with Additive Utilities"

**Proof sketch:**
1. Assume W = w.final_committee fails FJR
2. There exists a violation witness: (S, T, l, β) such that
   - S is l-large, |T| ≤ l, every voter in S approves ≥ β candidates from T
   - But every voter in S has utility < β from W
3. Since S ⊆ voters and voters who aren't deactivated are in final_active,
   and termination says no witness exists in final_active,
   some voter in S must have been deactivated.
4. Let i ∈ S be the first voter in S to be deactivated (at step t)
5. At step t, all of S was still active, so (S, T, β) was a valid witness at step t
7. By β-maximality, the algorithm chose some β' ≥ β at step t
8. Since i ∈ S_t: u_i(T_t) ≥ β' ≥ β
9. Since T_t ⊆ W: u_i(W) ≥ u_i(T_t) ≥ β
10. Contradiction with u_i(W) < β
-/

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- KEY LEMMA: UTILITY MONOTONICITY
-- ============================================================================

/--
If T ⊆ W, then utility from W is at least utility from T.
-/
lemma utility_mono_subset (inst : ABCInstance V C k) (T W : Finset C) (i : V)
    (hTW : T ⊆ W) : (T ∩ inst.approves i).card ≤ (W ∩ inst.approves i).card := by
  exact card_le_card (inter_subset_inter_right hTW)

/--
If a voter is not deactivated before step n, they are active at step n.
-/
lemma mem_active_at_of_not_deactivated_before {inst : ABCInstance V C k}
    (w : GCRWitness V C inst) (i : V) (hi : i ∈ inst.voters) :
    ∀ n (hn : n < w.num_steps),
      (∀ s : Fin w.num_steps, s.val < n → i ∉ (w.steps s).S) →
      i ∈ w.active_at ⟨n, hn⟩ := by
  classical
  refine Nat.rec ?base ?step
  · intro h0 _
    have hactive : (w.steps ⟨0, h0⟩).active_before = inst.voters := w.initial_active h0
    simpa [GCRWitness.active_at, hactive] using hi
  · intro n ih hn1 h_not
    have hn : n < w.num_steps := Nat.lt_trans (Nat.lt_succ_self n) hn1
    have h_not_prev : ∀ s : Fin w.num_steps, s.val < n → i ∉ (w.steps s).S := by
      intro s hs
      exact h_not s (Nat.lt_trans hs (Nat.lt_succ_self n))
    have hi_before : i ∈ w.active_at ⟨n, hn⟩ := ih hn h_not_prev
    have hi_not_Sn : i ∉ (w.steps ⟨n, hn⟩).S := h_not ⟨n, hn⟩ (Nat.lt_succ_self n)
    have hlink :
        (w.steps ⟨n + 1, hn1⟩).active_before = (w.steps ⟨n, hn⟩).active_after :=
      w.active_linked ⟨n, hn⟩ hn1
    have hi_after : i ∈ (w.steps ⟨n, hn⟩).active_after := by
      have hi_before' : i ∈ (w.steps ⟨n, hn⟩).active_before := by
        simpa [GCRWitness.active_at] using hi_before
      exact Finset.mem_sdiff.mpr ⟨hi_before', hi_not_Sn⟩
    simpa [GCRWitness.active_at, hlink] using hi_after

-- ============================================================================
-- THE MAIN THEOREM
-- ============================================================================

/--
Any committee produced by a GCRWitness satisfies FJR.

This is the main correctness theorem for the Greedy Cohesive Rule.
-/
theorem gcr_satisfies_fjr {inst : ABCInstance V C k} (w : GCRWitness V C inst) :
    inst.is_fjr w.final_committee := by
  classical
  -- Proof by contradiction
  intro S T l β hS_voters hT_cand hl_pos hβ_pos ⟨h_large, h_T_small, h_approves⟩
  -- We need to show: ∃ i ∈ S, (w.final_committee ∩ inst.approves i).card ≥ β

  -- Suppose for contradiction that no voter in S has utility ≥ β
  by_contra h_no_rep
  push_neg at h_no_rep
  -- h_no_rep : ∀ i ∈ S, (w.final_committee ∩ inst.approves i).card < β

  -- S is nonempty (since it's l-large with l ≥ 1)
  have hS_nonempty : S.Nonempty := l_large_nonempty inst S l hl_pos h_large
  have hT_nonempty : T.Nonempty := by
    obtain ⟨i, hi⟩ := hS_nonempty
    have h_card : (inst.approves i ∩ T).card ≥ β := h_approves i hi
    have h_one : 1 ≤ (inst.approves i ∩ T).card := le_trans hβ_pos h_card
    have hpos : 0 < (inst.approves i ∩ T).card :=
      lt_of_lt_of_le (Nat.zero_lt_succ _) h_one
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
    exact ⟨c, (Finset.mem_inter.mp hc).2⟩
  have hS_large' : inst.is_l_large S T.card := by
    unfold is_l_large at h_large ⊢
    calc T.card * inst.voters.card
        ≤ l * inst.voters.card := Nat.mul_le_mul_right _ h_T_small
      _ ≤ S.card * k := h_large

  -- Case 1: All of S is in final_active
  -- Then we can construct a valid witness, contradicting termination
  by_cases h_all_active : S ⊆ w.final_active
  · -- All of S is still active
    -- Construct the witness
    have witness : WeaklyCohesiveWitness V C inst w.final_committee w.final_active := {
      S := S
      T := T
      β := β
      S_active := h_all_active
      T_candidates := hT_cand
      T_nonempty := hT_nonempty
      S_nonempty := hS_nonempty
      β_pos := hβ_pos
      S_large := hS_large'
      S_approves := h_approves
    }
    -- This contradicts termination
    exact w.termination witness

  · -- Case 2: Not all of S is in final_active
    -- Some voter in S was deactivated
    obtain ⟨i₀, hi₀_S, hi₀_not_active⟩ := Finset.not_subset.mp h_all_active
    have hi₀_voters : i₀ ∈ inst.voters := hS_voters hi₀_S

    have hnum_pos : w.num_steps > 0 := by
      by_contra hnum
      have hnum' : w.num_steps = 0 := Nat.eq_zero_of_not_pos hnum
      have hfinal : w.final_active = inst.voters := by
        simpa [hnum'] using (w.final_active_correct)
      have h_all_active' : S ⊆ w.final_active := by
        intro i hi
        have hi_voters : i ∈ inst.voters := hS_voters hi
        simpa [hfinal] using hi_voters
      exact h_all_active h_all_active'

    let t_last : Fin w.num_steps := ⟨w.num_steps - 1, Nat.sub_lt hnum_pos Nat.one_pos⟩
    have hfinal_active : w.final_active = (w.steps t_last).active_after := by
      simpa [hnum_pos] using (w.final_active_correct)
    have hi₀_not_after : i₀ ∉ (w.steps t_last).active_after := by
      simpa [hfinal_active] using hi₀_not_active

    have h_step_i₀ : ∃ t : Fin w.num_steps, i₀ ∈ (w.steps t).S := by
      by_cases hi₀_in_last : i₀ ∈ (w.steps t_last).S
      · exact ⟨t_last, hi₀_in_last⟩
      · have hi₀_not_before : i₀ ∉ (w.steps t_last).active_before := by
          intro hi₀_before
          have hi₀_after : i₀ ∈ (w.steps t_last).active_after :=
            Finset.mem_sdiff.mpr ⟨hi₀_before, hi₀_in_last⟩
          exact hi₀_not_after hi₀_after
        have h_exists : ∃ s : Fin w.num_steps, s.val < t_last.val ∧ i₀ ∈ (w.steps s).S := by
          by_contra h_no
          have h_not :
              ∀ s : Fin w.num_steps, s.val < t_last.val → i₀ ∉ (w.steps s).S := by
            intro s hs
            by_contra hs_mem
            exact h_no ⟨s, hs, hs_mem⟩
          have hi₀_before :
              i₀ ∈ w.active_at t_last :=
            mem_active_at_of_not_deactivated_before w i₀ hi₀_voters
              t_last.val t_last.isLt h_not
          have hi₀_before' : i₀ ∈ (w.steps t_last).active_before := by
            simpa [GCRWitness.active_at] using hi₀_before
          exact hi₀_not_before hi₀_before'
        rcases h_exists with ⟨s, _, hs_mem⟩
        exact ⟨s, hs_mem⟩

    let bad_steps : Finset (Fin w.num_steps) :=
      Finset.univ.filter fun t => (S ∩ (w.steps t).S).Nonempty
    have h_bad_nonempty : bad_steps.Nonempty := by
      obtain ⟨t, ht⟩ := h_step_i₀
      refine ⟨t, ?_⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ t, ?_⟩
      exact ⟨i₀, Finset.mem_inter.mpr ⟨hi₀_S, ht⟩⟩

    let t := bad_steps.min' h_bad_nonempty
    have ht_mem : t ∈ bad_steps := Finset.min'_mem bad_steps h_bad_nonempty
    have ht_nonempty : (S ∩ (w.steps t).S).Nonempty := (Finset.mem_filter.mp ht_mem).2
    obtain ⟨i, hi_mem⟩ := ht_nonempty
    have hi_S : i ∈ S := (Finset.mem_inter.mp hi_mem).1
    have hi_step : i ∈ (w.steps t).S := (Finset.mem_inter.mp hi_mem).2

    have hS_active_t : S ⊆ w.active_at t := by
      intro j hjS
      have hj_voters : j ∈ inst.voters := hS_voters hjS
      have h_not_before :
          ∀ s : Fin w.num_steps, s.val < t.val → j ∉ (w.steps s).S := by
        intro s hs
        by_contra hs_mem
        have hs_bad : s ∈ bad_steps := by
          refine Finset.mem_filter.mpr ?_
          refine ⟨Finset.mem_univ s, ?_⟩
          exact ⟨j, Finset.mem_inter.mpr ⟨hjS, hs_mem⟩⟩
        have hleast : IsLeast (↑bad_steps) t := by
          simpa [t] using (Finset.isLeast_min' (s := bad_steps) (H := h_bad_nonempty))
        have h_lb : ∀ b ∈ (↑bad_steps), t ≤ b := by
          simpa [lowerBounds] using hleast.2
        have ht_le : t ≤ s := h_lb s (by simpa using hs_bad)
        have hs_lt : s < t := (Fin.lt_def).2 hs
        exact (not_lt_of_ge ht_le) hs_lt
      exact mem_active_at_of_not_deactivated_before w j hj_voters t.val t.isLt h_not_before

    have hbeta_le : β ≤ (w.steps t).β := by
      exact (w.steps t).β_maximal {
        S := S
        T := T
        β := β
        S_active := hS_active_t
        T_candidates := hT_cand
        T_nonempty := hT_nonempty
        S_nonempty := hS_nonempty
        β_pos := hβ_pos
        S_large := hS_large'
        S_approves := h_approves
      }

    have h_i_utility_Tt :
        (inst.approves i ∩ (w.steps t).T).card ≥ (w.steps t).β :=
      (w.steps t).S_approves i hi_step
    have h_Tt_subset : (w.steps t).T ⊆ w.final_committee := w.step_T_subset_final t
    have h_final_ge_step :
        (w.steps t).β ≤ (w.final_committee ∩ inst.approves i).card := by
      have h_i_utility_Tt' :
          ((w.steps t).T ∩ inst.approves i).card ≥ (w.steps t).β := by
        simpa [inter_comm] using h_i_utility_Tt
      have h_mono :
          ((w.steps t).T ∩ inst.approves i).card ≤
            (w.final_committee ∩ inst.approves i).card :=
        utility_mono_subset inst (w.steps t).T w.final_committee i h_Tt_subset
      exact le_trans h_i_utility_Tt' h_mono

    have h_final_ge_beta : β ≤ (w.final_committee ∩ inst.approves i).card :=
      le_trans hbeta_le h_final_ge_step
    exact (not_lt_of_ge h_final_ge_beta) (h_no_rep i hi_S)

/--
Any GCR outcome satisfies FJR.
-/
theorem gcr_outcome_satisfies_fjr (inst : ABCInstance V C k) (W : Finset C)
    (hW : is_gcr_outcome inst W) : inst.is_fjr W := by
  obtain ⟨w, hw⟩ := hW
  rw [← hw]
  exact gcr_satisfies_fjr w

end ABCInstance
