import ABCVoting.Rules.PAV.SwappingArgument
import ABCVoting.Axioms.JRAxioms

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- PAV SATISFIES EJR+
-- ============================================================================

/--
Lower bound on the PAV score gain from adding a candidate when an ℓ-large group
all approves it and all have utility < ℓ so far.

This is a key technical lemma for the EJR+ proof.
-/
lemma score_gain_lower_bound (inst : ABCInstance V C k) (W : Finset C) (c : C) (S : Finset V)
    (l : ℕ) (hl : 1 ≤ l)
    (hc : c ∉ W)
    (hS_sub : S ⊆ inst.voters)
    (hS_approves : ∀ i ∈ S, c ∈ inst.approves i)
    (h_util_bound : ∀ i ∈ S, (W ∩ inst.approves i).card < l) :
    (S.card : ℚ) / l ≤ inst.pav_score (W ∪ {c}) - inst.pav_score W := by
  rw [pav_score_add_candidate inst W c hc]
  calc (S.card : ℚ) / l
      = ∑ _ ∈ S, (1 : ℚ) / l := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ ∑ i ∈ S, 1 / ((W ∩ inst.approves i).card + 1 : ℚ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hbound := h_util_bound i hi
        have h1 : (W ∩ inst.approves i).card + 1 ≤ l := hbound
        have h2 : (1 : ℚ) ≤ l := by exact_mod_cast hl
        have h3 : (0 : ℚ) < (W ∩ inst.approves i).card + 1 := by norm_cast; omega
        have h4 : (0 : ℚ) < l := by linarith
        exact one_div_le_one_div_of_le h3 (by exact_mod_cast h1)
    _ ≤ ∑ i ∈ inst.voters.filter (fun i => c ∈ inst.approves i),
          1 / ((W ∩ inst.approves i).card + 1 : ℚ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [mem_filter]
          exact ⟨hS_sub hi, hS_approves i hi⟩
        · intro i _ _; positivity

/--
**Main Theorem: PAV winners satisfy EJR+.**

If W is a PAV winner (maximizes PAV score among committees of size k),
then W satisfies Extended Justified Representation Plus (EJR+).

**Proof sketch (from the paper):**
Suppose S is ℓ-large, all voters in S approve candidate c ∉ W, and W is a PAV winner.
Assume for contradiction that every voter in S has utility < ℓ in W.

1. Add c to W to get W̃ = W ∪ {c}. The score gain is ≥ |S|/ℓ ≥ n/k.

2. W̃ has size k+1, so we can identify the candidate c' with smallest removal cost < n/k.

3. Removing c' from W̃ gives W' = W̃ \ {c'} with size k and pav_score(W') > pav_score(W).

4. This contradicts W being a PAV winner (which requires pav_score(W') ≤ pav_score(W)).
-/
theorem pav_winner_satisfies_ejr_plus (inst : ABCInstance V C k) (W : Finset C)
    (h_winner : inst.is_pav_winner W) : inst.is_ejr_plus W := by
  obtain ⟨hW_sub, h_card, h_max⟩ := h_winner
  intro S l hS_sub hl ⟨h_large, c, hc_cand, hS_approves⟩
  by_contra h_neg
  push_neg at h_neg
  let W' := W ∪ {c}
  have hc_not_in_W : c ∉ W := (mem_sdiff.mp hc_cand).2

  -- Step 1: Score gain from adding c is ≥ |S|/l ≥ n/k
  have h_gain : (S.card : ℚ) / l ≤ inst.pav_score W' - inst.pav_score W :=
    score_gain_lower_bound inst W c S l hl hc_not_in_W hS_sub hS_approves h_neg

  have h_large_ineq : (inst.voters.card : ℚ) / k ≤ (S.card : ℚ) / l := by
    unfold is_l_large at h_large
    have hk_pos : (0 : ℚ) < k := Nat.cast_pos.mpr inst.k_pos
    have hl_pos : (0 : ℚ) < l := Nat.cast_pos.mpr hl
    field_simp
    calc (inst.voters.card : ℚ) * l = l * inst.voters.card := by ring
      _ ≤ S.card * k := by exact_mod_cast h_large
      _ = k * S.card := by ring

  have h_gain' : (inst.voters.card : ℚ) / k ≤ inst.pav_score W' - inst.pav_score W :=
    le_trans h_large_ineq h_gain

  -- Steps 2–4: Use the abstract swapping lemma to get a better size-`k` committee.
  obtain ⟨W'', hW''_sub, hW''_card, h_better⟩ :=
    improving_committee_from_gain inst W c hW_sub h_card (by exact (mem_sdiff.mp hc_cand).1)
      hc_not_in_W h_gain'

  -- Contradiction with optimality of the PAV winner.
  have h_le := h_max W'' hW''_sub hW''_card
  linarith

end ABCInstance
