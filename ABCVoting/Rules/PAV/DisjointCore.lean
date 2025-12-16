import ABCVoting.Rules.PAV.EJR
import ABCVoting.Axioms.Core

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- PAV SATISFIES DISJOINT CORE
-- ============================================================================

/--
The sum of score gains over T can be rewritten as a sum over voters.
-/
lemma sum_score_gains_eq (inst : ABCInstance V C k) (W T : Finset C)
    (hT_disj : Disjoint W T) :
    ∑ c ∈ T, (inst.pav_score (W ∪ {c}) - inst.pav_score W) =
    ∑ i ∈ inst.voters, ∑ _ ∈ T ∩ inst.approves i, 1 / ((W ∩ inst.approves i).card + 1 : ℚ) := by
  trans (∑ c ∈ T, ∑ i ∈ inst.voters.filter (fun i => c ∈ inst.approves i),
      1 / ((W ∩ inst.approves i).card + 1 : ℚ))
  · apply Finset.sum_congr rfl
    intro c hc_in_T
    have hc : c ∉ W := fun h => absurd hc_in_T ((disjoint_left.mp hT_disj) h)
    exact pav_score_add_candidate inst W c hc
  trans (∑ c ∈ T, ∑ i ∈ inst.voters,
      if c ∈ inst.approves i then 1 / ((W ∩ inst.approves i).card + 1 : ℚ) else 0)
  · congr 1 with _
    rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  congr 1 with i
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr
  · ext c; simp only [mem_filter, mem_inter]
  · intros; rfl

/--
Key lemma: When a coalition S has u_i(T) > u_i(W) for all i ∈ S, the sum of
score gains over T is at least |S|.

The proof uses: For each i ∈ S, we have u_i(W) + 1 ≤ u_i(T), so
∑_{c ∈ T ∩ A_i} 1/(u_i(W)+1) ≥ |T ∩ A_i|/u_i(T) = u_i(T)/u_i(T) = 1.
Summing over S gives ≥ |S|.
-/
lemma sum_score_gains_lower_bound (inst : ABCInstance V C k) (W T : Finset C) (S : Finset V)
    (hT_disj : Disjoint W T)
    (hS_sub : S ⊆ inst.voters)
    (h_strict : ∀ i ∈ S, (W ∩ inst.approves i).card < (T ∩ inst.approves i).card) :
    (S.card : ℚ) ≤ ∑ c ∈ T, (inst.pav_score (W ∪ {c}) - inst.pav_score W) := by
  rw [sum_score_gains_eq inst W T hT_disj]
  calc (S.card : ℚ)
      = ∑ _ ∈ S, (1 : ℚ) := by simp
    _ ≤ ∑ i ∈ S, ∑ c ∈ T ∩ inst.approves i, 1 / ((W ∩ inst.approves i).card + 1 : ℚ) := by
        apply Finset.sum_le_sum
        intro i hi
        have h_util_T_pos : 0 < (T ∩ inst.approves i).card := by
          have := h_strict i hi; omega
        have h_bound : (W ∩ inst.approves i).card + 1 ≤ (T ∩ inst.approves i).card :=
          h_strict i hi
        calc (1 : ℚ)
            = (T ∩ inst.approves i).card / (T ∩ inst.approves i).card := by
              field_simp
            _ ≤ (T ∩ inst.approves i).card / ((W ∩ inst.approves i).card + 1) := by
              apply div_le_div_of_nonneg_left
              · exact Nat.cast_nonneg _
              · positivity
              · exact_mod_cast h_bound
            _ = ∑ _ ∈ T ∩ inst.approves i, 1 / ((W ∩ inst.approves i).card + 1 : ℚ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ ∑ i ∈ inst.voters, ∑ c ∈ T ∩ inst.approves i, 1 / ((W ∩ inst.approves i).card + 1 : ℚ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hS_sub
        intro i _ _
        apply Finset.sum_nonneg
        intro c _
        positivity

/--
From the lower bound on sum, we get a lower bound on average when S is l-large
and |T| ≤ l.
-/
lemma avg_score_gain_lower_bound (inst : ABCInstance V C k) (W T : Finset C) (S : Finset V) (l : ℕ)
    (hT_disj : Disjoint W T)
    (hS_sub : S ⊆ inst.voters)
    (h_large : inst.is_l_large S l)
    (hT_card : T.card ≤ l)
    (hT_nonempty : T.Nonempty)
    (h_strict : ∀ i ∈ S, (W ∩ inst.approves i).card < (T ∩ inst.approves i).card) :
    (inst.voters.card : ℚ) / k ≤
      (∑ c ∈ T, (inst.pav_score (W ∪ {c}) - inst.pav_score W)) / T.card := by
  have hT_card_pos : 0 < T.card := card_pos.mpr hT_nonempty
  have h_sum := sum_score_gains_lower_bound inst W T S hT_disj hS_sub h_strict
  have hl_pos : 0 < l := Nat.lt_of_lt_of_le hT_card_pos hT_card
  have h_large_ineq : (inst.voters.card : ℚ) / k ≤ (S.card : ℚ) / l := by
    have hk_pos : (0 : ℚ) < k := Nat.cast_pos.mpr inst.k_pos
    have hl_pos' : (0 : ℚ) < l := Nat.cast_pos.mpr hl_pos
    unfold is_l_large at h_large
    field_simp
    calc (inst.voters.card : ℚ) * l = l * inst.voters.card := by ring
      _ ≤ S.card * k := by exact_mod_cast h_large
      _ = k * S.card := by ring
  calc (inst.voters.card : ℚ) / k
      ≤ S.card / l := h_large_ineq
    _ ≤ S.card / T.card := by
        apply div_le_div_of_nonneg_left
        · exact Nat.cast_nonneg _
        · exact Nat.cast_pos.mpr hT_card_pos
        · exact Nat.cast_le.mpr hT_card
    _ ≤ (∑ c ∈ T, (inst.pav_score (W ∪ {c}) - inst.pav_score W)) / T.card := by
        apply div_le_div_of_nonneg_right h_sum
        exact Nat.cast_nonneg _

/--
By pigeonhole: if the average score gain is ≥ n/k, then some element achieves ≥ n/k.
-/
lemma exists_high_score_gain (inst : ABCInstance V C k) (W T : Finset C)
    (hT_nonempty : T.Nonempty)
    (hT_disj : Disjoint W T)
    (h_avg : (inst.voters.card : ℚ) / k ≤
        (∑ c ∈ T, (inst.pav_score (W ∪ {c}) - inst.pav_score W)) / T.card) :
    ∃ c ∈ T, c ∉ W ∧ (inst.voters.card : ℚ) / k ≤ inst.pav_score (W ∪ {c}) - inst.pav_score W := by
  have hT_card_pos : 0 < T.card := card_pos.mpr hT_nonempty
  by_contra h_none
  push_neg at h_none
  have h_all_small : ∀ c ∈ T, inst.pav_score (W ∪ {c}) - inst.pav_score W <
      (inst.voters.card : ℚ) / k := by
    intro c hc
    have hc_not_W : c ∉ W := fun h => absurd hc ((disjoint_left.mp hT_disj) h)
    exact h_none c hc hc_not_W
  have h_sum_small : ∑ c ∈ T, (inst.pav_score (W ∪ {c}) - inst.pav_score W) <
      T.card * ((inst.voters.card : ℚ) / k) := by
    calc ∑ c ∈ T, (inst.pav_score (W ∪ {c}) - inst.pav_score W)
        < ∑ _ ∈ T, (inst.voters.card : ℚ) / k :=
          Finset.sum_lt_sum_of_nonempty hT_nonempty h_all_small
      _ = T.card * ((inst.voters.card : ℚ) / k) := by simp [Finset.sum_const, nsmul_eq_mul]
  have h_avg_small : (∑ c ∈ T, (inst.pav_score (W ∪ {c}) - inst.pav_score W)) / T.card <
      (inst.voters.card : ℚ) / k := by
    have hT_pos : (0 : ℚ) < T.card := Nat.cast_pos.mpr hT_card_pos
    calc (∑ c ∈ T, (inst.pav_score (W ∪ {c}) - inst.pav_score W)) / T.card
        < (T.card * ((inst.voters.card : ℚ) / k)) / T.card := by
          exact div_lt_div_of_pos_right h_sum_small hT_pos
      _ = (inst.voters.card : ℚ) / k := by field_simp
  linarith

/--
**Main Theorem: PAV winners are in the disjoint core.**

If W is a PAV winner (maximizes PAV score among committees of size k),
then W satisfies the disjoint core property.

**Proof sketch:**
Suppose S is ℓ-large, |T| ≤ ℓ, T ⊆ C \ W (disjoint from W), and every voter in S
strictly prefers T to W (i.e., u_i(T) > u_i(W)).

1. The average score gain when adding elements of T is:
   (1/|T|) ∑_{c ∈ T} MC+(c,W) ≥ |S|/|T| ≥ |S|/ℓ ≥ n/k

2. So some c ∈ T has MC+(c,W) ≥ n/k. Since T ∩ W = ∅, we can add c to get
   W' = W ∪ {c} with |W'| = k+1.

3. The average removal cost in W' is ≤ n/(k+1) < n/k, so some c' ∈ W' has
   removal cost < n/k.

4. Then W'' = W' \ {c'} has |W''| = k and PAV(W'') > PAV(W), contradicting
   W being a PAV winner.
-/
theorem pav_winner_in_disjoint_core (inst : ABCInstance V C k) (W : Finset C)
    (h_winner : inst.is_pav_winner W) : inst.is_in_disjoint_core W := by
  obtain ⟨hW_sub, h_card, h_max⟩ := h_winner
  intro S T l hS_sub hT_sub hT_disj hl_pos ⟨h_large, hT_card⟩
  -- We prove the contrapositive: if all voters in S strictly prefer T, derive contradiction
  by_contra h_neg
  push_neg at h_neg
  -- h_neg says: ∀ i ∈ S, u_i(W) < u_i(T)

  -- Handle edge case: T is empty
  by_cases hT_empty : T = ∅
  · -- If T is empty, then |T ∩ A_i| = 0 for all i, but we need |T ∩ A_i| > |W ∩ A_i| ≥ 0
    simp only [hT_empty, empty_inter, card_empty, not_lt_zero'] at h_neg
    obtain ⟨i, hi⟩ := l_large_nonempty inst S l hl_pos h_large
    exact h_neg i hi

  have hT_nonempty : T.Nonempty := nonempty_iff_ne_empty.mpr hT_empty

  -- Step 1: Average score gain over T is ≥ n/k
  have h_avg : (inst.voters.card : ℚ) / k ≤
      (∑ c ∈ T, (inst.pav_score (W ∪ {c}) - inst.pav_score W)) / T.card :=
    avg_score_gain_lower_bound inst W T S l hT_disj hS_sub h_large hT_card hT_nonempty h_neg

  -- Step 2: Some c ∈ T has score gain ≥ n/k
  obtain ⟨c, hc_in_T, hc_not_W, h_gain⟩ := exists_high_score_gain inst W T hT_nonempty hT_disj h_avg

  -- Step 3: Add c to get W' with |W'| = k+1
  let W' := W ∪ {c}
  have hW'_card : W'.card = k + 1 := by
    simp only [W', union_singleton, card_insert_of_notMem hc_not_W, h_card]

  -- Step 4: Sum of removal costs over W' is ≤ n
  have h_sum_le : ∑ c' ∈ W', ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
      1 / ((W' ∩ inst.approves i).card : ℚ) ≤ inst.voters.card :=
    sum_removal_costs_le_voters inst W'

  -- Step 5: By pigeonhole, ∃ c' with removal cost < n/k
  have h_exists_small : ∃ c' ∈ W',
      ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
        1 / ((W' ∩ inst.approves i).card : ℚ) < (inst.voters.card : ℚ) / k := by
    by_contra h_all_large
    push_neg at h_all_large
    have h_sum_ge : (k + 1) * ((inst.voters.card : ℚ) / k) ≤
        ∑ c' ∈ W', ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
          1 / ((W' ∩ inst.approves i).card : ℚ) := by
      calc (k + 1) * ((inst.voters.card : ℚ) / k)
          = ∑ _ ∈ W', (inst.voters.card : ℚ) / k := by
            simp only [Finset.sum_const, hW'_card, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        _ ≤ ∑ c' ∈ W', ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
              1 / ((W' ∩ inst.approves i).card : ℚ) :=
            Finset.sum_le_sum (fun c' hc' => h_all_large c' hc')
    have h_arith : (inst.voters.card : ℚ) < (k + 1) * ((inst.voters.card : ℚ) / k) := by
      have hk_pos : (0 : ℚ) < k := Nat.cast_pos.mpr inst.k_pos
      have hn_pos : (0 : ℚ) < inst.voters.card :=
        Nat.cast_pos.mpr (card_pos.mpr inst.voters_nonempty)
      field_simp
      linarith
    linarith

  obtain ⟨c', hc'_in_W', h_small⟩ := h_exists_small

  -- Step 6: W' \ {c'} has size k and higher PAV score than W
  have h_size : (W' \ {c'}).card = k := by
    simp only [card_sdiff, card_singleton, hW'_card, singleton_inter_of_mem hc'_in_W']
    omega

  have h_score_eq : inst.pav_score (W' \ {c'}) =
      inst.pav_score W' - ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
        1 / ((W' ∩ inst.approves i).card : ℚ) := by
    have := pav_score_remove_candidate inst W' c' hc'_in_W'
    linarith

  have h_better : inst.pav_score W < inst.pav_score (W' \ {c'}) := by
    calc inst.pav_score W
        = inst.pav_score W' - (inst.pav_score W' - inst.pav_score W) := by ring
      _ ≤ inst.pav_score W' - (inst.voters.card : ℚ) / k := by
          have : inst.pav_score W' - inst.pav_score W =
              inst.pav_score (W ∪ {c}) - inst.pav_score W := rfl
          linarith
      _ < inst.pav_score W' - ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
            1 / ((W' ∩ inst.approves i).card : ℚ) := by linarith
      _ = inst.pav_score (W' \ {c'}) := by linarith

  -- This contradicts W being a PAV winner
  have h_W'_sub : W' \ {c'} ⊆ inst.candidates := by
    intro x hx
    simp only [W', mem_sdiff, mem_union, mem_singleton] at hx
    obtain ⟨hx_in, _⟩ := hx
    rcases hx_in with hx_W | rfl
    · exact hW_sub hx_W
    · exact hT_sub hc_in_T
  have h_le := h_max (W' \ {c'}) h_W'_sub h_size
  linarith

end ABCInstance
