import ABCVoting.Rules.PAV.Defs
import ABCVoting.Axioms.JRAxioms

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C]

-- ============================================================================
-- PAV SATISFIES EJR+
-- ============================================================================

/--
Score contribution from adding a candidate c to committee W for voter i.

If i approves c: gain is 1/(u_i(W) + 1), otherwise 0
where u_i(W) = |W ∩ approves_i| is voter i's utility for W.
-/
lemma score_gain_voter (inst : ABCInstance V C) (W : Finset C) (c : C) (i : V)
    (hc : c ∉ W) :
    harmonic ((W ∪ {c}) ∩ inst.approves i).card - harmonic (W ∩ inst.approves i).card =
    if c ∈ inst.approves i then 1 / ((W ∩ inst.approves i).card + 1 : ℚ) else 0 := by
  split_ifs with hci
  · have h : (W ∪ {c}) ∩ inst.approves i = insert c (W ∩ inst.approves i) := by
      ext x
      simp only [mem_inter, mem_union, mem_singleton, mem_insert]
      constructor
      · rintro ⟨hxW | rfl, hxa⟩
        · right; exact ⟨hxW, hxa⟩
        · left; rfl
      · rintro (rfl | ⟨hxW, hxa⟩)
        · exact ⟨Or.inr rfl, hci⟩
        · exact ⟨Or.inl hxW, hxa⟩
    have hc' : c ∉ W ∩ inst.approves i := fun h => hc (mem_inter.mp h).1
    rw [h, card_insert_of_notMem hc', harmonic_succ_sub]
  · have h : (W ∪ {c}) ∩ inst.approves i = W ∩ inst.approves i := by
      ext x
      simp only [mem_inter, mem_union, mem_singleton]
      constructor
      · rintro ⟨hxW | rfl, hxa⟩
        · exact ⟨hxW, hxa⟩
        · exact absurd hxa hci
      · rintro ⟨hxW, hxa⟩
        exact ⟨Or.inl hxW, hxa⟩
    rw [h, sub_self]

/--
PAV score change when adding a candidate c to committee W.
-/
lemma pav_score_add_candidate (inst : ABCInstance V C) (W : Finset C) (c : C)
    (hc : c ∉ W) :
    inst.pav_score (W ∪ {c}) - inst.pav_score W =
    ∑ i ∈ inst.voters.filter (fun i => c ∈ inst.approves i),
      1 / ((W ∩ inst.approves i).card + 1 : ℚ) := by
  unfold pav_score
  rw [← Finset.sum_sub_distrib]
  trans (∑ i ∈ inst.voters, if c ∈ inst.approves i
      then 1 / ((W ∩ inst.approves i).card + 1 : ℚ) else 0)
  · congr 1 with i
    exact score_gain_voter inst W c i hc
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]

/--
Score contribution from removing a candidate c from committee W for voter i.

If i approves c: loss is 1/u_i(W), otherwise 0.
-/
lemma score_loss_voter (inst : ABCInstance V C) (W : Finset C) (c : C) (i : V)
    (hc : c ∈ W) :
    harmonic (W ∩ inst.approves i).card - harmonic ((W \ {c}) ∩ inst.approves i).card =
    if c ∈ inst.approves i then 1 / ((W ∩ inst.approves i).card : ℚ) else 0 := by
  split_ifs with hci
  · have h : W ∩ inst.approves i = insert c ((W \ {c}) ∩ inst.approves i) := by
      ext x
      simp only [mem_inter, mem_insert, mem_sdiff, mem_singleton]
      constructor
      · rintro ⟨hxW, hxa⟩
        by_cases hxc : x = c
        · left; exact hxc
        · right; exact ⟨⟨hxW, hxc⟩, hxa⟩
      · rintro (rfl | ⟨⟨hxW, _⟩, hxa⟩)
        · exact ⟨hc, hci⟩
        · exact ⟨hxW, hxa⟩
    have hc' : c ∉ (W \ {c}) ∩ inst.approves i := fun hx =>
      (mem_sdiff.mp (mem_inter.mp hx).1).2 (mem_singleton.mpr rfl)
    rw [h, card_insert_of_notMem hc', harmonic_succ_sub]; simp
  · have h : (W \ {c}) ∩ inst.approves i = W ∩ inst.approves i := by
      ext x
      simp only [mem_inter, mem_sdiff, mem_singleton]
      constructor
      · rintro ⟨⟨hxW, _⟩, hxa⟩
        exact ⟨hxW, hxa⟩
      · rintro ⟨hxW, hxa⟩
        refine ⟨⟨hxW, ?_⟩, hxa⟩
        rintro rfl
        exact hci hxa
    rw [h, sub_self]

/--
PAV score change when removing a candidate c from committee W.
-/
lemma pav_score_remove_candidate (inst : ABCInstance V C) (W : Finset C) (c : C)
    (hc : c ∈ W) :
    inst.pav_score W - inst.pav_score (W \ {c}) =
    ∑ i ∈ inst.voters.filter (fun i => c ∈ inst.approves i),
      1 / ((W ∩ inst.approves i).card : ℚ) := by
  unfold pav_score
  rw [← Finset.sum_sub_distrib]
  trans (∑ i ∈ inst.voters, if c ∈ inst.approves i
      then 1 / ((W ∩ inst.approves i).card : ℚ) else 0)
  · congr 1 with i
    exact score_loss_voter inst W c i hc
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]

/--
Sum of removal costs over all candidates equals the number of voters with positive utility.

∑_{c ∈ W} ∑_{i : c ∈ A_i} 1/u_i(W) = ∑_{i ∈ N} ∑_{c ∈ A_i ∩ W} 1/u_i(W) = #{i ∈ N : u_i(W) > 0}
-/
lemma sum_removal_costs (inst : ABCInstance V C) (W : Finset C) :
    ∑ c ∈ W, ∑ i ∈ inst.voters.filter (fun i => c ∈ inst.approves i),
      1 / ((W ∩ inst.approves i).card : ℚ) =
    (inst.voters.filter (fun i => (W ∩ inst.approves i).Nonempty)).card := by
  trans (∑ c ∈ W, ∑ i ∈ inst.voters,
      if c ∈ inst.approves i then 1 / ((W ∩ inst.approves i).card : ℚ) else 0)
  · congr 1 with c
    rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  trans (∑ i ∈ inst.voters, ∑ c ∈ W ∩ inst.approves i, 1 / ((W ∩ inst.approves i).card : ℚ))
  · congr 1 with i
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext c; simp only [mem_filter, mem_inter]
    · intros; rfl
  trans (∑ i ∈ inst.voters, if (W ∩ inst.approves i).Nonempty then (1 : ℚ) else 0)
  · congr 1 with i
    by_cases hne : (W ∩ inst.approves i).Nonempty
    · simp only [hne, ↓reduceIte]
      have hcard_pos : 0 < (W ∩ inst.approves i).card := card_pos.mpr hne
      have hcard_ne : ((W ∩ inst.approves i).card : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hcard_pos)
      rw [Finset.sum_const, nsmul_eq_mul, mul_one_div, div_self hcard_ne]
    · simp [not_nonempty_iff_eq_empty.mp hne]
  rw [← Finset.sum_boole]

/--
Corollary: The sum of removal costs is at most the number of voters.
-/
lemma sum_removal_costs_le_voters (inst : ABCInstance V C) (W : Finset C) :
    ∑ c ∈ W, ∑ i ∈ inst.voters.filter (fun i => c ∈ inst.approves i),
      1 / ((W ∩ inst.approves i).card : ℚ) ≤ inst.voters.card := by
  rw [sum_removal_costs]
  exact_mod_cast Finset.card_filter_le inst.voters _

/--
Lower bound on the PAV score gain from adding a candidate when an ℓ-large group
all approves it and all have utility < ℓ so far.

This is a key technical lemma for the EJR+ proof.
-/
lemma score_gain_lower_bound (inst : ABCInstance V C) (W : Finset C) (c : C) (S : Finset V)
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
theorem pav_winner_satisfies_ejr_plus (inst : ABCInstance V C) (W : Finset C)
    (h_winner : inst.is_pav_winner W) : inst.is_ejr_plus W := by
  obtain ⟨h_card, h_max⟩ := h_winner
  intro S l hS_sub hl ⟨h_large, c, hc_cand, hS_approves⟩
  by_contra h_neg
  push_neg at h_neg
  let W' := W ∪ {c}
  have hc_not_in_W : c ∉ W := (mem_sdiff.mp hc_cand).2

  -- Step 1: Score gain from adding c is ≥ |S|/l ≥ n/k
  have h_gain : (S.card : ℚ) / l ≤ inst.pav_score W' - inst.pav_score W :=
    score_gain_lower_bound inst W c S l hl hc_not_in_W hS_sub hS_approves h_neg

  have h_large_ineq : (inst.voters.card : ℚ) / inst.k ≤ (S.card : ℚ) / l := by
    unfold is_l_large at h_large
    have hk_pos : (0 : ℚ) < inst.k := Nat.cast_pos.mpr inst.k_pos
    have hl_pos : (0 : ℚ) < l := Nat.cast_pos.mpr hl
    field_simp
    calc (inst.voters.card : ℚ) * l = l * inst.voters.card := by ring
      _ ≤ S.card * inst.k := by exact_mod_cast h_large
      _ = inst.k * S.card := by ring

  have h_gain' : (inst.voters.card : ℚ) / inst.k ≤ inst.pav_score W' - inst.pav_score W :=
    le_trans h_large_ineq h_gain

  -- Step 2: Sum of removal costs over W' is ≤ n
  have h_W'_card : W'.card = inst.k + 1 := by
    simp only [W', union_singleton, card_insert_of_notMem hc_not_in_W, h_card]

  have h_sum_le : ∑ c' ∈ W', ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
      1 / ((W' ∩ inst.approves i).card : ℚ) ≤ inst.voters.card :=
    sum_removal_costs_le_voters inst W'

  -- Step 3: By pigeonhole, ∃ c† with removal cost < n/(k+1) < n/k
  have h_exists_small : ∃ c' ∈ W',
      ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
        1 / ((W' ∩ inst.approves i).card : ℚ) < (inst.voters.card : ℚ) / inst.k := by
    by_contra h_all_large
    push_neg at h_all_large
    have h_sum_ge : (inst.k + 1) * ((inst.voters.card : ℚ) / inst.k) ≤
        ∑ c' ∈ W', ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
          1 / ((W' ∩ inst.approves i).card : ℚ) := by
      calc (inst.k + 1) * ((inst.voters.card : ℚ) / inst.k)
          = ∑ _ ∈ W', (inst.voters.card : ℚ) / inst.k := by
            simp only [Finset.sum_const, h_W'_card, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        _ ≤ ∑ c' ∈ W', ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
              1 / ((W' ∩ inst.approves i).card : ℚ) :=
            Finset.sum_le_sum (fun c' hc' => h_all_large c' hc')
    have h_arith : (inst.voters.card : ℚ) < (inst.k + 1) * ((inst.voters.card : ℚ) / inst.k) := by
      have hk_pos : (0 : ℚ) < inst.k := Nat.cast_pos.mpr inst.k_pos
      have hn_pos : (0 : ℚ) < inst.voters.card :=
        Nat.cast_pos.mpr (card_pos.mpr inst.voters_nonempty)
      field_simp
      linarith
    linarith

  obtain ⟨c', hc'_in_W', h_small⟩ := h_exists_small

  -- Step 4: W' \ {c'} has size k and higher PAV score than W
  have hc'_in : c' ∈ W' := hc'_in_W'
  have h_size : (W' \ {c'}).card = inst.k := by
    simp only [card_sdiff, card_singleton, h_W'_card, singleton_inter_of_mem hc'_in]
    omega

  have h_score_eq : inst.pav_score (W' \ {c'}) =
      inst.pav_score W' - ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
        1 / ((W' ∩ inst.approves i).card : ℚ) := by
    have := pav_score_remove_candidate inst W' c' hc'_in
    linarith

  have h_better : inst.pav_score W < inst.pav_score (W' \ {c'}) := by
    calc inst.pav_score W
        = inst.pav_score W' - (inst.pav_score W' - inst.pav_score W) := by ring
      _ ≤ inst.pav_score W' - (inst.voters.card : ℚ) / inst.k := by linarith
      _ < inst.pav_score W' - ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
            1 / ((W' ∩ inst.approves i).card : ℚ) := by linarith
      _ = inst.pav_score (W' \ {c'}) := by linarith

  -- This contradicts W being a PAV winner
  have h_le := h_max (W' \ {c'}) h_size
  linarith

end ABCInstance
