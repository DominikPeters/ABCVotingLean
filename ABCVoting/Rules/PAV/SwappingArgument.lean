import ABCVoting.Rules.PAV.Defs

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

/--
Score contribution from adding a candidate `c` to committee `W` for voter `i`.

If `i` approves `c`: gain is `1/(u_i(W) + 1)`, otherwise `0`
where `u_i(W) = |W ∩ approves_i|` is voter `i`'s utility for `W`.
-/
lemma score_gain_voter (inst : ABCInstance V C k) (W : Finset C) (c : C) (i : V)
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
PAV score change when adding a candidate `c` to committee `W`.
-/
lemma pav_score_add_candidate (inst : ABCInstance V C k) (W : Finset C) (c : C)
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
PAV score change when removing a candidate `c` from committee `W` for voter `i`.

If `i` approves `c`: loss is `1/u_i(W)`, otherwise `0`.
-/
lemma score_loss_voter (inst : ABCInstance V C k) (W : Finset C) (c : C) (i : V)
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

/-- Removal cost of candidate `c` from committee `W`. -/
def pav_removal_cost (inst : ABCInstance V C k) (W : Finset C) (c : C) : ℚ :=
  ∑ i ∈ inst.voters.filter (fun i => c ∈ inst.approves i),
    1 / ((W ∩ inst.approves i).card : ℚ)

/--
PAV score change when removing a candidate `c` from committee `W`.
-/
lemma pav_score_remove_candidate (inst : ABCInstance V C k) (W : Finset C) (c : C)
    (hc : c ∈ W) :
    inst.pav_score W - inst.pav_score (W \ {c}) = inst.pav_removal_cost W c := by
  unfold pav_removal_cost
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
lemma sum_removal_costs (inst : ABCInstance V C k) (W : Finset C) :
    ∑ c ∈ W, inst.pav_removal_cost W c =
    (inst.voters.filter (fun i => (W ∩ inst.approves i).Nonempty)).card := by
  unfold pav_removal_cost
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
lemma sum_removal_costs_le_voters (inst : ABCInstance V C k) (W : Finset C) :
    ∑ c ∈ W, inst.pav_removal_cost W c ≤ inst.voters.card := by
  rw [sum_removal_costs]
  exact_mod_cast Finset.card_filter_le inst.voters _

/--
Pigeonhole step: in a committee of size `k+1`, some candidate has removal cost `< n/k`.
-/
lemma exists_small_removal_cost (inst : ABCInstance V C k) (W : Finset C)
    (h_card : W.card = k + 1) :
    ∑ c ∈ W, inst.pav_removal_cost W c ≤ inst.voters.card →
    ∃ c ∈ W, inst.pav_removal_cost W c < (inst.voters.card : ℚ) / k := by
  intro h_sum_le
  by_contra h_all_large
  push_neg at h_all_large
  have h_sum_ge : (k + 1) * ((inst.voters.card : ℚ) / k) ≤
      ∑ c ∈ W, inst.pav_removal_cost W c := by
    calc (k + 1) * ((inst.voters.card : ℚ) / k)
        = ∑ _ ∈ W, (inst.voters.card : ℚ) / k := by
            simp [Finset.sum_const, h_card, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      _ ≤ ∑ c ∈ W, inst.pav_removal_cost W c :=
          Finset.sum_le_sum (fun c hc => h_all_large c hc)
  have h_arith : (inst.voters.card : ℚ) <
      (k + 1) * ((inst.voters.card : ℚ) / k) := by
    have hk_pos : (0 : ℚ) < k := Nat.cast_pos.mpr inst.k_pos
    have hn_pos : (0 : ℚ) < inst.voters.card :=
      Nat.cast_pos.mpr (card_pos.mpr inst.voters_nonempty)
    field_simp
    linarith
  linarith

/--
If adding `c` increases the score by at least `n/k`, we can remove some candidate
and obtain a better size-`k` committee.
-/
lemma improving_committee_from_gain (inst : ABCInstance V C k) (W : Finset C) (c : C)
    (hW_sub : W ⊆ inst.candidates) (hW_card : W.card = k)
    (hc_cand : c ∈ inst.candidates) (hc_not : c ∉ W)
    (h_gain : (inst.voters.card : ℚ) / k ≤ inst.pav_score (W ∪ {c}) - inst.pav_score W) :
    ∃ W', W' ⊆ inst.candidates ∧ W'.card = k ∧ inst.pav_score W < inst.pav_score W' := by
  classical
  let W' := W ∪ {c}
  have hW'_card : W'.card = k + 1 := by
    simp [W', union_singleton, hW_card, hc_not]
  have h_sum_le : ∑ c' ∈ W', inst.pav_removal_cost W' c' ≤ inst.voters.card :=
    sum_removal_costs_le_voters inst W'
  obtain ⟨c', hc'_in, h_small⟩ :=
    exists_small_removal_cost inst W' hW'_card h_sum_le
  have h_score_remove := pav_score_remove_candidate inst W' c' hc'_in
  have h_score_eq : inst.pav_score W' - inst.pav_removal_cost W' c' =
      inst.pav_score (W' \ {c'}) := by
    have h_score_remove := pav_score_remove_candidate inst W' c' hc'_in
    linarith

  have h_better : inst.pav_score W < inst.pav_score (W' \ {c'}) := by
    calc inst.pav_score W
        = inst.pav_score W' - (inst.pav_score W' - inst.pav_score W) := by ring
      _ ≤ inst.pav_score W' - (inst.voters.card : ℚ) / k := by linarith
      _ < inst.pav_score W' - inst.pav_removal_cost W' c' := by linarith
      _ = inst.pav_score (W' \ {c'}) := h_score_eq

  have h_subset : W' \ {c'} ⊆ inst.candidates := by
    intro x hx
    rcases mem_sdiff.mp hx with ⟨hx_in, _⟩
    rcases mem_union.mp hx_in with hxW | hx_singleton
    · exact hW_sub hxW
    · rcases mem_singleton.mp hx_singleton with rfl
      exact hc_cand

  have h_size : (W' \ {c'}).card = k := by
    classical
    have h_card : (W' \ {c'}).card = W'.card - 1 := by
      classical
      have h := card_erase_of_mem (s := W') (a := c') hc'_in
      -- rewrite `sdiff` as `erase`
      simpa [sdiff_singleton_eq_erase] using h
    calc
      (W' \ {c'}).card = W'.card - 1 := h_card
      _ = (k + 1) - 1 := by simpa [hW'_card]
      _ = k := by omega

  exact ⟨W' \ {c'}, h_subset, h_size, h_better⟩

end ABCInstance
