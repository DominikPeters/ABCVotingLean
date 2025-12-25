/-
# Sequential Phragmén: Committee Monotonicity

This file proves that Sequential Phragmén satisfies committee monotonicity:
- Downward: Any (k+1)-outcome has a k-subset that is a k-outcome
- Upward: Any k-outcome can be extended to a (k+1)-outcome (under suitable conditions)

## References
- Elkind, Faliszewski, Skowron, Slinko. "Properties of Multiwinner Voting Rules"
-/

import ABCVoting.Rules.SeqPhragmen.Defs
import ABCVoting.Rules.SeqPhragmen.Priceability
import ABCVoting.Axioms.CommitteeMonotonicity
import ABCVoting.Axioms.Efficiency

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k k' : ℕ}

-- ============================================================================
-- TRANSFERRING ROUNDS BETWEEN COMPATIBLE INSTANCES
-- ============================================================================

/--
The supporters of a candidate are the same for compatible instances.
-/
lemma supporters_eq_of_compatible {inst : ABCInstance V C k} {inst' : ABCInstance V C k'}
    (hcompat : inst.Compatible inst') (c : C) :
    inst.supporters c = inst'.supporters c := by
  ext v
  simp only [supporters, Finset.mem_filter]
  rw [hcompat.voters_eq, hcompat.approves_eq v]

/--
The s_value_num is the same for compatible instances.
-/
lemma s_value_num_eq_of_compatible {inst : ABCInstance V C k} {inst' : ABCInstance V C k'}
    (hcompat : inst.Compatible inst') (loads : V → ℚ) (c : C) :
    inst.s_value_num loads c = inst'.s_value_num loads c := by
  unfold s_value_num
  rw [supporters_eq_of_compatible hcompat]

/--
Transfer a SeqPhragmenRound from one instance to a compatible instance.
-/
def SeqPhragmenRound.transfer {inst : ABCInstance V C k} {inst' : ABCInstance V C k'}
    (hcompat : inst.Compatible inst')
    (r : SeqPhragmenRound V C inst) : SeqPhragmenRound V C inst' where
  start_loads := r.start_loads
  end_loads := r.end_loads
  already_selected := r.already_selected
  selected := r.selected
  selected_s := r.selected_s
  selected_in_candidates := hcompat.candidates_eq ▸ r.selected_in_candidates
  selected_not_prior := r.selected_not_prior
  supporters_nonempty := by
    rw [← supporters_eq_of_compatible hcompat]
    exact r.supporters_nonempty
  selected_s_nonneg := r.selected_s_nonneg
  s_formula := by
    rw [← supporters_eq_of_compatible hcompat, ← s_value_num_eq_of_compatible hcompat]
    exact r.s_formula
  supporter_loads_le_s := fun i hi => by
    rw [← supporters_eq_of_compatible hcompat] at hi
    exact r.supporter_loads_le_s i hi
  selected_minimal := fun c hc hne => by
    rw [← supporters_eq_of_compatible hcompat, ← s_value_num_eq_of_compatible hcompat]
    have hc' : c ∈ inst.candidates \ r.already_selected := by
      simp only [Finset.mem_sdiff] at hc ⊢
      exact ⟨hcompat.candidates_eq ▸ hc.1, hc.2⟩
    have hne' : (inst.supporters c).Nonempty := by
      rw [supporters_eq_of_compatible hcompat]
      exact hne
    exact r.selected_minimal c hc' hne'
  loads_evolution := fun i hi => by
    rw [← hcompat.voters_eq] at hi
    rw [← hcompat.approves_eq]
    exact r.loads_evolution i hi

/--
The selected candidate is preserved under transfer.
-/
@[simp]
lemma SeqPhragmenRound.transfer_selected {inst : ABCInstance V C k} {inst' : ABCInstance V C k'}
    (hcompat : inst.Compatible inst') (r : SeqPhragmenRound V C inst) :
    (r.transfer hcompat).selected = r.selected := rfl

/--
Transfer a SeqPhragmenWitness from one instance to a compatible instance.
-/
noncomputable def SeqPhragmenWitness.transfer {inst : ABCInstance V C k} {inst' : ABCInstance V C k'}
    (hcompat : inst.Compatible inst')
    (w : SeqPhragmenWitness V C inst) : SeqPhragmenWitness V C inst' where
  num_rounds := w.num_rounds
  rounds := fun t => (w.rounds t).transfer hcompat
  final_loads := w.final_loads
  initial_loads := fun h => w.initial_loads h
  initial_already_selected := fun h => w.initial_already_selected h
  loads_linked := fun t h => w.loads_linked t h
  already_selected_linked := fun t h => w.already_selected_linked t h
  final_loads_correct := w.final_loads_correct
  selected_distinct := fun s t hne hsel => w.selected_distinct s t hne hsel

/--
The committee is preserved under transfer.
-/
lemma SeqPhragmenWitness.transfer_committee {inst : ABCInstance V C k} {inst' : ABCInstance V C k'}
    (hcompat : inst.Compatible inst') (w : SeqPhragmenWitness V C inst) :
    (w.transfer hcompat).committee = w.committee := by
  simp only [SeqPhragmenWitness.committee, SeqPhragmenWitness.transfer,
             SeqPhragmenRound.transfer_selected]

-- ============================================================================
-- DOWNWARD MONOTONICITY: TRUNCATING A WITNESS
-- ============================================================================

/--
Given a witness with num_rounds rounds, we can truncate it to fewer rounds.
This is the key construction for downward committee monotonicity.
-/
noncomputable def SeqPhragmenWitness.truncate {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (n : ℕ) (hn : n ≤ w.num_rounds)
    (hn_pos : 0 < n) :
    SeqPhragmenWitness V C inst where
  num_rounds := n
  rounds := fun t => w.rounds ⟨t.val, Nat.lt_of_lt_of_le t.isLt hn⟩
  final_loads :=
    if h : n > 0
    then (w.rounds ⟨n - 1, Nat.lt_of_lt_of_le (Nat.sub_lt h Nat.one_pos) hn⟩).end_loads
    else fun _ => 0
  initial_loads := fun h => by
    simp only
    have heq : (⟨0, Nat.lt_of_lt_of_le h hn⟩ : Fin w.num_rounds) = ⟨0, Nat.lt_of_lt_of_le hn_pos hn⟩ := rfl
    exact w.initial_loads (Nat.lt_of_lt_of_le hn_pos hn)
  initial_already_selected := fun h => by
    simp only
    exact w.initial_already_selected (Nat.lt_of_lt_of_le hn_pos hn)
  loads_linked := fun t h => by
    simp only
    have h' : t.val + 1 < w.num_rounds := Nat.lt_of_lt_of_le h hn
    exact w.loads_linked ⟨t.val, Nat.lt_of_lt_of_le t.isLt hn⟩ h'
  already_selected_linked := fun t h => by
    simp only
    have h' : t.val + 1 < w.num_rounds := Nat.lt_of_lt_of_le h hn
    exact w.already_selected_linked ⟨t.val, Nat.lt_of_lt_of_le t.isLt hn⟩ h'
  final_loads_correct := by
    simp only
    split_ifs with h
    · rfl
    · omega
  selected_distinct := fun s t hne hsel => by
    have hs : (⟨s.val, Nat.lt_of_lt_of_le s.isLt hn⟩ : Fin w.num_rounds) ≠
              ⟨t.val, Nat.lt_of_lt_of_le t.isLt hn⟩ := by
      intro heq
      apply hne
      exact Fin.ext (Fin.mk.inj heq)
    exact w.selected_distinct _ _ hs hsel

/--
The committee of a truncated witness is a subset of the original committee.
-/
lemma SeqPhragmenWitness.truncate_committee_subset {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (n : ℕ) (hn : n ≤ w.num_rounds) (hn_pos : 0 < n) :
    (w.truncate n hn hn_pos).committee ⊆ w.committee := by
  intro c hc
  simp only [SeqPhragmenWitness.committee, Finset.mem_image, Finset.mem_univ, true_and] at hc ⊢
  obtain ⟨t, rfl⟩ := hc
  exact ⟨⟨t.val, Nat.lt_of_lt_of_le t.isLt hn⟩, rfl⟩

/--
The committee of a truncated witness has cardinality n.
-/
lemma SeqPhragmenWitness.truncate_committee_card {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (n : ℕ) (hn : n ≤ w.num_rounds) (hn_pos : 0 < n) :
    (w.truncate n hn hn_pos).committee.card = n := by
  exact (w.truncate n hn hn_pos).committee_card

-- ============================================================================
-- DOWNWARD MONOTONICITY THEOREM
-- ============================================================================

/--
**Downward Committee Monotonicity for Sequential Phragmén**

If W is a seq-Phragmén outcome for committee size k+1 (with num_rounds = k+1),
then there exists a seq-Phragmén outcome W' for committee size k such that W' ⊆ W.

More precisely: the first k candidates selected form a valid k-outcome.
-/
theorem seq_phragmen_committee_monotonicity_down
    {inst : ABCInstance V C k} {inst' : ABCInstance V C (k + 1)}
    (hcompat : inst.Compatible inst')
    (w' : SeqPhragmenWitness V C inst')
    (hw'_rounds : w'.num_rounds = k + 1)
    (hk_pos : 0 < k) :
    ∃ w : SeqPhragmenWitness V C inst,
      w.num_rounds = k ∧ w.committee ⊆ w'.committee := by
  -- Step 1: Transfer w' from inst' to inst
  let w_transferred := w'.transfer hcompat.symm
  -- Step 2: Truncate to k rounds
  have h_rounds_eq : w_transferred.num_rounds = k + 1 := hw'_rounds
  have h_k_le : k ≤ w_transferred.num_rounds := by omega
  let w := w_transferred.truncate k h_k_le hk_pos
  -- Step 3: Show the properties hold
  refine ⟨w, ?_, ?_⟩
  · -- num_rounds = k
    rfl
  · -- committee ⊆ w'.committee
    -- w.committee ⊆ w_transferred.committee = w'.committee
    calc w.committee
        ⊆ w_transferred.committee := w_transferred.truncate_committee_subset k h_k_le hk_pos
      _ = w'.committee := w'.transfer_committee hcompat.symm

-- ============================================================================
-- UPWARD MONOTONICITY: EXTENDING A WITNESS
-- ============================================================================

/--
The instance has "enough approved candidates" if at least k candidates have supporters.
This is needed for upward monotonicity.
-/
def has_enough_approved_candidates (inst : ABCInstance V C k) : Prop :=
  k ≤ (approvedCandidates inst).card

lemma approvedCandidates_subset_candidates (inst : ABCInstance V C k) :
    approvedCandidates inst ⊆ inst.candidates := by
  intro c hc
  rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hcv⟩
  exact inst.approves_subset v hv hcv

lemma mem_approvedCandidates_iff (inst : ABCInstance V C k) (c : C) :
    c ∈ approvedCandidates inst ↔ c ∈ inst.candidates ∧ (inst.supporters c).Nonempty := by
  constructor
  · intro hc
    rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hcv⟩
    refine ⟨inst.approves_subset v hv hcv, ?_⟩
    refine ⟨v, ?_⟩
    simp [supporters, hv, hcv]
  · rintro ⟨_, hsup⟩
    rcases hsup with ⟨v, hv⟩
    rcases (by simpa [supporters] using hv) with ⟨hvoters, hcv⟩
    exact Finset.mem_biUnion.mpr ⟨v, hvoters, hcv⟩

/--
If fewer candidates are selected than approved candidates exist,
there is an unselected candidate with supporters.
-/
lemma exists_unselected_with_supporters (inst : ABCInstance V C k)
    (selected : Finset C) (hsubset : selected ⊆ approvedCandidates inst)
    (hcard : selected.card < (approvedCandidates inst).card) :
    ∃ c ∈ inst.candidates \ selected, (inst.supporters c).Nonempty := by
  have hcarddiff : (approvedCandidates inst \ selected).card =
      (approvedCandidates inst).card - selected.card :=
    Finset.card_sdiff_of_subset hsubset
  have hpos : 0 < (approvedCandidates inst \ selected).card := by
    have : 0 < (approvedCandidates inst).card - selected.card := Nat.sub_pos_of_lt hcard
    omega
  rcases Finset.card_pos.mp hpos with ⟨c, hc⟩
  have hc_appr : c ∈ approvedCandidates inst := (Finset.mem_sdiff.mp hc).1
  have hc_sel : c ∉ selected := (Finset.mem_sdiff.mp hc).2
  have hc_cand : c ∈ inst.candidates := approvedCandidates_subset_candidates inst hc_appr
  have hsup : (inst.supporters c).Nonempty := (mem_approvedCandidates_iff inst c).1 hc_appr |>.2
  exact ⟨c, Finset.mem_sdiff.mpr ⟨hc_cand, hc_sel⟩, hsup⟩

/--
Among candidates in a nonempty set with supporters, there exists one minimizing s-value.
-/
lemma exists_minimizing_candidate (inst : ABCInstance V C k) (loads : V → ℚ)
    (candidates : Finset C) (hne : candidates.Nonempty)
    (hsup : ∀ c ∈ candidates, (inst.supporters c).Nonempty) :
    ∃ c ∈ candidates,
      ∀ c' ∈ candidates,
        s_value_num inst loads c * (inst.supporters c').card ≤
        s_value_num inst loads c' * (inst.supporters c).card := by
  -- Use the s-value as a rational for comparison
  let s_val : C → ℚ := fun c =>
    if h : (inst.supporters c).Nonempty
    then s_value_num inst loads c / (inst.supporters c).card
    else 0
  have hmin := Finset.exists_min_image candidates s_val hne
  obtain ⟨c, hc_mem, hc_min⟩ := hmin
  refine ⟨c, hc_mem, fun c' hc'_mem => ?_⟩
  have hc_sup := hsup c hc_mem
  have hc'_sup := hsup c' hc'_mem
  have hle : s_val c ≤ s_val c' := hc_min c' hc'_mem
  simp only [s_val, hc_sup, hc'_sup, dite_true] at hle
  have hc_card_pos : (0 : ℚ) < (inst.supporters c).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr hc_sup)
  have hc'_card_pos : (0 : ℚ) < (inst.supporters c').card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr hc'_sup)
  have hc'_card_nonneg : (0 : ℚ) ≤ (inst.supporters c').card := le_of_lt hc'_card_pos
  calc s_value_num inst loads c * (inst.supporters c').card
      = (s_value_num inst loads c / (inst.supporters c).card) *
          (inst.supporters c).card * (inst.supporters c').card := by
            field_simp
    _ ≤ (s_value_num inst loads c' / (inst.supporters c').card) *
          (inst.supporters c).card * (inst.supporters c').card := by
            apply mul_le_mul_of_nonneg_right _ hc'_card_nonneg
            apply mul_le_mul_of_nonneg_right hle
            exact le_of_lt hc_card_pos
    _ = s_value_num inst loads c' * (inst.supporters c).card := by
            field_simp

/--
Update loads: supporters of c get load s, others unchanged.
-/
def seq_phragmen_update_loads (inst : ABCInstance V C k) (loads : V → ℚ) (c : C) (s : ℚ) : V → ℚ :=
  fun v => if c ∈ inst.approves v then s else loads v

lemma seq_phragmen_update_loads_spec (inst : ABCInstance V C k) (loads : V → ℚ) (c : C) (s : ℚ)
    (v : V) (_hv : v ∈ inst.voters) :
    seq_phragmen_update_loads inst loads c s v = if c ∈ inst.approves v then s else loads v := rfl

/--
Construct a new round given:
- Current loads
- Previously selected candidates
- A candidate c minimizing s-value among unselected candidates with supporters
-/
noncomputable def construct_round (inst : ABCInstance V C k)
    (start_loads : V → ℚ) (already_selected : Finset C)
    (c : C) (hc_cand : c ∈ inst.candidates) (hc_new : c ∉ already_selected)
    (hc_sup : (inst.supporters c).Nonempty)
    (hloads_nonneg : ∀ v, 0 ≤ start_loads v)
    (hloads_le : ∀ v ∈ inst.supporters c, start_loads v ≤
        s_value_num inst start_loads c / (inst.supporters c).card)
    (hminimal : ∀ c' ∈ inst.candidates \ already_selected,
        (inst.supporters c').Nonempty →
        s_value_num inst start_loads c * (inst.supporters c').card ≤
        s_value_num inst start_loads c' * (inst.supporters c).card) :
    SeqPhragmenRound V C inst where
  start_loads := start_loads
  end_loads := seq_phragmen_update_loads inst start_loads c (s_value_num inst start_loads c / (inst.supporters c).card)
  already_selected := already_selected
  selected := c
  selected_s := s_value_num inst start_loads c / (inst.supporters c).card
  selected_in_candidates := hc_cand
  selected_not_prior := hc_new
  supporters_nonempty := hc_sup
  selected_s_nonneg := by
    apply div_nonneg
    · have := s_value_num_pos inst start_loads hloads_nonneg c
      linarith
    · exact Nat.cast_nonneg _
  s_formula := by
    have hcard_ne : ((inst.supporters c).card : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hc_sup)
    field_simp [hcard_ne]
  supporter_loads_le_s := hloads_le
  selected_minimal := fun c' hc' hc'_sup => by
    have hmin := hminimal c' hc' hc'_sup
    have hc_card_pos : (0 : ℚ) < (inst.supporters c).card :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr hc_sup)
    have hc'_card_nonneg : (0 : ℚ) ≤ (inst.supporters c').card :=
      Nat.cast_nonneg _
    calc (s_value_num inst start_loads c / (inst.supporters c).card) *
            (inst.supporters c').card
        = s_value_num inst start_loads c * (inst.supporters c').card /
            (inst.supporters c).card := by ring
      _ ≤ s_value_num inst start_loads c' * (inst.supporters c).card /
            (inst.supporters c).card := by
              apply div_le_div_of_nonneg_right hmin (le_of_lt hc_card_pos)
      _ = s_value_num inst start_loads c' := by field_simp
  loads_evolution := fun v _ => rfl

/--
The already_selected at round t equals the set of candidates selected in rounds 0..t-1.
-/
lemma SeqPhragmenWitness.already_selected_eq {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (t : Fin w.num_rounds) :
    (w.rounds t).already_selected =
      (Finset.univ.filter (fun s : Fin w.num_rounds => s.val < t.val)).image
        (fun s => (w.rounds s).selected) := by
  have hrec : ∀ n (hn : n < w.num_rounds),
      (w.rounds ⟨n, hn⟩).already_selected =
        (Finset.univ.filter (fun s : Fin w.num_rounds => s.val < n)).image
          (fun s => (w.rounds s).selected) := by
    intro n
    induction n with
    | zero =>
      intro hn
      simp only [not_lt_zero', Finset.filter_false, Finset.image_empty]
      exact w.initial_already_selected hn
    | succ m ih =>
      intro hm
      have hm' : m < w.num_rounds := Nat.lt_of_succ_lt hm
      have hlink := w.already_selected_linked ⟨m, hm'⟩ hm
      rw [hlink, ih hm']
      ext c
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
                 true_and, Finset.mem_singleton]
      constructor
      · intro hc
        cases hc with
        | inl hc =>
          obtain ⟨s, hs, hcs⟩ := hc
          exact ⟨s, Nat.lt_succ_of_lt hs, hcs⟩
        | inr hc =>
          exact ⟨⟨m, hm'⟩, Nat.lt_succ_self m, hc.symm⟩
      · intro ⟨s, hs, hcs⟩
        by_cases heq : s.val = m
        · right
          have : s = ⟨m, hm'⟩ := Fin.ext heq
          rw [this] at hcs
          exact hcs.symm
        · left
          exact ⟨s, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hs) heq, hcs⟩
  exact hrec t.val t.isLt

/--
Committee equals already_selected ∪ {selected} for the last round.
-/
lemma SeqPhragmenWitness.committee_eq_last_union {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (h : w.num_rounds > 0) :
    w.committee =
      (w.rounds ⟨w.num_rounds - 1, Nat.sub_lt h Nat.one_pos⟩).already_selected ∪
        {(w.rounds ⟨w.num_rounds - 1, Nat.sub_lt h Nat.one_pos⟩).selected} := by
  let last : Fin w.num_rounds := ⟨w.num_rounds - 1, Nat.sub_lt h Nat.one_pos⟩
  rw [w.already_selected_eq last]
  ext c
  simp only [SeqPhragmenWitness.committee, Finset.mem_union, Finset.mem_image,
             Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro ⟨t, htc⟩
    by_cases hlt : t.val < last.val
    · left; exact ⟨t, hlt, htc⟩
    · right
      have heq : t.val = last.val := by
        have := t.isLt
        simp only [last] at hlt ⊢
        omega
      have : t = last := Fin.ext heq
      rw [this] at htc
      exact htc.symm
  · intro hc
    cases hc with
    | inl hc =>
      obtain ⟨t, _, htc⟩ := hc
      exact ⟨t, htc⟩
    | inr hc =>
      exact ⟨last, hc.symm⟩

/--
For an unselected candidate with supporters, its s-value at any round is at least
the selected s-value at that round. This follows from the minimality of selection.
-/
lemma SeqPhragmenWitness.unselected_s_ge_selected {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (t : Fin w.num_rounds) (c : C)
    (hc_cand : c ∈ inst.candidates) (hc_not_sel : c ∉ (w.rounds t).already_selected)
    (hc_sup : (inst.supporters c).Nonempty) :
    (w.rounds t).selected_s ≤
      s_value_num inst (w.rounds t).start_loads c / (inst.supporters c).card := by
  have hmem : c ∈ inst.candidates \ (w.rounds t).already_selected :=
    Finset.mem_sdiff.mpr ⟨hc_cand, hc_not_sel⟩
  have hmin := (w.rounds t).selected_minimal c hmem hc_sup
  have hcard_pos : (0 : ℚ) < (inst.supporters c).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr hc_sup)
  calc (w.rounds t).selected_s
      = (w.rounds t).selected_s * (inst.supporters c).card / (inst.supporters c).card := by
        field_simp
    _ ≤ s_value_num inst (w.rounds t).start_loads c / (inst.supporters c).card := by
        apply div_le_div_of_nonneg_right hmin (le_of_lt hcard_pos)

/--
For an unselected candidate with supporters, its final s-value is at least the budget.
This is because at each round, its s-value was ≥ selected s-value, and s-values increase.
-/
lemma SeqPhragmenWitness.unselected_s_ge_budget {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (c : C)
    (hc_cand : c ∈ inst.candidates) (hc_not_comm : c ∉ w.committee)
    (hc_sup : (inst.supporters c).Nonempty) :
    w.budget ≤ s_value_num inst w.final_loads c / (inst.supporters c).card := by
  by_cases h : w.num_rounds > 0
  · -- There are rounds; budget = sup of s-values
    simp only [SeqPhragmenWitness.budget, h, dite_true]
    apply Finset.sup'_le
    intro t _
    -- At round t, c was not in already_selected (since c ∉ committee)
    have hc_not_sel_t : c ∉ (w.rounds t).already_selected := by
      intro hmem
      have hsub := w.already_selected_subset_committee t
      exact hc_not_comm (hsub hmem)
    -- s^{(t)} ≤ s_c at round t
    have hle_t := w.unselected_s_ge_selected t c hc_cand hc_not_sel_t hc_sup
    -- s_c at round t ≤ s_c at final (since loads increase)
    have hloads_le : ∀ i ∈ inst.supporters c,
        (w.rounds t).start_loads i ≤ w.final_loads i := by
      intro i hi
      have hi_voters : i ∈ inst.voters := (Finset.mem_filter.mp hi).1
      -- start_loads at t ≤ end_loads at last round = final_loads
      have := w.start_loads_nondecreasing t ⟨w.num_rounds - 1, Nat.sub_lt h Nat.one_pos⟩
          (Nat.le_sub_one_of_lt t.isLt) i hi_voters
      have hfinal := w.final_loads_correct
      simp only [h, dite_true] at hfinal
      calc (w.rounds t).start_loads i
          ≤ (w.rounds ⟨w.num_rounds - 1, _⟩).start_loads i := this
        _ ≤ (w.rounds ⟨w.num_rounds - 1, _⟩).end_loads i :=
          (w.rounds ⟨w.num_rounds - 1, _⟩).loads_nondecreasing i hi_voters
        _ = w.final_loads i := (congrFun hfinal i).symm
    have hnum_le : s_value_num inst (w.rounds t).start_loads c ≤
        s_value_num inst w.final_loads c := by
      unfold s_value_num
      have hsum : ∑ i ∈ inst.supporters c, (w.rounds t).start_loads i ≤
          ∑ i ∈ inst.supporters c, w.final_loads i :=
        Finset.sum_le_sum (fun i hi => hloads_le i hi)
      linarith
    have hcard_pos : (0 : ℚ) < (inst.supporters c).card :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr hc_sup)
    calc ((w.rounds t).selected_s : ℝ)
        ≤ s_value_num inst (w.rounds t).start_loads c / (inst.supporters c).card := by
          exact_mod_cast hle_t
      _ ≤ s_value_num inst w.final_loads c / (inst.supporters c).card := by
          apply div_le_div_of_nonneg_right _ (by exact_mod_cast le_of_lt hcard_pos)
          exact_mod_cast hnum_le
  · -- No rounds: budget = 0, s-value ≥ 0
    simp only [SeqPhragmenWitness.budget, h, dite_false]
    apply div_nonneg
    · have : w.final_loads = fun _ => 0 := by
        have := w.final_loads_correct
        simp only [h, dite_false] at this
        exact this
      simp only [s_value_num, this, Finset.sum_const_zero, add_zero]
      norm_num
    · exact Nat.cast_nonneg _

/--
**Upward Committee Monotonicity for Sequential Phragmén** (conditional)

If W is a seq-Phragmén outcome for committee size k, and the (k+1)-instance
has enough approved candidates, then there exists W' ⊇ W that is a (k+1)-outcome.
-/
theorem seq_phragmen_committee_monotonicity_up
    {inst : ABCInstance V C k} {inst' : ABCInstance V C (k + 1)}
    (hcompat : inst.Compatible inst')
    (w : SeqPhragmenWitness V C inst)
    (hw_rounds : w.num_rounds = k)
    (h_enough : has_enough_approved_candidates inst') :
    ∃ w' : SeqPhragmenWitness V C inst',
      w'.num_rounds = k + 1 ∧ w.committee ⊆ w'.committee := by
  -- Step 1: Transfer w to inst'
  let w_transferred := w.transfer hcompat

  -- Step 2: The committee of the transferred witness is the same
  have hw_comm : w_transferred.committee = w.committee := w.transfer_committee hcompat

  -- Step 3: Show there exists an unselected candidate with supporters
  -- This uses h_enough: k+1 ≤ |approvedCandidates inst'|
  -- and the fact that w.committee has cardinality k
  have hcomm_card : w.committee.card = k := by
    have := w.committee_card
    omega

  -- The committee is a subset of approved candidates (any selected candidate has supporters)
  have hcomm_subset_approved : w.committee ⊆ approvedCandidates inst' := by
    intro c hc
    rw [mem_approvedCandidates_iff]
    constructor
    · have hcand := w.committee_subset hc
      exact hcompat.candidates_eq ▸ hcand
    · -- c was selected in some round, so it has supporters
      simp only [SeqPhragmenWitness.committee, Finset.mem_image] at hc
      obtain ⟨t, _, ht⟩ := hc
      have hsup := (w.rounds t).supporters_nonempty
      rw [← ht, ← supporters_eq_of_compatible hcompat]
      exact hsup

  have hex : ∃ c ∈ inst'.candidates \ w.committee,
      (inst'.supporters c).Nonempty := by
    apply exists_unselected_with_supporters inst' w.committee hcomm_subset_approved
    calc w.committee.card = k := hcomm_card
      _ < k + 1 := Nat.lt_succ_self k
      _ ≤ (approvedCandidates inst').card := h_enough

  -- Step 4: Among such candidates, find one minimizing s-value
  -- This requires constructing the extended witness with one more round
  -- The new round uses:
  --   start_loads = w.final_loads (transferred)
  --   already_selected = w.committee
  --   selected = minimizing candidate from hex
  --   selected_s = computed s-value

  -- Uniform construction: extend w_transferred with one more round
  -- Works for k = 0 and k > 0

  -- Find minimizing candidate among unselected candidates with supporters
  let candidates_with_sup := (inst'.candidates \ w.committee).filter
      (fun c => (inst'.supporters c).Nonempty)
  have h_cws_ne : candidates_with_sup.Nonempty := by
    obtain ⟨c, hc_mem, hc_sup⟩ := hex
    exact ⟨c, Finset.mem_filter.mpr ⟨hc_mem, hc_sup⟩⟩
  have h_cws_sup : ∀ c' ∈ candidates_with_sup, (inst'.supporters c').Nonempty := by
    intro c' hc'; exact (Finset.mem_filter.mp hc').2

  obtain ⟨best, hbest_mem, hbest_min⟩ := exists_minimizing_candidate inst'
      w_transferred.final_loads candidates_with_sup h_cws_ne h_cws_sup
  have hbest_in_cand : best ∈ inst'.candidates :=
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hbest_mem).1).1
  have hbest_not_comm : best ∉ w.committee :=
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hbest_mem).1).2
  have hbest_sup : (inst'.supporters best).Nonempty := h_cws_sup best hbest_mem

  -- best is also unselected in the transferred witness
  have hbest_not_trans_comm : best ∉ w_transferred.committee := by
    rw [w.transfer_committee hcompat]
    exact hbest_not_comm

  -- The s-value for the new candidate
  let s_val := s_value_num inst' w_transferred.final_loads best / (inst'.supporters best).card

  -- Budget lower-bounds the s-value of any unselected candidate
  have hs_ge_budget : w_transferred.budget ≤ s_val := by
    have h := w_transferred.unselected_s_ge_budget best hbest_in_cand hbest_not_trans_comm hbest_sup
    -- Unfold the local definition of s_val to align the expressions
    simpa [s_val] using h

  -- Key lemma: for unselected candidates, supporter loads ≤ s-value
  -- This is the crucial invariant of Sequential Phragmén (equation seq04 from the paper):
  --   s_c^{(j)} ≥ s^{(j-1)} ≥ x_i^{(j-1)}
  -- i.e., for any remaining candidate c, its s-value bounds all current loads.
  --
  -- Proof outline:
  -- 1. At each round j, selected candidate had minimum s-value s^{(j)}
  -- 2. Any unselected c had s_c^{(j)} ≥ s^{(j)} (by minimality of selection)
  -- 3. Since loads increase, s-values increase: s_c^{(k)} ≥ s_c^{(j)} ≥ s^{(j)}
  -- 4. So s_c^{(k)} ≥ max_j s^{(j)} = budget
  -- 5. By final_loads_le_budget: load(v) ≤ budget ≤ s_c^{(k)}
  -- best ∉ w_transferred.committee (since transfer preserves committee)
  have hbest_not_trans_comm : best ∉ w_transferred.committee := by
    rw [w.transfer_committee hcompat]
    exact hbest_not_comm

  have hloads_le : ∀ v ∈ inst'.supporters best, w_transferred.final_loads v ≤ s_val := by
    intro v hv
    have hv_voter : v ∈ inst'.voters := by
      simp only [supporters, Finset.mem_filter] at hv
      exact hv.1
    have hload_le_budget : (w_transferred.final_loads v : ℝ) ≤ w_transferred.budget :=
      w_transferred.final_loads_le_budget v hv_voter
    -- Combine: load(v) ≤ budget ≤ s_val (with type casts)
    have : (w_transferred.final_loads v : ℝ) ≤ (s_val : ℝ) :=
      calc (w_transferred.final_loads v : ℝ)
          ≤ w_transferred.budget := hload_le_budget
        _ ≤ s_val := hs_ge_budget
    exact_mod_cast this

  -- Build the new round (round k in 0-indexed)
  let new_round : SeqPhragmenRound V C inst' := {
    start_loads := w_transferred.final_loads
    end_loads := seq_phragmen_update_loads inst' w_transferred.final_loads best s_val
    already_selected := w.committee  -- = w_transferred.committee
    selected := best
    selected_s := s_val
    selected_in_candidates := hbest_in_cand
    selected_not_prior := hbest_not_comm
    supporters_nonempty := hbest_sup
    selected_s_nonneg := by
      -- budget ≥ 0 and s_val ≥ budget
      have hbudget_nonneg : 0 ≤ w_transferred.budget := w_transferred.budget_nonneg
      have hs_val_ge : (0 : ℝ) ≤ s_val := le_trans hbudget_nonneg hs_ge_budget
      -- selected_s has type ℚ, so cast the real inequality back down
      exact_mod_cast hs_val_ge
    s_formula := by
      have hcard_ne : ((inst'.supporters best).card : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hbest_sup)
      simp only [s_val]
      field_simp
    supporter_loads_le_s := hloads_le
    selected_minimal := fun c' hc' hc'_sup => by
      have hc'_in : c' ∈ candidates_with_sup := Finset.mem_filter.mpr ⟨hc', hc'_sup⟩
      -- hbest_min gives us the cross-multiplication inequality
      have hmin := hbest_min c' hc'_in
      -- Convert to the required form: s_val * |supporters c'| ≤ s_value_num c'
      simp only [s_val]
      have hcard_pos : (0 : ℚ) < (inst'.supporters best).card :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr hbest_sup)
      calc (s_value_num inst' w_transferred.final_loads best /
              (inst'.supporters best).card) * (inst'.supporters c').card
          = s_value_num inst' w_transferred.final_loads best *
              (inst'.supporters c').card / (inst'.supporters best).card := by ring
        _ ≤ s_value_num inst' w_transferred.final_loads c' *
              (inst'.supporters best).card / (inst'.supporters best).card := by
            apply div_le_div_of_nonneg_right hmin (le_of_lt hcard_pos)
        _ = s_value_num inst' w_transferred.final_loads c' := by field_simp
    loads_evolution := fun v _ => rfl
  }

  -- Key fact: w_transferred has the same number of rounds as w
  have hw_trans_rounds : w_transferred.num_rounds = k := hw_rounds

  -- Helper to convert indices
  have to_trans_idx : ∀ (n : ℕ) (hn : n < k), n < w_transferred.num_rounds :=
    fun n hn => by simpa [hw_trans_rounds] using hn

  -- Build the extended witness with k+1 rounds
  -- Rounds 0..k-1: from w_transferred
  -- Round k: new_round
  let w' : SeqPhragmenWitness V C inst' := {
    num_rounds := k + 1
    rounds := fun t =>
      if h : t.val < k then
        w_transferred.rounds ⟨t.val, to_trans_idx t.val h⟩
      else
        -- t.val = k (since t < k+1)
        new_round
    final_loads := new_round.end_loads
    initial_loads := fun h => by
      by_cases hk : k = 0
      · subst hk
        -- num_rounds = 1, round 0 is new_round whose start_loads = w_transferred.final_loads = 0
        have hzero : w_transferred.final_loads = fun _ => 0 := by
          have hfinal := w_transferred.final_loads_correct
          simp [hw_trans_rounds] at hfinal
          simpa using hfinal
        have hcomm_empty : w.committee = ∅ := by
          apply Finset.card_eq_zero.mp
          simpa [hw_rounds] using hcomm_card
        simp [new_round, hzero, hcomm_empty]
      · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
        simp only [dif_pos hk_pos]
        have := w_transferred.initial_loads (to_trans_idx 0 hk_pos)
        simpa using this
    initial_already_selected := fun h => by
      by_cases hk : k = 0
      · subst hk
        have hcomm_empty : w.committee = ∅ := by
          apply Finset.card_eq_zero.mp
          simpa [hw_rounds] using hcomm_card
        simp [new_round, hcomm_empty]
      · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
        simp only [dif_pos hk_pos]
        have := w_transferred.initial_already_selected (to_trans_idx 0 hk_pos)
        simpa using this
    loads_linked := fun t ht => by
      -- Need to show round t's end_loads = round (t+1)'s start_loads
      by_cases h : t.val + 1 < k
      · -- Both rounds are from w_transferred
        simp only [dif_pos (Nat.lt_of_succ_lt h), dif_pos h]
        have := w_transferred.loads_linked ⟨t.val, to_trans_idx t.val (Nat.lt_of_succ_lt h)⟩
            (by simpa [hw_trans_rounds] using h)
        simpa using this
      · -- t+1 = k, so round t+1 is new_round
        have ht_eq : t.val + 1 = k := by omega
        have ht_lt : t.val < k := by omega
        simp only [dif_pos ht_lt]
        simp only [show ¬(t.val + 1 < k) by omega, dif_neg, not_false_eq_true]
        -- end_loads of round t = final_loads of w_transferred = start_loads of new_round
        have hlast : t.val = k - 1 := by omega
        have hk_pos : k > 0 := by omega
        have hk_pos' : w_transferred.num_rounds > 0 := by simpa [hw_trans_rounds] using hk_pos
        have hfinal := w_transferred.final_loads_correct
        simp only [hk_pos', dite_true] at hfinal
        -- (w_transferred.rounds ⟨t.val, _⟩).end_loads = w_transferred.final_loads
        have hlast_idx : t.val = w_transferred.num_rounds - 1 := by
          simp only [hw_trans_rounds]; omega
        ext v
        have : (w_transferred.rounds ⟨t.val, to_trans_idx t.val ht_lt⟩).end_loads v =
            (w_transferred.rounds ⟨w_transferred.num_rounds - 1, Nat.sub_lt hk_pos' Nat.one_pos⟩).end_loads v := by
          congr 2
          exact Fin.ext hlast_idx
        rw [this, ← congrFun hfinal v]
    already_selected_linked := fun t ht => by
      by_cases h : t.val + 1 < k
      · simp only [dif_pos (Nat.lt_of_succ_lt h), dif_pos h]
        have := w_transferred.already_selected_linked ⟨t.val, to_trans_idx t.val (Nat.lt_of_succ_lt h)⟩
            (by simpa [hw_trans_rounds] using h)
        simpa using this
      · have ht_eq : t.val + 1 = k := by omega
        have ht_lt : t.val < k := by omega
        simp only [dif_pos ht_lt]
        simp only [show ¬(t.val + 1 < k) by omega, dif_neg, not_false_eq_true]
        have hk_pos : k > 0 := by omega
        have hk_pos' : w_transferred.num_rounds > 0 := by simpa [hw_trans_rounds] using hk_pos
        have hlast_idx : t.val = w_transferred.num_rounds - 1 := by
          have : t.val + 1 = w_transferred.num_rounds := by simpa [hw_trans_rounds] using ht_eq
          omega
        have hcomm_eq := w_transferred.committee_eq_last_union hk_pos'
        calc
          new_round.already_selected
              = w_transferred.committee := by simpa [new_round, hw_comm]
          _ = (w_transferred.rounds ⟨w_transferred.num_rounds - 1, Nat.sub_lt hk_pos' Nat.one_pos⟩).already_selected ∪
                {(w_transferred.rounds ⟨w_transferred.num_rounds - 1, Nat.sub_lt hk_pos' Nat.one_pos⟩).selected} := hcomm_eq
          _ = (w_transferred.rounds ⟨t.val, to_trans_idx t.val ht_lt⟩).already_selected ∪
                {(w_transferred.rounds ⟨t.val, to_trans_idx t.val ht_lt⟩).selected} := by
                -- align the indices using hlast_idx
                have hfin_eq : (⟨t.val, to_trans_idx t.val ht_lt⟩ : Fin w_transferred.num_rounds) =
                    ⟨w_transferred.num_rounds - 1, Nat.sub_lt hk_pos' Nat.one_pos⟩ := by
                  apply Fin.ext
                  simpa [hlast_idx]
                simpa [hfin_eq]
    final_loads_correct := by
      have hkpos : k + 1 > 0 := by omega
      simp [hkpos, new_round]
    selected_distinct := fun s t hne hsel => by
      -- If both from w_transferred, use w_transferred.selected_distinct
      -- If one is new_round, the selected is best ∉ w.committee
      by_cases hs : s.val < k <;> by_cases ht : t.val < k
      · -- Both from w_transferred
        simp only [dif_pos hs, dif_pos ht] at hsel ⊢
        have hne' : (⟨s.val, to_trans_idx s.val hs⟩ : Fin w_transferred.num_rounds) ≠
            ⟨t.val, to_trans_idx t.val ht⟩ := by
          intro heq; apply hne; exact Fin.ext (Fin.mk.inj heq)
        exact w_transferred.selected_distinct _ _ hne' hsel
      · -- s from w_transferred, t is new_round
        simp only [dif_pos hs, show ¬t.val < k by exact ht, dif_neg, not_false_eq_true] at hsel
        -- hsel says w_transferred.rounds[s].selected = best
        -- But best ∉ w.committee, contradiction
        have hs_in_comm : (w_transferred.rounds ⟨s.val, to_trans_idx s.val hs⟩).selected ∈
            w_transferred.committee := by
          simp only [SeqPhragmenWitness.committee, Finset.mem_image]
          exact ⟨⟨s.val, to_trans_idx s.val hs⟩, Finset.mem_univ _, rfl⟩
        rw [w.transfer_committee hcompat] at hs_in_comm
        rw [hsel] at hs_in_comm
        exact hbest_not_comm hs_in_comm
      · -- s is new_round, t from w_transferred
        simp only [show ¬s.val < k by exact hs, dif_neg, not_false_eq_true, dif_pos ht] at hsel
        have ht_in_comm : (w_transferred.rounds ⟨t.val, to_trans_idx t.val ht⟩).selected ∈
            w_transferred.committee := by
          simp only [SeqPhragmenWitness.committee, Finset.mem_image]
          exact ⟨⟨t.val, to_trans_idx t.val ht⟩, Finset.mem_univ _, rfl⟩
        rw [w.transfer_committee hcompat] at ht_in_comm
        rw [← hsel] at ht_in_comm
        exact hbest_not_comm ht_in_comm
      · -- Both new_round, but s ≠ t with s.val ≥ k and t.val ≥ k and both < k+1
        -- So s.val = k = t.val, contradicting s ≠ t
        have : s.val = k := by omega
        have : t.val = k := by omega
        have : s = t := Fin.ext (by omega)
        contradiction
  }

  refine ⟨w', rfl, ?_⟩
  -- Show w.committee ⊆ w'.committee
  intro c hc
  simp only [SeqPhragmenWitness.committee, Finset.mem_image] at hc ⊢
  obtain ⟨t, _, ht⟩ := hc
  -- c = (w.rounds t).selected, and t < k
  -- t : Fin w.num_rounds, so t.val < w.num_rounds = k
  have ht_lt_k : t.val < k := by simpa [hw_rounds] using t.isLt
  -- In w', round t.val uses w_transferred.rounds t
  use ⟨t.val, Nat.lt_succ_of_lt ht_lt_k⟩
  constructor
  · exact Finset.mem_univ _
  · -- Need to show the selected candidates match
    have heq : (w_transferred.rounds ⟨t.val, to_trans_idx t.val ht_lt_k⟩).selected =
        (w.rounds t).selected := by
      simp [w_transferred, SeqPhragmenWitness.transfer, SeqPhragmenRound.transfer_selected]
    have hsel_trans : (w_transferred.rounds ⟨t.val, to_trans_idx t.val ht_lt_k⟩).selected = c := by
      calc
        (w_transferred.rounds ⟨t.val, to_trans_idx t.val ht_lt_k⟩).selected
            = (w.rounds t).selected := heq
        _ = c := ht
    have hround : (w'.rounds ⟨t.val, Nat.lt_succ_of_lt ht_lt_k⟩) =
        w_transferred.rounds ⟨t.val, to_trans_idx t.val ht_lt_k⟩ := by
      simp [w', ht_lt_k]
    simpa [hround] using hsel_trans

end ABCInstance
