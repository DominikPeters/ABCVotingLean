/-
# Sequential Phragmén: Definitions

This file provides a witness-based definition of the Sequential Phragmén rule,
following the formulation from Brill, Freeman, Janson, and Lackner (2024).

## Overview

Sequential Phragmén iteratively builds a committee by selecting candidates that
minimize the maximum voter load. In each round:
1. For each remaining candidate c, compute s_c = (1 + Σᵢ∈Nᶜ xᵢ) / |Nᶜ|
2. Select the candidate c minimizing s_c
3. Update loads: all supporters of c get load s_c

Unlike MES which uses min(ρ, budget), Phragmén **equalizes** all supporter loads.

## Main Definitions
- `SeqPhragmenRound`: A single round of the algorithm
- `SeqPhragmenWitness`: A complete execution trace
- `is_seq_phragmen_outcome`: Definition of seq-Phragmén outcomes

## References
- Brill, Freeman, Janson, Lackner. "Phragmén's Voting Methods and Justified
  Representation". Mathematical Programming, 203: 47-76, 2024.
-/

import ABCVoting.Basic

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- BASIC DEFINITIONS
-- ============================================================================

/--
A load function assigns a non-negative rational load to each voter.
This represents the cumulative "cost" a voter has paid for elected candidates.
-/
abbrev LoadFunction (V : Type*) := V → ℚ

/--
The s-value for a candidate c given current voter loads.
This is the load that all supporters of c would have if c is elected.

Formula: s_c = (1 + Σᵢ∈Nᶜ xᵢ) / |Nᶜ|

We store this in "multiplicative form" to avoid division:
  s_c * |Nᶜ| = 1 + Σᵢ∈Nᶜ xᵢ
-/
def s_value_num (inst : ABCInstance V C k) (loads : V → ℚ) (c : C) : ℚ :=
  1 + ∑ i ∈ inst.supporters c, loads i

/--
The s-value as a rational (requires non-empty supporters).
-/
def s_value (inst : ABCInstance V C k) (loads : V → ℚ) (c : C)
    (_ : (inst.supporters c).Nonempty) : ℚ :=
  s_value_num inst loads c / (inst.supporters c).card

-- ============================================================================
-- SEQUENTIAL PHRAGMÉN ROUND
-- ============================================================================

/--
A single round of Sequential Phragmén execution.

Each round tracks:
- **Loads**: The load each voter has at the start and end of this round
- **already_selected**: Candidates selected in previous rounds
- **selected**: The candidate selected in this round (minimizes s-value)
- **selected_s**: The s-value of the selected candidate

Key properties:
1. The selected candidate is new (not previously selected)
2. The selected candidate has non-empty supporters
3. selected_s satisfies the s-value formula
4. selected_s is minimal among remaining candidates
5. Loads evolve correctly: supporters get load selected_s, others unchanged
-/
structure SeqPhragmenRound (V C : Type*) [DecidableEq V] [DecidableEq C]
    (inst : ABCInstance V C k) where
  /-- Voter loads at the start of this round -/
  start_loads : V → ℚ
  /-- Voter loads at the end of this round -/
  end_loads : V → ℚ

  /-- Candidates already selected in prior rounds -/
  already_selected : Finset C

  /-- The candidate selected in this round -/
  selected : C
  /-- The s-value of the selected candidate -/
  selected_s : ℚ

  -- ===== Core Properties =====

  /-- Selected candidate is in the candidate set -/
  selected_in_candidates : selected ∈ inst.candidates

  /-- Selected candidate was not previously selected -/
  selected_not_prior : selected ∉ already_selected

  /-- Selected candidate has at least one supporter -/
  supporters_nonempty : (inst.supporters selected).Nonempty

  /-- s-value is non-negative -/
  selected_s_nonneg : 0 ≤ selected_s

  /-- The s-value formula (multiplicative form to avoid division):
      selected_s * |N_selected| = 1 + Σᵢ∈N_selected loads_i -/
  s_formula : selected_s * (inst.supporters selected).card =
              inst.s_value_num start_loads selected

  /-- Supporters' previous loads are at most the new s-value. -/
  supporter_loads_le_s :
    ∀ i ∈ inst.supporters selected, start_loads i ≤ selected_s

  /-- Minimality: selected_s ≤ s_c for all remaining candidates c with supporters.
      Using multiplicative form: selected_s * |N_selected| / |N_selected| ≤ s_c_num / |N_c|
      Equivalently: selected_s * |N_c| ≤ s_c_num (when |N_c| > 0) -/
  selected_minimal : ∀ c ∈ inst.candidates \ already_selected,
    (inst.supporters c).Nonempty →
    selected_s * (inst.supporters c).card ≤ inst.s_value_num start_loads c

  /-- Load evolution: supporters of selected get load selected_s,
      others keep their previous load -/
  loads_evolution : ∀ i ∈ inst.voters,
    end_loads i = if selected ∈ inst.approves i
                  then selected_s
                  else start_loads i

-- ============================================================================
-- SEQUENTIAL PHRAGMÉN WITNESS
-- ============================================================================

/--
A witness for a Sequential Phragmén execution.

This captures a complete execution trace of the algorithm, including:
- **Rounds**: All k rounds of the algorithm
- **Consistency**: Loads and selected sets link correctly between rounds
- **Initial conditions**: Loads start at 0, no candidates initially selected

The witness structure allows us to define seq-Phragmén outcomes and prove
properties without implementing the algorithm directly.
-/
structure SeqPhragmenWitness (V C : Type*) [DecidableEq V] [DecidableEq C]
    (inst : ABCInstance V C k) where
  /-- Number of rounds (= committee size) -/
  num_rounds : ℕ

  /-- The rounds of execution -/
  rounds : Fin num_rounds → SeqPhragmenRound V C inst

  /-- Final loads (after all rounds) -/
  final_loads : V → ℚ

  -- ===== Initial Conditions =====

  /-- Initial loads are all 0 -/
  initial_loads : (h : num_rounds > 0) →
    (rounds ⟨0, h⟩).start_loads = fun _ => 0

  /-- First round has empty already_selected -/
  initial_already_selected : (h : num_rounds > 0) →
    (rounds ⟨0, h⟩).already_selected = ∅

  -- ===== Linking Properties =====

  /-- Loads are linked: end loads of round t = start loads of round t+1 -/
  loads_linked : ∀ t : Fin num_rounds, ∀ h : t.val + 1 < num_rounds,
    (rounds t).end_loads = (rounds ⟨t.val + 1, h⟩).start_loads

  /-- already_selected grows correctly: adds the selected candidate each round -/
  already_selected_linked : ∀ t : Fin num_rounds, ∀ h : t.val + 1 < num_rounds,
    (rounds ⟨t.val + 1, h⟩).already_selected =
      (rounds t).already_selected ∪ {(rounds t).selected}

  /-- Final loads = end loads of last round (or all 0s if no rounds) -/
  final_loads_correct :
    if h : num_rounds > 0
    then final_loads = (rounds ⟨num_rounds - 1, Nat.sub_lt h Nat.one_pos⟩).end_loads
    else final_loads = fun _ => 0

  -- ===== Consistency =====

  /-- Selected candidates are distinct across rounds -/
  selected_distinct : ∀ s t : Fin num_rounds, s ≠ t →
    (rounds s).selected ≠ (rounds t).selected

-- ============================================================================
-- COMMITTEE EXTRACTION AND OUTCOME DEFINITION
-- ============================================================================

variable (inst : ABCInstance V C k) in
/--
The resulting committee from a Sequential Phragmén witness.
Extracts the set of selected candidates from all rounds.
-/
def SeqPhragmenWitness.committee (w : SeqPhragmenWitness V C inst) : Finset C :=
  Finset.image (fun t => (w.rounds t).selected) Finset.univ

/--
Definition: A committee W is a Sequential Phragmén outcome if
there exists a valid witness w such that w.committee = W.

This allows reasoning about seq-Phragmén outcomes without implementing the algorithm.
-/
def is_seq_phragmen_outcome (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∃ w : SeqPhragmenWitness V C inst, w.committee = W

-- ============================================================================
-- BASIC LEMMAS
-- ============================================================================

/--
The s-value numerator is always at least 1 (since we add 1 to the sum of loads).
-/
lemma s_value_num_pos (inst : ABCInstance V C k) (loads : V → ℚ)
    (hloads : ∀ v, 0 ≤ loads v) (c : C) :
    1 ≤ inst.s_value_num loads c := by
  unfold s_value_num
  have h : 0 ≤ ∑ i ∈ inst.supporters c, loads i :=
    Finset.sum_nonneg (fun i _ => hloads i)
  linarith

/--
If all loads are non-negative, then s-value is at least 1/|N_c|.
-/
lemma s_value_pos (inst : ABCInstance V C k) (loads : V → ℚ)
    (hloads : ∀ v, 0 ≤ loads v) (c : C)
    (h : (inst.supporters c).Nonempty) :
    0 < inst.s_value loads c h := by
  unfold s_value s_value_num
  apply div_pos
  · have := s_value_num_pos inst loads hloads c
    unfold s_value_num at this
    linarith
  · exact Nat.cast_pos.mpr (Finset.card_pos.mpr h)

/--
Loads are non-decreasing across rounds (Lemma 1 from paper).
This requires knowing that start_loads i ≤ selected_s for all supporters i.
-/
lemma SeqPhragmenRound.loads_nondecreasing {inst : ABCInstance V C k}
    (r : SeqPhragmenRound V C inst)
    (i : V) (hi : i ∈ inst.voters) :
    r.start_loads i ≤ r.end_loads i := by
  rw [r.loads_evolution i hi]
  split_ifs with h
  · -- Supporter case: follows from hypothesis
    have hsup : i ∈ inst.supporters r.selected := by
      simp only [supporters, Finset.mem_filter]
      exact ⟨hi, h⟩
    exact r.supporter_loads_le_s i hsup
  · -- Non-supporter case: load unchanged
    rfl

/--
The committee from a witness is a subset of candidates.
-/
lemma SeqPhragmenWitness.committee_subset {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) :
    w.committee ⊆ inst.candidates := by
  intro c hc
  simp only [SeqPhragmenWitness.committee] at hc
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hc
  exact (w.rounds t).selected_in_candidates

/--
The committee from a witness has cardinality equal to num_rounds.
-/
lemma SeqPhragmenWitness.committee_card {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) :
    w.committee.card = w.num_rounds := by
  simp only [SeqPhragmenWitness.committee]
  rw [Finset.card_image_of_injective]
  · exact Finset.card_fin w.num_rounds
  · intro s t hst
    by_contra hne
    exact w.selected_distinct s t hne hst

/--
Loads at the start of rounds are pointwise non-decreasing across time.
-/
lemma SeqPhragmenWitness.start_loads_nondecreasing {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst)
    (s t : Fin w.num_rounds) (hst : s.val ≤ t.val)
    (i : V) (hi : i ∈ inst.voters) :
    (w.rounds s).start_loads i ≤ (w.rounds t).start_loads i := by
  -- Step lemma: from u to u+1.
  have step :
      ∀ u : Fin w.num_rounds, ∀ h : u.val + 1 < w.num_rounds,
        (w.rounds u).start_loads i ≤ (w.rounds ⟨u.val + 1, h⟩).start_loads i := by
    intro u h
    have hle : (w.rounds u).start_loads i ≤ (w.rounds u).end_loads i :=
      (w.rounds u).loads_nondecreasing i hi
    have hlink_i :
        (w.rounds ⟨u.val + 1, h⟩).start_loads i = (w.rounds u).end_loads i := by
      have := congrArg (fun f => f i) (w.loads_linked u h)
      simpa using this.symm
    simpa [hlink_i] using hle
  -- Induction on the round index.
  let P : (n : ℕ) → s.val ≤ n → Prop :=
    fun n _ => ∀ hn : n < w.num_rounds,
      (w.rounds s).start_loads i ≤ (w.rounds ⟨n, hn⟩).start_loads i
  have hP : P t.val hst := by
    refine Nat.le_induction (m := s.val) (P := P) ?base ?step t.val hst
    · intro hn
      have hs : (⟨s.val, hn⟩ : Fin w.num_rounds) = s := by
        apply Fin.ext
        rfl
      simpa [hs]
    · intro n hsn hn hn1
      have hn' : n < w.num_rounds :=
        lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_of_lt hn1)
      have hstep := step ⟨n, hn'⟩ hn1
      exact le_trans (hn hn') hstep
  exact hP t.isLt

/--
Maximum load is non-decreasing across rounds (part of Lemma 1).
-/
lemma SeqPhragmenWitness.s_values_nondecreasing {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst)
    (s t : Fin w.num_rounds) (hst : s.val < t.val) :
    (w.rounds s).selected_s ≤ (w.rounds t).selected_s := by
  -- Step lemma: the selected s-value is nondecreasing from one round to the next.
  have step :
      ∀ u : Fin w.num_rounds, ∀ h : u.val + 1 < w.num_rounds,
        (w.rounds u).selected_s ≤ (w.rounds ⟨u.val + 1, h⟩).selected_s := by
    intro u h
    -- Compare s_value_num for the next round's selected candidate.
    have hsum :
        ∑ i ∈ inst.supporters (w.rounds ⟨u.val + 1, h⟩).selected,
          (w.rounds u).start_loads i ≤
        ∑ i ∈ inst.supporters (w.rounds ⟨u.val + 1, h⟩).selected,
          (w.rounds ⟨u.val + 1, h⟩).start_loads i := by
      apply Finset.sum_le_sum
      intro i hi
      have hi_voters : i ∈ inst.voters := (Finset.mem_filter.mp hi).1
      have hle := w.start_loads_nondecreasing (s := u) (t := ⟨u.val + 1, h⟩)
        (hst := Nat.le_succ u.val) i hi_voters
      simpa using hle
    have hnum_le :
        inst.s_value_num (w.rounds u).start_loads (w.rounds ⟨u.val + 1, h⟩).selected ≤
          inst.s_value_num (w.rounds ⟨u.val + 1, h⟩).start_loads
            (w.rounds ⟨u.val + 1, h⟩).selected := by
      unfold s_value_num
      linarith
    have hnot_mem :
        (w.rounds ⟨u.val + 1, h⟩).selected ∉ (w.rounds u).already_selected := by
      intro hmem
      have hmem' :
          (w.rounds ⟨u.val + 1, h⟩).selected ∈
            (w.rounds ⟨u.val + 1, h⟩).already_selected := by
        have hlink_sel := w.already_selected_linked u h
        have :
            (w.rounds ⟨u.val + 1, h⟩).selected ∈
              (w.rounds u).already_selected ∪ {(w.rounds u).selected} :=
          Finset.mem_union.mpr (Or.inl hmem)
        simpa [hlink_sel] using this
      exact (w.rounds ⟨u.val + 1, h⟩).selected_not_prior hmem'
    have hmem :
        (w.rounds ⟨u.val + 1, h⟩).selected ∈
          inst.candidates \ (w.rounds u).already_selected := by
      exact Finset.mem_sdiff.mpr
        ⟨(w.rounds ⟨u.val + 1, h⟩).selected_in_candidates, hnot_mem⟩
    have hmin :
        (w.rounds u).selected_s *
            (inst.supporters (w.rounds ⟨u.val + 1, h⟩).selected).card ≤
          inst.s_value_num (w.rounds u).start_loads
            (w.rounds ⟨u.val + 1, h⟩).selected :=
      (w.rounds u).selected_minimal _ hmem
        (w.rounds ⟨u.val + 1, h⟩).supporters_nonempty
    have hmul :
        (w.rounds u).selected_s *
            (inst.supporters (w.rounds ⟨u.val + 1, h⟩).selected).card ≤
          (w.rounds ⟨u.val + 1, h⟩).selected_s *
            (inst.supporters (w.rounds ⟨u.val + 1, h⟩).selected).card := by
      calc
        (w.rounds u).selected_s *
            (inst.supporters (w.rounds ⟨u.val + 1, h⟩).selected).card
            ≤ inst.s_value_num (w.rounds u).start_loads
                (w.rounds ⟨u.val + 1, h⟩).selected := hmin
        _ ≤ inst.s_value_num (w.rounds ⟨u.val + 1, h⟩).start_loads
              (w.rounds ⟨u.val + 1, h⟩).selected := hnum_le
        _ = (w.rounds ⟨u.val + 1, h⟩).selected_s *
              (inst.supporters (w.rounds ⟨u.val + 1, h⟩).selected).card := by
              symm
              exact (w.rounds ⟨u.val + 1, h⟩).s_formula
    have hpos :
        (0 : ℚ) <
          (inst.supporters (w.rounds ⟨u.val + 1, h⟩).selected).card := by
      exact Nat.cast_pos.mpr
        (Finset.card_pos.mpr (w.rounds ⟨u.val + 1, h⟩).supporters_nonempty)
    exact le_of_mul_le_mul_right hmul hpos
  -- Induction on the round index.
  have hle : s.val ≤ t.val := Nat.le_of_lt hst
  let P : (n : ℕ) → s.val ≤ n → Prop :=
    fun n _ => ∀ hn : n < w.num_rounds,
      (w.rounds s).selected_s ≤ (w.rounds ⟨n, hn⟩).selected_s
  have hP : P t.val hle := by
    refine Nat.le_induction (m := s.val) (P := P) ?base ?step t.val hle
    · intro hn
      have hs : (⟨s.val, hn⟩ : Fin w.num_rounds) = s := by
        apply Fin.ext
        rfl
      simpa [hs]
    · intro n hsn hn hn1
      have hn' : n < w.num_rounds :=
        lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_of_lt hn1)
      have hstep := step ⟨n, hn'⟩ hn1
      exact le_trans (hn hn') hstep
  exact hP t.isLt

end ABCInstance
