/-
# Sequential Phragmén: Algorithm Implementation

This file provides a computable implementation of the Sequential Phragmén
algorithm, complementing the witness-based definition in Defs.lean.

The main purpose is to enable verification of concrete examples via `decide`,
making counterexamples easy to state and check.

## Algorithm Overview

Sequential Phragmén iteratively selects candidates:
1. Start with all voters having load 0
2. In each round, for each remaining candidate c compute:
   s_c = (1 + Σᵢ∈Nᶜ xᵢ) / |Nᶜ|
3. Select the candidate c minimizing s_c (break ties by candidate order)
4. Update loads: all supporters of c get load s_c
5. Repeat until k candidates are selected

## References
- Brill, Freeman, Janson, Lackner. "Phragmén's Voting Methods and Justified
  Representation". Mathematical Programming, 203: 47-76, 2024.
-/

import ABCVoting.Rules.SeqPhragmen.Defs
import ABCVoting.Axioms.Efficiency
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.MinMax

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] [LinearOrder V] [LinearOrder C] {k : ℕ}

-- ============================================================================
-- COMPUTING s-VALUE FOR A CANDIDATE
-- ============================================================================

/--
Compute the s-value for a candidate c given current voter loads.
Returns (numerator, denominator) pair to avoid division until comparison.

s_c = (1 + Σᵢ∈Nᶜ xᵢ) / |Nᶜ|

We store it as (1 + Σᵢ∈Nᶜ xᵢ, |Nᶜ|) for exact rational comparison.
-/
def compute_s_value (inst : ABCInstance V C k) (loads : V → ℚ) (c : C) : ℚ × ℕ :=
  let supporters := inst.supporters c
  let num := 1 + ∑ i ∈ supporters, loads i
  (num, supporters.card)

/--
Compare two s-values given as (numerator, denominator) pairs.
s₁ = n₁/d₁ ≤ s₂ = n₂/d₂ iff n₁ * d₂ ≤ n₂ * d₁
-/
def s_value_le (s1 s2 : ℚ × ℕ) : Bool :=
  s1.1 * s2.2 ≤ s2.1 * s1.2

/--
Get the actual s-value as a rational (for load updates).
Returns 0 if no supporters (shouldn't happen for valid candidates).
-/
def s_value_rat (s : ℚ × ℕ) : ℚ :=
  if s.2 = 0 then 0 else s.1 / s.2

-- ============================================================================
-- ALGORITHM STATE
-- ============================================================================

/--
State of the Sequential Phragmén algorithm during execution.
-/
structure SeqPhragmenState (V C : Type*) [DecidableEq V] [DecidableEq C] (k : ℕ)
    (inst : ABCInstance V C k) where
  /-- Current loads for each voter -/
  loads : V → ℚ
  /-- Candidates selected so far -/
  selected : Finset C
  /-- Number of rounds remaining -/
  rounds_remaining : ℕ

/--
Initial state: all voters have load 0, no candidates selected.
-/
def initial_state (inst : ABCInstance V C k) (max_rounds : ℕ) : SeqPhragmenState V C k inst where
  loads := fun _ => 0
  selected := ∅
  rounds_remaining := max_rounds

-- ============================================================================
-- SINGLE STEP
-- ============================================================================

/--
Get a sorted list of candidates (for canonical iteration order / tie-breaking).
-/
def candidates_list (inst : ABCInstance V C k) : List C :=
  inst.candidates.sort (· ≤ ·)

/--
Find the candidate with minimal s-value among those not yet selected.
Returns `none` if no candidate has supporters (shouldn't happen normally).
-/
def find_best_candidate (inst : ABCInstance V C k) (loads : V → ℚ)
    (already_selected : Finset C) : Option (C × ℚ) :=
  let available := (inst.candidates \ already_selected).sort (· ≤ ·)
  -- Filter to candidates with at least one supporter
  let candidates_with_s := available.filterMap fun c =>
    let s := compute_s_value inst loads c
    if s.2 > 0 then some (c, s_value_rat s) else none
  -- Find minimum by s-value (ties broken by list order)
  match candidates_with_s.argmin (fun cs => cs.2) with
  | none => none
  | some (c, s) => some (c, s)

/--
Update loads after selecting a candidate.
All supporters get the new s-value as their load.
-/
def update_loads (inst : ABCInstance V C k) (loads : V → ℚ) (c : C) (s : ℚ) : V → ℚ :=
  fun v =>
    if c ∈ inst.approves v then s
    else loads v

/--
Execute one step of Sequential Phragmén.
Returns the updated state, or the same state if no candidate can be selected.
-/
def seq_phragmen_step (inst : ABCInstance V C k) (state : SeqPhragmenState V C k inst)
    : SeqPhragmenState V C k inst :=
  if state.rounds_remaining = 0 then state
  else
    match find_best_candidate inst state.loads state.selected with
    | none => { state with rounds_remaining := 0 }  -- No valid candidate, terminate
    | some (c, s) =>
      { loads := update_loads inst state.loads c s
        selected := state.selected ∪ {c}
        rounds_remaining := state.rounds_remaining - 1 }

-- State after `n` algorithm steps.
def seq_phragmen_state_at (inst : ABCInstance V C k) : ℕ → SeqPhragmenState V C k inst
  | 0 => initial_state inst k
  | n + 1 => seq_phragmen_step inst (seq_phragmen_state_at inst n)

-- ============================================================================
-- FULL ALGORITHM
-- ============================================================================

/--
The Sequential Phragmén algorithm: returns the committee selected.

This runs Sequential Phragmén starting with all voters having load 0,
selecting candidates until k candidates are selected or no valid candidate remains.
-/
def seq_phragmen_algorithm (inst : ABCInstance V C k) : Finset C :=
  (seq_phragmen_state_at inst k).selected

-- ============================================================================
-- LIST-BASED OUTPUT (for ordered results)
-- ============================================================================

/--
Run Sequential Phragmén and return the selection order as a list.
-/
def seq_phragmen_loop_list (inst : ABCInstance V C k) (state : SeqPhragmenState V C k inst)
    (acc : List C) : List C :=
  if h : state.rounds_remaining = 0 then acc.reverse
  else
    match find_best_candidate inst state.loads state.selected with
    | none => acc.reverse
    | some (c, s) =>
      let new_state : SeqPhragmenState V C k inst :=
        { loads := update_loads inst state.loads c s
          selected := state.selected ∪ {c}
          rounds_remaining := state.rounds_remaining - 1 }
      have : new_state.rounds_remaining < state.rounds_remaining := by
        simp [new_state]
        omega
      seq_phragmen_loop_list inst new_state (c :: acc)
termination_by state.rounds_remaining

/--
The Sequential Phragmén algorithm returning the selection order.
-/
def seq_phragmen_algorithm_list (inst : ABCInstance V C k) : List C :=
  seq_phragmen_loop_list inst (initial_state inst k) []

-- ============================================================================
-- LOADS OUTPUT (for debugging / verification)
-- ============================================================================

/--
State after running the full algorithm (includes final loads).
-/
def seq_phragmen_final_state (inst : ABCInstance V C k) : SeqPhragmenState V C k inst :=
  let loop := fun state =>
    if state.rounds_remaining = 0 then state
    else
      let new_state := seq_phragmen_step inst state
      if new_state.rounds_remaining = state.rounds_remaining then state
      else new_state
  -- Run k iterations
  (List.range k).foldl (fun s _ => loop s) (initial_state inst k)

-- ============================================================================
-- BASIC PROPERTIES
-- ============================================================================

section BasicLemmas

omit [LinearOrder V] [LinearOrder C] in
lemma s_value_rat_eq (inst : ABCInstance V C k) (loads : V → ℚ) (c : C)
    (h : (inst.supporters c).Nonempty) :
    s_value_rat (compute_s_value inst loads c) =
      inst.s_value_num loads c / (inst.supporters c).card := by
  unfold s_value_rat compute_s_value
  have hcard : (inst.supporters c).card ≠ 0 := by
    exact Finset.card_ne_zero.mpr h
  simp [hcard, s_value_num]

omit [LinearOrder V] [LinearOrder C] in
lemma update_loads_nonneg (inst : ABCInstance V C k) (loads : V → ℚ) (c : C) (s : ℚ)
    (hloads : ∀ v, 0 ≤ loads v) (hs : 0 ≤ s) :
    ∀ v, 0 ≤ update_loads inst loads c s v := by
  intro v
  unfold update_loads
  by_cases hcv : c ∈ inst.approves v
  · simp [hcv, hs]
  · simp [hcv, hloads v]

omit [LinearOrder V] [LinearOrder C] in
lemma approvedCandidates_subset_candidates (inst : ABCInstance V C k) :
    inst.approvedCandidates ⊆ inst.candidates := by
  intro c hc
  rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hcv⟩
  exact inst.approves_subset v hv hcv

omit [LinearOrder V] [LinearOrder C] in
lemma mem_approvedCandidates_iff_supporters_nonempty (inst : ABCInstance V C k) (c : C) :
    c ∈ inst.approvedCandidates ↔ (inst.supporters c).Nonempty := by
  constructor
  · intro hc
    rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hcv⟩
    refine ⟨v, ?_⟩
    simp [supporters, hv, hcv]
  · intro hsup
    rcases hsup with ⟨v, hv⟩
    have hv' : v ∈ inst.voters := (Finset.mem_filter.mp hv).1
    have hcv : c ∈ inst.approves v := (Finset.mem_filter.mp hv).2
    exact Finset.mem_biUnion.mpr ⟨v, hv', hcv⟩

omit [LinearOrder V] [LinearOrder C] in
lemma exists_candidate_with_supporters_of_card_lt (inst : ABCInstance V C k)
    (selected : Finset C) (hsubset : selected ⊆ inst.approvedCandidates)
    (hcard : selected.card < inst.approvedCandidates.card) :
    ∃ c ∈ inst.candidates \ selected, (inst.supporters c).Nonempty := by
  classical
  have hsubset' : selected ⊆ inst.approvedCandidates := hsubset
  have hcarddiff :
      (inst.approvedCandidates \ selected).card =
        inst.approvedCandidates.card - selected.card :=
    Finset.card_sdiff_of_subset hsubset'
  have hpos : 0 < (inst.approvedCandidates \ selected).card := by
    have : 0 < inst.approvedCandidates.card - selected.card :=
      Nat.sub_pos_of_lt hcard
    simpa [hcarddiff] using this
  rcases Finset.card_pos.mp hpos with ⟨c, hc⟩
  have hc_appr : c ∈ inst.approvedCandidates := (Finset.mem_sdiff.mp hc).1
  have hc_sel : c ∉ selected := (Finset.mem_sdiff.mp hc).2
  have hc_cand : c ∈ inst.candidates :=
    approvedCandidates_subset_candidates inst hc_appr
  have hsup : (inst.supporters c).Nonempty :=
    (mem_approvedCandidates_iff_supporters_nonempty inst c).1 hc_appr
  exact ⟨c, Finset.mem_sdiff.mpr ⟨hc_cand, hc_sel⟩, hsup⟩

omit [LinearOrder V] [LinearOrder C] in
lemma exists_candidate_with_supporters_of_plentiful (inst : ABCInstance V C k)
    (selected : Finset C) (hsubset : selected ⊆ inst.approvedCandidates)
    (hcard : selected.card < k) (hpl : inst.plentiful) :
    ∃ c ∈ inst.candidates \ selected, (inst.supporters c).Nonempty := by
  have hcard' : selected.card < inst.approvedCandidates.card :=
    lt_of_lt_of_le hcard hpl
  exact exists_candidate_with_supporters_of_card_lt inst selected hsubset hcard'

omit [LinearOrder V] in
lemma find_best_candidate_some_of_exists (inst : ABCInstance V C k) (loads : V → ℚ)
    (selected : Finset C)
    (hex : ∃ c ∈ inst.candidates \ selected, (inst.supporters c).Nonempty) :
    ∃ c s, find_best_candidate inst loads selected = some (c, s) := by
  classical
  rcases hex with ⟨c, hc, hsup⟩
  unfold find_best_candidate
  set available := (inst.candidates \ selected).sort (· ≤ ·) with havailable
  set candidates_with_s :=
    available.filterMap (fun c =>
      let s := compute_s_value inst loads c
      if s.2 > 0 then some (c, s_value_rat s) else none) with hcandidates
  have hmem_avail : c ∈ available := by
    have hc' : c ∈ inst.candidates \ selected := hc
    have hc_list : c ∈ (inst.candidates \ selected).sort (· ≤ ·) :=
      (Finset.mem_sort (s := inst.candidates \ selected) (r := (· ≤ ·))).2 hc'
    simpa [havailable] using hc_list
  have hpos : (compute_s_value inst loads c).2 > 0 := by
    simpa [compute_s_value] using (Finset.card_pos.mpr hsup)
  have hmem : (c, s_value_rat (compute_s_value inst loads c)) ∈ candidates_with_s := by
    apply List.mem_filterMap.mpr
    refine ⟨c, hmem_avail, ?_⟩
    simp [hpos]
  have hne : candidates_with_s ≠ [] := by
    intro hnil
    have : (c, s_value_rat (compute_s_value inst loads c)) ∈ ([] : List (C × ℚ)) := by
      simpa [hnil] using hmem
    simpa using this
  have hargmin_ne :
      candidates_with_s.argmin (fun cs => cs.2) ≠ none := by
    intro hnone
    have hnil : candidates_with_s = [] :=
      (List.argmin_eq_none (f := fun cs => cs.2) (l := candidates_with_s)).1 hnone
    exact hne hnil
  cases hlist : candidates_with_s.argmin (fun cs => cs.2) with
  | none =>
      exact (hargmin_ne hlist).elim
  | some cs =>
      rcases cs with ⟨c', s'⟩
      have hlist' :
          List.argmin (fun cs => cs.2)
              (List.filterMap
                (fun c =>
                  let s := compute_s_value inst loads c
                  if s.2 > 0 then some (c, s_value_rat s) else none)
                available) = some (c', s') := by
        simpa [hcandidates] using hlist
      exact ⟨c', s', by simp [hlist']⟩

omit [LinearOrder V] in
lemma find_best_candidate_mem (inst : ABCInstance V C k) (loads : V → ℚ)
    (already_selected : Finset C) (c : C) (s : ℚ)
    (h : find_best_candidate inst loads already_selected = some (c, s)) :
    c ∈ inst.candidates \ already_selected := by
  classical
  unfold find_best_candidate at h
  set available := (inst.candidates \ already_selected).sort (· ≤ ·) with havailable
  set candidates_with_s :=
    available.filterMap (fun c =>
      let s := compute_s_value inst loads c
      if s.2 > 0 then some (c, s_value_rat s) else none) with hcandidates
  cases hlist : candidates_with_s.argmin (fun cs => cs.2) with
  | none =>
    have hlist' :
        List.argmin (fun cs => cs.2)
          (List.filterMap
            (fun c =>
              let s := compute_s_value inst loads c
              if s.2 > 0 then some (c, s_value_rat s) else none)
            available) = none := by
      simpa [hcandidates] using hlist
    have : False := by
      simpa [hlist'] using h
    exact this.elim
  | some cs =>
    rcases cs with ⟨c', s'⟩
    have hlist' :
        List.argmin (fun cs => cs.2)
          (List.filterMap
            (fun c =>
              let s := compute_s_value inst loads c
              if s.2 > 0 then some (c, s_value_rat s) else none)
            available) = some (c', s') := by
      simpa [hcandidates] using hlist
    simp [hlist'] at h
    rcases h with ⟨hc, hs⟩
    have hc_mem : (c, s) ∈ candidates_with_s := by
      have hc_mem' : (c', s') ∈ candidates_with_s := by
        have : (c', s') ∈ candidates_with_s.argmin (fun cs => cs.2) := by
          simp [hlist]
        exact List.argmin_mem (f := fun cs => cs.2) this
      simpa [hc, hs] using hc_mem'
    have hc_avail : c ∈ available := by
      rcases List.mem_filterMap.mp hc_mem with ⟨a, ha_mem, ha_eq⟩
      by_cases hpos : (compute_s_value inst loads a).2 > 0
      · simp [hpos] at ha_eq
        rcases ha_eq with ⟨ha, _⟩
        subst ha
        simpa using ha_mem
      · simp [hpos] at ha_eq
    have hc_list' : c ∈ (inst.candidates \ already_selected).sort (· ≤ ·) := by
      simpa [havailable] using hc_avail
    exact (Finset.mem_sort (s := inst.candidates \ already_selected) (r := (· ≤ ·))).1 hc_list'

omit [LinearOrder V] in
lemma find_best_candidate_supporters_nonempty (inst : ABCInstance V C k) (loads : V → ℚ)
    (already_selected : Finset C) (c : C) (s : ℚ)
    (h : find_best_candidate inst loads already_selected = some (c, s)) :
    (inst.supporters c).Nonempty := by
  classical
  unfold find_best_candidate at h
  set available := (inst.candidates \ already_selected).sort (· ≤ ·) with havailable
  set candidates_with_s :=
    available.filterMap (fun c =>
      let s := compute_s_value inst loads c
      if s.2 > 0 then some (c, s_value_rat s) else none) with hcandidates
  cases hlist : candidates_with_s.argmin (fun cs => cs.2) with
  | none =>
    have hlist' :
        List.argmin (fun cs => cs.2)
          (List.filterMap
            (fun c =>
              let s := compute_s_value inst loads c
              if s.2 > 0 then some (c, s_value_rat s) else none)
            available) = none := by
      simpa [hcandidates] using hlist
    have : False := by
      simpa [hlist'] using h
    exact this.elim
  | some cs =>
    rcases cs with ⟨c', s'⟩
    have hlist' :
        List.argmin (fun cs => cs.2)
          (List.filterMap
            (fun c =>
              let s := compute_s_value inst loads c
              if s.2 > 0 then some (c, s_value_rat s) else none)
            available) = some (c', s') := by
      simpa [hcandidates] using hlist
    simp [hlist'] at h
    rcases h with ⟨hc, hs⟩
    have hc_mem : (c, s) ∈ candidates_with_s := by
      have hc_mem' : (c', s') ∈ candidates_with_s := by
        have : (c', s') ∈ candidates_with_s.argmin (fun cs => cs.2) := by
          simp [hlist]
        exact List.argmin_mem (f := fun cs => cs.2) this
      simpa [hc, hs] using hc_mem'
    rcases List.mem_filterMap.mp hc_mem with ⟨a, ha_mem, ha_eq⟩
    by_cases hpos : (compute_s_value inst loads a).2 > 0
    · have ha_eq' : a = c := by
        simp [hpos] at ha_eq
        simpa using ha_eq.1
      subst a
      have hcard : (inst.supporters c).card > 0 := by
        simpa [compute_s_value] using hpos
      exact Finset.card_pos.mp hcard
    · simp [hpos] at ha_eq

omit [LinearOrder V] in
lemma find_best_candidate_value (inst : ABCInstance V C k) (loads : V → ℚ)
    (already_selected : Finset C) (c : C) (s : ℚ)
    (h : find_best_candidate inst loads already_selected = some (c, s)) :
    s = s_value_rat (compute_s_value inst loads c) := by
  classical
  unfold find_best_candidate at h
  set available := (inst.candidates \ already_selected).sort (· ≤ ·) with havailable
  set candidates_with_s :=
    available.filterMap (fun c =>
      let s := compute_s_value inst loads c
      if s.2 > 0 then some (c, s_value_rat s) else none) with hcandidates
  cases hlist : candidates_with_s.argmin (fun cs => cs.2) with
  | none =>
    have hlist' :
        List.argmin (fun cs => cs.2)
          (List.filterMap
            (fun c =>
              let s := compute_s_value inst loads c
              if s.2 > 0 then some (c, s_value_rat s) else none)
            available) = none := by
      simpa [hcandidates] using hlist
    have : False := by
      simpa [hlist'] using h
    exact this.elim
  | some cs =>
    rcases cs with ⟨c', s'⟩
    have hlist' :
        List.argmin (fun cs => cs.2)
          (List.filterMap
            (fun c =>
              let s := compute_s_value inst loads c
              if s.2 > 0 then some (c, s_value_rat s) else none)
            available) = some (c', s') := by
      simpa [hcandidates] using hlist
    simp [hlist'] at h
    rcases h with ⟨hc, hs⟩
    have hmem' : (c', s') ∈ candidates_with_s := by
      have : (c', s') ∈ candidates_with_s.argmin (fun cs => cs.2) := by
        simp [hlist]
      exact List.argmin_mem (f := fun cs => cs.2) this
    rcases List.mem_filterMap.mp hmem' with ⟨a, ha_mem, ha_eq⟩
    by_cases hpos : (compute_s_value inst loads a).2 > 0
    · simp [hpos] at ha_eq
      rcases ha_eq with ⟨ha, hs'⟩
      subst ha
      simpa [hc, hs] using hs'.symm
    · simp [hpos] at ha_eq

omit [LinearOrder V] in
lemma find_best_candidate_minimal (inst : ABCInstance V C k) (loads : V → ℚ)
    (already_selected : Finset C) (c : C) (s : ℚ)
    (h : find_best_candidate inst loads already_selected = some (c, s)) :
    ∀ c' ∈ inst.candidates \ already_selected,
      (inst.supporters c').Nonempty →
      s ≤ s_value_rat (compute_s_value inst loads c') := by
  classical
  intro c' hc' hsup
  unfold find_best_candidate at h
  set available := (inst.candidates \ already_selected).sort (· ≤ ·) with havailable
  set candidates_with_s :=
    available.filterMap (fun c =>
      let s := compute_s_value inst loads c
      if s.2 > 0 then some (c, s_value_rat s) else none) with hcandidates
  have hc'_mem : c' ∈ available := by
    have hc'_list' : c' ∈ (inst.candidates \ already_selected).sort (· ≤ ·) := by
      have hc'_fin : c' ∈ inst.candidates \ already_selected := hc'
      exact (Finset.mem_sort (s := inst.candidates \ already_selected) (r := (· ≤ ·))).2 hc'_fin
    simpa [havailable] using hc'_list'
  have hc'_mem' : (c', s_value_rat (compute_s_value inst loads c')) ∈ candidates_with_s := by
    apply List.mem_filterMap.mpr
    refine ⟨c', hc'_mem, ?_⟩
    have hpos : (compute_s_value inst loads c').2 > 0 := by
      simpa [compute_s_value] using (Finset.card_pos.mpr hsup)
    simp [hpos]
  cases hlist : candidates_with_s.argmin (fun cs => cs.2) with
  | none =>
    have hlist' :
        List.argmin (fun cs => cs.2)
          (List.filterMap
            (fun c =>
              let s := compute_s_value inst loads c
              if s.2 > 0 then some (c, s_value_rat s) else none)
            available) = none := by
      simpa [hcandidates] using hlist
    have : False := by
      simpa [hlist'] using h
    exact this.elim
  | some cs =>
    rcases cs with ⟨cmin, smin⟩
    have hlist' :
        List.argmin (fun cs => cs.2)
          (List.filterMap
            (fun c =>
              let s := compute_s_value inst loads c
              if s.2 > 0 then some (c, s_value_rat s) else none)
            available) = some (cmin, smin) := by
      simpa [hcandidates] using hlist
    simp [hlist'] at h
    rcases h with ⟨hc, hs⟩
    have hmem : (c, s) ∈ candidates_with_s := by
      have hmem' : (cmin, smin) ∈ candidates_with_s := by
        have : (cmin, smin) ∈ candidates_with_s.argmin (fun cs => cs.2) := by
          simp [hlist]
        exact List.argmin_mem (f := fun cs => cs.2) this
      simpa [hc, hs] using hmem'
    have hmem_arg : (c, s) ∈ candidates_with_s.argmin (fun cs => cs.2) := by
      simp [hlist, hc, hs]
    have hle := List.le_of_mem_argmin (f := fun cs => cs.2) hc'_mem' hmem_arg
    simpa using hle

omit [LinearOrder V] in
def seq_phragmen_round_of_state (inst : ABCInstance V C k)
    (state : SeqPhragmenState V C k inst) (c : C) (s : ℚ)
    (hbest : find_best_candidate inst state.loads state.selected = some (c, s))
    (hloads : ∀ v, 0 ≤ state.loads v)
    (hle : ∀ v ∈ inst.voters, state.loads v ≤ s) :
    SeqPhragmenRound V C inst := by
  classical
  refine
    { start_loads := state.loads
      end_loads := update_loads inst state.loads c s
      already_selected := state.selected
      selected := c
      selected_s := s
      selected_in_candidates :=
        (Finset.mem_sdiff.mp
          (find_best_candidate_mem inst state.loads state.selected c s hbest)).1
      selected_not_prior :=
        (Finset.mem_sdiff.mp
          (find_best_candidate_mem inst state.loads state.selected c s hbest)).2
      supporters_nonempty := find_best_candidate_supporters_nonempty inst state.loads state.selected c s hbest
      selected_s_nonneg := by
        have hsup := find_best_candidate_supporters_nonempty inst state.loads state.selected c s hbest
        have hs : s = s_value_rat (compute_s_value inst state.loads c) :=
          find_best_candidate_value inst state.loads state.selected c s hbest
        have hpos : 0 < inst.s_value state.loads c hsup :=
          s_value_pos inst state.loads hloads c hsup
        have hs' :
            s = inst.s_value state.loads c hsup := by
          simp [s_value, s_value_rat_eq inst state.loads c hsup, hs]
        exact le_of_lt (by simpa [hs'] using hpos)
      s_formula := by
        have hsup := find_best_candidate_supporters_nonempty inst state.loads state.selected c s hbest
        have hs : s = s_value_rat (compute_s_value inst state.loads c) :=
          find_best_candidate_value inst state.loads state.selected c s hbest
        have hcard : (inst.supporters c).card ≠ 0 := Finset.card_ne_zero.mpr hsup
        -- unfold using s_value_num
        calc
          s * (inst.supporters c).card
              = (inst.s_value_num state.loads c / (inst.supporters c).card) *
                (inst.supporters c).card := by
                    simp [hs, s_value_rat_eq inst state.loads c hsup]
          _ = inst.s_value_num state.loads c := by
                field_simp [hcard]
      supporter_loads_le_s := by
        intro i hi
        have hi_voters : i ∈ inst.voters := (Finset.mem_filter.mp hi).1
        exact hle i hi_voters
      selected_minimal := by
        intro c' hc' hsup
        have hmin :=
          find_best_candidate_minimal inst state.loads state.selected c s hbest c' hc' hsup
        have hpos : (0 : ℚ) ≤ (inst.supporters c').card := by
          exact Nat.cast_nonneg _
        have hcard : (inst.supporters c').card ≠ 0 := Finset.card_ne_zero.mpr hsup
        have hsval :
            s_value_rat (compute_s_value inst state.loads c') =
              inst.s_value_num state.loads c' / (inst.supporters c').card :=
          s_value_rat_eq inst state.loads c' hsup
        calc
          s * (inst.supporters c').card
              ≤ s_value_rat (compute_s_value inst state.loads c') *
                  (inst.supporters c').card := by
                    exact mul_le_mul_of_nonneg_right hmin hpos
          _ = inst.s_value_num state.loads c' := by
                calc
                  s_value_rat (compute_s_value inst state.loads c') *
                      (inst.supporters c').card
                      = (inst.s_value_num state.loads c' / (inst.supporters c').card) *
                          (inst.supporters c').card := by
                            simp [hsval]
                  _ = inst.s_value_num state.loads c' := by
                        field_simp [hcard]
      loads_evolution := by
        intro i hi
        unfold update_loads
        simp }

end BasicLemmas

-- ============================================================================
-- WITNESS CONSTRUCTION (ASSUMING STEP DATA)
-- ============================================================================

section WitnessConstruction

/-- Data needed to build a witness round from a state. -/
structure StepData (inst : ABCInstance V C k) (state : SeqPhragmenState V C k inst) where
  c : C
  s : ℚ
  hbest : find_best_candidate inst state.loads state.selected = some (c, s)
  hloads : ∀ v, 0 ≤ state.loads v
  hle : ∀ v ∈ inst.voters, state.loads v ≤ s
  hrounds : state.rounds_remaining > 0

/-- Build a witness round from step data. -/
def round_of_step (inst : ABCInstance V C k) (state : SeqPhragmenState V C k inst)
    (step : StepData inst state) : SeqPhragmenRound V C inst :=
  seq_phragmen_round_of_state inst state step.c step.s step.hbest step.hloads step.hle

/--
Construct a Sequential Phragmén witness from step data for each round.
This lets us connect the algorithm to the witness-based definition once we
prove suitable step data exists.
-/
def seq_phragmen_witness_of_steps (inst : ABCInstance V C k)
    (hsteps : ∀ t : Fin k, StepData inst (seq_phragmen_state_at inst t.val))
    (hdistinct :
      ∀ s t : Fin k, s ≠ t →
        (round_of_step inst (seq_phragmen_state_at inst s.val) (hsteps s)).selected ≠
          (round_of_step inst (seq_phragmen_state_at inst t.val) (hsteps t)).selected) :
    SeqPhragmenWitness V C inst := by
  refine
    { num_rounds := k
      rounds := fun t => round_of_step inst (seq_phragmen_state_at inst t.val) (hsteps t)
      final_loads := if hk : k > 0
        then (round_of_step inst (seq_phragmen_state_at inst (k - 1))
              (hsteps ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩)).end_loads
        else fun _ => 0
      initial_loads := by
        intro hk
        rfl
      initial_already_selected := by
        intro hk
        rfl
      loads_linked := ?_
      already_selected_linked := ?_
      final_loads_correct := ?_
      selected_distinct := hdistinct }
  · intro t ht
    cases hsteps t with
    | mk c s hbest hloads hle hrounds =>
      -- unfold the next state and use the defining step
      have hne : (seq_phragmen_state_at inst t.val).rounds_remaining ≠ 0 :=
        Nat.ne_of_gt hrounds
      simpa [seq_phragmen_state_at, round_of_step, seq_phragmen_round_of_state,
        seq_phragmen_step, hbest, hne]
  · intro t ht
    cases hsteps t with
    | mk c s hbest hloads hle hrounds =>
      have hne : (seq_phragmen_state_at inst t.val).rounds_remaining ≠ 0 :=
        Nat.ne_of_gt hrounds
      simpa [seq_phragmen_state_at, round_of_step, seq_phragmen_round_of_state,
        seq_phragmen_step, hbest, hne]
  · by_cases hk : k > 0
    · simp [hk]
    · simp [hk]

end WitnessConstruction

-- ============================================================================
-- ALGORITHM → OUTCOME (PLENTIFUL INSTANCES)
-- ============================================================================

omit [LinearOrder V] in
theorem seq_phragmen_algorithm_is_outcome_of_plentiful (inst : ABCInstance V C k)
    (hpl : inst.plentiful) :
    is_seq_phragmen_outcome inst (seq_phragmen_algorithm inst) := by
  classical
  -- 1. Build `StepData` for each round using plentifulness and the fact that
  --    fewer than k candidates have been selected so far.
  have hsteps' :
      ∀ n, n < k →
        ∃ step : StepData inst (seq_phragmen_state_at inst n),
          (seq_phragmen_state_at inst n).selected ⊆ inst.approvedCandidates ∧
          (seq_phragmen_state_at inst n).selected.card = n ∧
          (seq_phragmen_state_at inst n).rounds_remaining = k - n := by
    intro n hn
    induction n with
    | zero =>
        have hsubset : (∅ : Finset C) ⊆ inst.approvedCandidates := by
          intro c hc
          simpa using hc
        have hcard : (∅ : Finset C).card < k := by
          simpa using hn
        have hex :=
          (exists_candidate_with_supporters_of_plentiful inst ∅ hsubset hcard hpl)
        rcases find_best_candidate_some_of_exists inst (fun _ => 0) ∅ hex with ⟨c, s, hbest⟩
        have hsup : (inst.supporters c).Nonempty :=
          find_best_candidate_supporters_nonempty inst (fun _ => 0) ∅ c s hbest
        have hloads : ∀ v, 0 ≤ (fun _ : V => (0 : ℚ)) v := by
          intro v
          simp
        have hs_nonneg : 0 ≤ s := by
          have hspos : 0 < inst.s_value (fun _ => 0) c hsup :=
            s_value_pos inst (fun _ => 0) hloads c hsup
          have hsrat : s = s_value_rat (compute_s_value inst (fun _ => 0) c) :=
            find_best_candidate_value inst (fun _ => 0) ∅ c s hbest
          have hsval :
              s_value_rat (compute_s_value inst (fun _ => 0) c) =
                inst.s_value (fun _ => 0) c hsup := by
            simp [s_value, s_value_rat_eq inst (fun _ => 0) c hsup]
          have : 0 < s := by
            simpa [hsrat, hsval] using hspos
          exact le_of_lt this
        refine ⟨?step0, hsubset, ?card, ?rounds⟩
        · refine
            { c := c
              s := s
              hbest := hbest
              hloads := hloads
              hle := ?_
              hrounds := ?_ }
          · intro v hv
            simpa using hs_nonneg
          · simpa using hn
        · simp [seq_phragmen_state_at, initial_state]
        · simp [seq_phragmen_state_at, initial_state]
    | succ n ih =>
        have hn' : n < k := Nat.lt_of_succ_lt hn
        rcases ih hn' with ⟨step, hsubset, hcard, hrounds_eq⟩
        rcases step with ⟨c, s, hbest, hloads, hle, hrounds⟩
        have hne : (seq_phragmen_state_at inst n).rounds_remaining ≠ 0 :=
          Nat.ne_of_gt hrounds
        have hstate_succ :
            seq_phragmen_state_at inst (n + 1) =
              { loads := update_loads inst (seq_phragmen_state_at inst n).loads c s
                selected := (seq_phragmen_state_at inst n).selected ∪ {c}
                rounds_remaining := (seq_phragmen_state_at inst n).rounds_remaining - 1 } := by
          simpa [seq_phragmen_state_at, seq_phragmen_step, hbest, hne]
        have hmem :=
          find_best_candidate_mem inst (seq_phragmen_state_at inst n).loads
            (seq_phragmen_state_at inst n).selected c s hbest
        have hnot_mem : c ∉ (seq_phragmen_state_at inst n).selected :=
          (Finset.mem_sdiff.mp hmem).2
        have hsup : (inst.supporters c).Nonempty :=
          find_best_candidate_supporters_nonempty inst
            (seq_phragmen_state_at inst n).loads (seq_phragmen_state_at inst n).selected c s hbest
        have hloads' :
            ∀ v, 0 ≤
              update_loads inst (seq_phragmen_state_at inst n).loads c s v := by
          have hs_nonneg : 0 ≤ s := by
            have hspos : 0 < inst.s_value (seq_phragmen_state_at inst n).loads c hsup :=
              s_value_pos inst (seq_phragmen_state_at inst n).loads hloads c hsup
            have hsrat :
                s = s_value_rat (compute_s_value inst (seq_phragmen_state_at inst n).loads c) :=
              find_best_candidate_value inst (seq_phragmen_state_at inst n).loads
                (seq_phragmen_state_at inst n).selected c s hbest
            have hsval :
                s_value_rat (compute_s_value inst (seq_phragmen_state_at inst n).loads c) =
                  inst.s_value (seq_phragmen_state_at inst n).loads c hsup := by
              simp [s_value, s_value_rat_eq inst (seq_phragmen_state_at inst n).loads c hsup]
            have : 0 < s := by
              simpa [hsrat, hsval] using hspos
            exact le_of_lt this
          exact update_loads_nonneg inst (seq_phragmen_state_at inst n).loads c s hloads hs_nonneg
        have hloads'' :
            ∀ v, 0 ≤ (seq_phragmen_state_at inst (n + 1)).loads v := by
          intro v
          simpa [hstate_succ] using (hloads' v)
        have hsubset' :
            (seq_phragmen_state_at inst (n + 1)).selected ⊆ inst.approvedCandidates := by
          intro x hx
          have hx' : x ∈ (seq_phragmen_state_at inst n).selected ∪ {c} := by
            simpa [hstate_succ] using hx
          cases Finset.mem_union.mp hx' with
          | inl hxsel =>
              exact hsubset hxsel
          | inr hxc =>
              have hc_appr : c ∈ inst.approvedCandidates :=
                (mem_approvedCandidates_iff_supporters_nonempty inst c).2 hsup
              have : x = c := by
                simpa using (Finset.mem_singleton.mp hxc)
              simpa [this] using hc_appr
        have hcard' :
            (seq_phragmen_state_at inst (n + 1)).selected.card = n + 1 := by
          simp [hstate_succ, hcard, hnot_mem]
        have hrounds_eq' :
            (seq_phragmen_state_at inst (n + 1)).rounds_remaining = k - (n + 1) := by
          calc
            (seq_phragmen_state_at inst (n + 1)).rounds_remaining
                = (seq_phragmen_state_at inst n).rounds_remaining - 1 := by
                    simp [hstate_succ]
            _ = (k - n) - 1 := by simp [hrounds_eq]
            _ = k - (n + 1) := by
                  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                    (Nat.sub_sub k n 1)
        have hcard_lt : (seq_phragmen_state_at inst (n + 1)).selected.card < k := by
          simpa [hcard'] using hn
        have hex :=
          exists_candidate_with_supporters_of_plentiful inst
            (seq_phragmen_state_at inst (n + 1)).selected hsubset' hcard_lt hpl
        rcases find_best_candidate_some_of_exists inst
          (seq_phragmen_state_at inst (n + 1)).loads
          (seq_phragmen_state_at inst (n + 1)).selected hex with ⟨c', s', hbest'⟩
        have hsup' : (inst.supporters c').Nonempty :=
          find_best_candidate_supporters_nonempty inst
            (seq_phragmen_state_at inst (n + 1)).loads
            (seq_phragmen_state_at inst (n + 1)).selected c' s' hbest'
        have hmem' :=
          find_best_candidate_mem inst (seq_phragmen_state_at inst (n + 1)).loads
            (seq_phragmen_state_at inst (n + 1)).selected c' s' hbest'
        have hmem'_cand : c' ∈ inst.candidates := (Finset.mem_sdiff.mp hmem').1
        have hmem'_not : c' ∉ (seq_phragmen_state_at inst (n + 1)).selected :=
          (Finset.mem_sdiff.mp hmem').2
        have hmem'_not_prev : c' ∉ (seq_phragmen_state_at inst n).selected := by
          intro hmem_prev
          apply hmem'_not
          have : c' ∈ (seq_phragmen_state_at inst n).selected ∪ {c} := by
            exact Finset.mem_union.mpr (Or.inl hmem_prev)
          simpa [hstate_succ] using this
        have hc' :=
          Finset.mem_sdiff.mpr ⟨hmem'_cand, hmem'_not_prev⟩
        have hloads_le_s :
            ∀ v ∈ inst.voters,
              (seq_phragmen_state_at inst (n + 1)).loads v ≤ s := by
          intro v hv
          have hle' : (seq_phragmen_state_at inst n).loads v ≤ s := hle v hv
          by_cases hcv : c ∈ inst.approves v
          · simp [hstate_succ, update_loads, hcv]
          · simp [hstate_succ, update_loads, hcv, hle']
        have hs_le_s' : s ≤ s' := by
          have hmin :
              s ≤ s_value_rat
                (compute_s_value inst (seq_phragmen_state_at inst n).loads c') :=
            find_best_candidate_minimal inst (seq_phragmen_state_at inst n).loads
              (seq_phragmen_state_at inst n).selected c s hbest c' hc' hsup'
          have hsum :
              ∑ i ∈ inst.supporters c', (seq_phragmen_state_at inst n).loads i ≤
                ∑ i ∈ inst.supporters c', (seq_phragmen_state_at inst (n + 1)).loads i := by
            apply Finset.sum_le_sum
            intro i hi
            have hi_voters : i ∈ inst.voters := (Finset.mem_filter.mp hi).1
            have hle_i : (seq_phragmen_state_at inst n).loads i ≤ s := hle i hi_voters
            by_cases hci : c ∈ inst.approves i
            · simp [hstate_succ, update_loads, hci, hle_i]
            · simp [hstate_succ, update_loads, hci]
          have hnum_le :
              inst.s_value_num (seq_phragmen_state_at inst n).loads c' ≤
                inst.s_value_num (seq_phragmen_state_at inst (n + 1)).loads c' := by
            unfold s_value_num
            linarith
          have hcard_nonneg : (0 : ℚ) ≤ (inst.supporters c').card := by
            exact Nat.cast_nonneg _
          have hsval_le :
              s_value_rat (compute_s_value inst (seq_phragmen_state_at inst n).loads c') ≤
                s_value_rat (compute_s_value inst (seq_phragmen_state_at inst (n + 1)).loads c') := by
            have hdiv :
                inst.s_value_num (seq_phragmen_state_at inst n).loads c' /
                    (inst.supporters c').card ≤
                  inst.s_value_num (seq_phragmen_state_at inst (n + 1)).loads c' /
                    (inst.supporters c').card := by
              exact div_le_div_of_nonneg_right hnum_le hcard_nonneg
            simpa [s_value_rat_eq inst (seq_phragmen_state_at inst n).loads c' hsup',
              s_value_rat_eq inst (seq_phragmen_state_at inst (n + 1)).loads c' hsup'] using hdiv
          have hs' :
              s' = s_value_rat (compute_s_value inst
                (seq_phragmen_state_at inst (n + 1)).loads c') :=
            find_best_candidate_value inst (seq_phragmen_state_at inst (n + 1)).loads
              (seq_phragmen_state_at inst (n + 1)).selected c' s' hbest'
          calc
            s ≤ s_value_rat (compute_s_value inst (seq_phragmen_state_at inst n).loads c') := hmin
            _ ≤ s_value_rat
                (compute_s_value inst (seq_phragmen_state_at inst (n + 1)).loads c') := hsval_le
            _ = s' := by symm; exact hs'
        have hle' :
            ∀ v ∈ inst.voters,
              (seq_phragmen_state_at inst (n + 1)).loads v ≤ s' := by
          intro v hv
          exact le_trans (hloads_le_s v hv) hs_le_s'
        have hrounds_pos : (seq_phragmen_state_at inst (n + 1)).rounds_remaining > 0 := by
          have : 0 < k - (n + 1) := Nat.sub_pos_of_lt hn
          simpa [hrounds_eq'] using this
        refine ⟨?step1, hsubset', hcard', hrounds_eq'⟩
        · refine
            { c := c'
              s := s'
              hbest := hbest'
              hloads := hloads''
              hle := hle'
              hrounds := hrounds_pos }
  have hsteps : ∀ t : Fin k, StepData inst (seq_phragmen_state_at inst t.val) := by
    intro t
    exact Classical.choose (hsteps' t.val t.isLt)
  have selected_in_state :
      ∀ s : Fin k, ∀ n, s.val < n → n ≤ k →
        (round_of_step inst (seq_phragmen_state_at inst s.val) (hsteps s)).selected ∈
          (seq_phragmen_state_at inst n).selected := by
    intro s n hlt hnle
    have hle : s.val + 1 ≤ n := Nat.succ_le_of_lt hlt
    let P : (m : ℕ) → s.val + 1 ≤ m → Prop :=
      fun m _ =>
        m ≤ k →
          (round_of_step inst (seq_phragmen_state_at inst s.val) (hsteps s)).selected ∈
            (seq_phragmen_state_at inst m).selected
    have hP : P n hle := by
      refine Nat.le_induction (m := s.val + 1) (P := P) ?base ?step n hle
      · intro hmk
        rcases hsteps s with ⟨c, s', hbest, hloads, hle, hrounds⟩
        have hne : (seq_phragmen_state_at inst s.val).rounds_remaining ≠ 0 :=
          Nat.ne_of_gt hrounds
        have hstate_succ :
            (seq_phragmen_state_at inst (s.val + 1)).selected =
              (seq_phragmen_state_at inst s.val).selected ∪ {c} := by
          simpa [seq_phragmen_state_at, seq_phragmen_step, hbest, hne]
        have hmem : c ∈ (seq_phragmen_state_at inst s.val).selected ∪ {c} := by
          exact Finset.mem_union.mpr (Or.inr (by simp))
        simpa [round_of_step, seq_phragmen_round_of_state, hstate_succ] using hmem
      · intro m hsm hm hmle
        have hmle' : m < k := lt_of_lt_of_le (Nat.lt_succ_self m) hmle
        have hmle'' : m ≤ k := le_trans (Nat.le_of_lt (Nat.lt_succ_self m)) hmle
        have hm' :
            (round_of_step inst (seq_phragmen_state_at inst s.val) (hsteps s)).selected ∈
              (seq_phragmen_state_at inst m).selected := hm hmle''
        rcases hsteps ⟨m, hmle'⟩ with ⟨c, s', hbest, hloads, hle, hrounds⟩
        have hne : (seq_phragmen_state_at inst m).rounds_remaining ≠ 0 :=
          Nat.ne_of_gt hrounds
        have hsel_succ :
            (seq_phragmen_state_at inst (m + 1)).selected =
              (seq_phragmen_state_at inst m).selected ∪ {c} := by
          simpa [seq_phragmen_state_at, seq_phragmen_step, hbest, hne]
        have :
            (round_of_step inst (seq_phragmen_state_at inst s.val) (hsteps s)).selected ∈
              (seq_phragmen_state_at inst m).selected ∪ {c} := by
          exact Finset.mem_union.mpr (Or.inl hm')
        simpa [hsel_succ] using this
    exact hP hnle
  -- 2. Distinctness of selected candidates across rounds.
  have hdistinct :
      ∀ s t : Fin k, s ≠ t →
        (round_of_step inst (seq_phragmen_state_at inst s.val) (hsteps s)).selected ≠
          (round_of_step inst (seq_phragmen_state_at inst t.val) (hsteps t)).selected := by
    intro s t hst
    have hne : s.val ≠ t.val := by
      intro hst'
      apply hst
      exact Fin.ext hst'
    cases lt_or_gt_of_ne hne with
    | inl hlt =>
        have hmem : (round_of_step inst (seq_phragmen_state_at inst s.val) (hsteps s)).selected ∈
            (seq_phragmen_state_at inst t.val).selected :=
          selected_in_state s t.val hlt (Nat.le_of_lt t.isLt)
        intro hEq
        have hmem' :
            (round_of_step inst (seq_phragmen_state_at inst t.val) (hsteps t)).selected ∈
              (seq_phragmen_state_at inst t.val).selected := by
          simpa [hEq] using hmem
        have hmem'' :
            (round_of_step inst (seq_phragmen_state_at inst t.val) (hsteps t)).selected ∈
              (round_of_step inst (seq_phragmen_state_at inst t.val) (hsteps t)).already_selected := by
          simpa [round_of_step, seq_phragmen_round_of_state] using hmem'
        exact (round_of_step inst (seq_phragmen_state_at inst t.val) (hsteps t)).selected_not_prior hmem''
    | inr hgt =>
        have hmem : (round_of_step inst (seq_phragmen_state_at inst t.val) (hsteps t)).selected ∈
            (seq_phragmen_state_at inst s.val).selected :=
          selected_in_state t s.val hgt (Nat.le_of_lt s.isLt)
        intro hEq
        have hmem' :
            (round_of_step inst (seq_phragmen_state_at inst s.val) (hsteps s)).selected ∈
              (seq_phragmen_state_at inst s.val).selected := by
          simpa [hEq] using hmem
        have hmem'' :
            (round_of_step inst (seq_phragmen_state_at inst s.val) (hsteps s)).selected ∈
              (round_of_step inst (seq_phragmen_state_at inst s.val) (hsteps s)).already_selected := by
          simpa [round_of_step, seq_phragmen_round_of_state] using hmem'
        exact (round_of_step inst (seq_phragmen_state_at inst s.val) (hsteps s)).selected_not_prior hmem''
  -- 3. Construct the witness from step data.
  refine ⟨seq_phragmen_witness_of_steps inst hsteps hdistinct, ?_⟩
  -- 4. Relate the witness committee to `seq_phragmen_algorithm`.
  -- TODO: show the committee from the witness equals the algorithm’s output.
  let w := seq_phragmen_witness_of_steps inst hsteps hdistinct
  have hcard_final :
      (seq_phragmen_state_at inst k).selected.card = k := by
    by_cases hk : k = 0
    · subst hk
      simp [seq_phragmen_state_at, initial_state]
    · have hkpos : k > 0 := Nat.pos_of_ne_zero hk
      have hk' : k - 1 < k := Nat.sub_lt hkpos Nat.one_pos
      have hspec := Classical.choose_spec (hsteps' (k - 1) hk')
      have hsteps_k :
          (seq_phragmen_state_at inst (k - 1)).selected.card = k - 1 := hspec.2.1
      rcases hsteps ⟨k - 1, Nat.sub_lt hkpos Nat.one_pos⟩ with ⟨c, s, hbest, hloads, hle, hrounds⟩
      have hne : (seq_phragmen_state_at inst (k - 1)).rounds_remaining ≠ 0 :=
        Nat.ne_of_gt hrounds
      have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hkpos)
      have hstate_succ :
          (seq_phragmen_state_at inst k).selected =
            (seq_phragmen_state_at inst (k - 1)).selected ∪ {c} := by
        calc
          (seq_phragmen_state_at inst k).selected
              = (seq_phragmen_state_at inst (k - 1 + 1)).selected := by
                  simpa [hk1]
          _ = (seq_phragmen_state_at inst (k - 1)).selected ∪ {c} := by
                simp [seq_phragmen_state_at, seq_phragmen_step, hbest, hne]
      have hmem :=
        find_best_candidate_mem inst (seq_phragmen_state_at inst (k - 1)).loads
          (seq_phragmen_state_at inst (k - 1)).selected c s hbest
      have hnot_mem : c ∉ (seq_phragmen_state_at inst (k - 1)).selected :=
        (Finset.mem_sdiff.mp hmem).2
      have hks : k - 1 + 1 = k := hk1
      calc
        (seq_phragmen_state_at inst k).selected.card
            = ((seq_phragmen_state_at inst (k - 1)).selected ∪ {c}).card := by
                simpa [hstate_succ]
        _ = (seq_phragmen_state_at inst (k - 1)).selected.card + 1 := by
              simp [hnot_mem]
        _ = k := by
              simpa [hsteps_k, hks]
  have hcommittee_subset :
      w.committee ⊆ (seq_phragmen_state_at inst k).selected := by
    intro c hc
    simp [SeqPhragmenWitness.committee] at hc
    rcases hc with ⟨t, ht, rfl⟩
    have hmem :
        (round_of_step inst (seq_phragmen_state_at inst t.val) (hsteps t)).selected ∈
          (seq_phragmen_state_at inst k).selected :=
      selected_in_state t k t.isLt (Nat.le_refl k)
    simpa using hmem
  have hcommittee_card : w.committee.card = k :=
    SeqPhragmenWitness.committee_card (inst := inst) w
  have hfinal_card : (seq_phragmen_state_at inst k).selected.card = k := hcard_final
  have hcommittee_eq :
      w.committee = (seq_phragmen_state_at inst k).selected := by
    apply Finset.eq_of_subset_of_card_le hcommittee_subset
    simpa [hcommittee_card, hfinal_card]
  simpa [hcommittee_eq, seq_phragmen_algorithm]

-- TODO: Once `find_best_candidate_some_of_exists` is proved, finish:
-- - `seq_phragmen_stepdata_exists_of_plentiful`
-- - `seq_phragmen_algorithm_is_outcome_of_plentiful`

end ABCInstance

-- ============================================================================
-- TEST EXAMPLE
-- ============================================================================

namespace SeqPhragmenTest

open ABCInstance Finset

/-- Test instance from Example 3 in the paper:
- 5 voters with approval sets:
  - A₁ = {a}
  - A₂ = {b}
  - A₃ = {b, c}
  - A₄ = {a, b, c}
  - A₅ = {d}
- k = 3
- Expected: First b (s=1/3), then a (s=2/3), then c or d (tie at s=1)
-/

abbrev V := Fin 5
abbrev C := Fin 4  -- a=0, b=1, c=2, d=3

def test_approves : V → Finset C
  | ⟨0, _⟩ => {0}        -- A₁ = {a}
  | ⟨1, _⟩ => {1}        -- A₂ = {b}
  | ⟨2, _⟩ => {1, 2}     -- A₃ = {b, c}
  | ⟨3, _⟩ => {0, 1, 2}  -- A₄ = {a, b, c}
  | ⟨4, _⟩ => {3}        -- A₅ = {d}

lemma test_approves_subset (v : V) (_ : v ∈ (univ : Finset V)) :
    test_approves v ⊆ (univ : Finset C) := subset_univ _

def test_inst : ABCInstance V C 3 where
  voters := univ
  candidates := univ
  approves := test_approves
  approves_subset := test_approves_subset
  voters_nonempty := ⟨0, mem_univ _⟩
  k_pos := by norm_num
  k_le_m := by simp [Fintype.card_fin]

-- See what the algorithm produces
#eval seq_phragmen_algorithm_list test_inst
-- Expected: [1, 0, 2] or [1, 0, 3] depending on tie-breaking
-- That is: b first (s=1/3), then a (s=2/3), then c or d (s=1)

-- Verify with native_decide
set_option linter.style.nativeDecide false in
example : seq_phragmen_algorithm test_inst = {0, 1, 2} := by native_decide

-- Explanation:
-- Round 1: s_a = (1+0+0)/(2) = 1/2, s_b = (1+0+0+0)/3 = 1/3,
--          s_c = (1+0+0)/2 = 1/2, s_d = (1+0)/1 = 1
--          Select b (s=1/3), voters 1,2,3 get load 1/3
-- Round 2: s_a = (1+0+1/3)/2 = 2/3, s_c = (1+1/3+1/3)/2 = 5/6, s_d = 1
--          Select a (s=2/3), voters 0,3 get load 2/3
-- Round 3: s_c = (1+1/3+2/3)/2 = 1, s_d = 1
--          Tie! Select c (first by tie-breaking)

end SeqPhragmenTest
