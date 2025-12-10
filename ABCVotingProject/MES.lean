/-
# Method of Equal Shares (MES)

This file defines the Method of Equal Shares voting rule and proves it satisfies EJR.

## Overview

The Method of Equal Shares is a sequential voting rule where:
- Each voter starts with a budget of 1
- Candidates are selected one at a time
- Each selected candidate costs n/k (price), paid by supporters
- The ρ-value determines how the cost is shared: each supporter pays min(ρ, remaining_budget)
- At each round, the candidate with minimum ρ is selected
- The algorithm terminates when no candidate is affordable

## Formalization Approach

We define MES outcomes via a witness structure that captures an execution trace.
This allows us to later define algorithms and prove they produce valid witnesses.
-/

import ABCVotingProject.ABC
import Mathlib.Order.WithBot

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C]

-- ============================================================================
-- 1. BASIC DEFINITIONS
-- ============================================================================

-- ρ value: either a rational or ⊤ (unaffordable)
abbrev RhoValue := WithTop ℚ

-- Price per candidate: n/k
def price (inst : ABCInstance V C) : ℚ := inst.voters.card / inst.k

-- Supporters of candidate c (voters who approve c)
def supporters (inst : ABCInstance V C) (c : C) : Finset V :=
  inst.voters.filter (c ∈ inst.approves ·)

-- Total remaining budget of c's supporters
def supporter_budget (inst : ABCInstance V C) (budgets : V → ℚ) (c : C) : ℚ :=
  ∑ i ∈ inst.supporters c, budgets i

-- ============================================================================
-- 2. MES ROUND STRUCTURE
-- ============================================================================

/--
A single round of MES execution.

Each round tracks:
- Budgets at start and end of the round
- ρ-values for all candidates (⊤ if unaffordable)
- Which candidates were already selected in prior rounds
- The selected candidate and its ρ-value
-/
structure MESRound (V C : Type*) [DecidableEq V] [DecidableEq C]
    (inst : ABCInstance V C) where
  -- Budgets at start and end of this round
  start_budgets : V → ℚ
  end_budgets : V → ℚ

  -- ρ-values for all candidates (⊤ means unaffordable)
  rho : C → RhoValue

  -- Candidates already selected in prior rounds
  already_selected : Finset C

  -- The selected candidate and its ρ-value
  selected : C
  selected_rho : ℚ

  -- ===== Properties =====

  -- Selected candidate is in candidates but not already selected
  selected_in_candidates : selected ∈ inst.candidates
  selected_not_prior : selected ∉ already_selected

  -- ρ-value is non-negative
  selected_rho_nonneg : 0 ≤ selected_rho

  -- ρ-values are ⊤ iff candidate is unaffordable
  rho_infinite_iff : ∀ c ∈ inst.candidates,
    rho c = ⊤ ↔ inst.supporter_budget start_budgets c < inst.price

  -- For affordable candidates, ρ satisfies the equality constraint
  rho_equality : ∀ c ∈ inst.candidates, ∀ ρ_c : ℚ, rho c = ↑ρ_c →
    ∑ i ∈ inst.supporters c, min ρ_c (start_budgets i) = inst.price

  -- For affordable candidates, some supporter has budget ≥ ρ
  -- This is satisfied by the minimum ρ (where some voter's budget equals ρ)
  -- and ensures we can bound ρ by supporter budgets
  rho_witness : ∀ c ∈ inst.candidates, ∀ ρ_c : ℚ, rho c = ↑ρ_c →
    ∃ i ∈ inst.supporters c, ρ_c ≤ start_budgets i

  -- Selected candidate has the stored ρ value
  selected_has_rho : rho selected = ↑selected_rho

  -- Selected has minimal ρ among candidates not yet selected
  selected_minimal : ∀ c ∈ inst.candidates \ already_selected,
    rho selected ≤ rho c

  -- Budget evolution: supporters of selected pay, others don't
  budget_evolution : ∀ i ∈ inst.voters,
    end_budgets i = if selected ∈ inst.approves i
                    then start_budgets i - min selected_rho (start_budgets i)
                    else start_budgets i

-- ============================================================================
-- 3. MES WITNESS STRUCTURE
-- ============================================================================

/--
A witness for an MES execution.

This captures a complete execution trace of the Method of Equal Shares,
including all rounds, budget evolution, and termination.
-/
structure MESWitness (V C : Type*) [DecidableEq V] [DecidableEq C]
    (inst : ABCInstance V C) where
  -- Number of rounds (= committee size)
  num_rounds : ℕ

  -- The rounds of execution
  rounds : Fin num_rounds → MESRound V C inst

  -- Final budgets (after all rounds)
  final_budgets : V → ℚ

  -- ===== Initial conditions =====

  -- Initial budgets are 1
  initial_budgets : (h : num_rounds > 0) →
    (rounds ⟨0, h⟩).start_budgets = fun _ => 1

  -- First round has empty already_selected
  initial_already_selected : (h : num_rounds > 0) →
    (rounds ⟨0, h⟩).already_selected = ∅

  -- ===== Linking properties =====

  -- Rounds are linked: end budgets of round t = start budgets of round t+1
  budgets_linked : ∀ t : Fin num_rounds, ∀ h : t.val + 1 < num_rounds,
    (rounds t).end_budgets = (rounds ⟨t.val + 1, h⟩).start_budgets

  -- already_selected grows correctly
  already_selected_linked : ∀ t : Fin num_rounds, ∀ h : t.val + 1 < num_rounds,
    (rounds ⟨t.val + 1, h⟩).already_selected =
      (rounds t).already_selected ∪ {(rounds t).selected}

  -- Final budgets = end budgets of last round (or all 1s if no rounds)
  final_budgets_correct :
    if h : num_rounds > 0
    then final_budgets = (rounds ⟨num_rounds - 1, Nat.sub_lt h Nat.one_pos⟩).end_budgets
    else final_budgets = fun _ => 1

  -- ===== Consistency =====

  -- Selected candidates are distinct
  selected_distinct : ∀ s t : Fin num_rounds, s ≠ t →
    (rounds s).selected ≠ (rounds t).selected

  -- ===== Termination =====

  -- All remaining candidates are unaffordable with final budgets
  termination : ∀ c ∈ inst.candidates,
    (∀ t : Fin num_rounds, (rounds t).selected ≠ c) →
    inst.supporter_budget final_budgets c < inst.price

-- ============================================================================
-- 4. MES OUTCOME DEFINITION
-- ============================================================================

variable (inst : ABCInstance V C) in
-- The resulting committee from a witness
def MESWitness.committee (w : MESWitness V C inst) : Finset C :=
  Finset.image (fun t => (w.rounds t).selected) Finset.univ

-- Definition: W is an MES outcome
def is_mes_outcome (inst : ABCInstance V C) (W : Finset C) : Prop :=
  ∃ w : MESWitness V C inst, w.committee = W

-- ============================================================================
-- 5. BASIC LEMMAS ABOUT MES ROUNDS
-- ============================================================================

-- Payment is non-negative
omit [DecidableEq V] in
lemma payment_nonneg (budgets : V → ℚ) (i : V) (ρ : ℚ) (hρ : 0 ≤ ρ) (hb : 0 ≤ budgets i) :
    0 ≤ min ρ (budgets i) := le_min hρ hb

-- Payment is at most the budget
omit [DecidableEq V] in
lemma payment_le_budget (budgets : V → ℚ) (i : V) (ρ : ℚ) :
    min ρ (budgets i) ≤ budgets i := min_le_right ρ (budgets i)

-- Payment is at most ρ
omit [DecidableEq V] in
lemma payment_le_rho (budgets : V → ℚ) (i : V) (ρ : ℚ) :
    min ρ (budgets i) ≤ ρ := min_le_left ρ (budgets i)

-- ============================================================================
-- 6. LEMMAS ABOUT BUDGET EVOLUTION
-- ============================================================================

section BudgetEvolution

variable (inst : ABCInstance V C) (w : MESWitness V C inst)

-- Committee equals the image of selected over all rounds
lemma committee_eq_image :
    w.committee = Finset.image (fun t => (w.rounds t).selected) Finset.univ := rfl

-- Selected candidates are injective as a function
lemma selected_injective : Function.Injective (fun t => (w.rounds t).selected) := by
  intro s t hst
  by_contra hne
  exact w.selected_distinct s t hne hst

-- Committee has size num_rounds
lemma committee_card : w.committee.card = w.num_rounds := by
  rw [committee_eq_image]
  rw [Finset.card_image_of_injective _ (selected_injective inst w)]
  exact Finset.card_fin w.num_rounds

-- already_selected at round t contains exactly {selected[0], ..., selected[t-1]}
lemma mem_already_selected_iff (t : Fin w.num_rounds) (c : C) :
    c ∈ (w.rounds t).already_selected ↔ ∃ s : Fin w.num_rounds, s.val < t.val ∧
      (w.rounds s).selected = c := by
  induction' hn : t.val with n ih generalizing t
  · -- Base case: t = 0, already_selected = ∅
    have hpos : w.num_rounds > 0 := t.pos
    have ht0 : t = ⟨0, hpos⟩ := Fin.ext hn
    rw [ht0, w.initial_already_selected hpos]
    simp only [Finset.notMem_empty, false_iff, not_exists, not_and]
    intro s hs_lt
    omega
  · -- Inductive case: t.val = n + 1
    have hn_lt : n < w.num_rounds := by omega
    let t' : Fin w.num_rounds := ⟨n, hn_lt⟩
    have ht_lt : n + 1 < w.num_rounds := by omega
    have ht_eq : t = ⟨n + 1, ht_lt⟩ := Fin.ext hn
    -- Use already_selected_linked: at t, already_selected = already_selected[t'] ∪ {selected[t']}
    have hlink : (w.rounds t).already_selected =
        (w.rounds t').already_selected ∪ {(w.rounds t').selected} := by
      have h_succ : t'.val + 1 < w.num_rounds := by simp only [t']; omega
      have := w.already_selected_linked t' h_succ
      simp only [t'] at this
      rw [ht_eq]
      convert this using 2
    rw [hlink, Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro h
      rcases h with h_old | h_new
      · -- c was in already_selected[t']
        have ih' := ih t' rfl
        rw [ih'] at h_old
        obtain ⟨s, hs_lt, hs_eq⟩ := h_old
        exact ⟨s, by omega, hs_eq⟩
      · -- c = selected[t']
        exact ⟨t', by simp only [t']; omega, h_new.symm⟩
    · intro ⟨s, hs_lt, hs_eq⟩
      by_cases hs_n : s.val < n
      · -- s < n, so c was in already_selected[t']
        left
        have ih' := ih t' rfl
        rw [ih']
        exact ⟨s, hs_n, hs_eq⟩
      · -- s.val = n, so c = selected[t']
        right
        have hs_eq_n : s.val = n := by omega
        have hs_eq_t' : s = t' := Fin.ext hs_eq_n
        rw [hs_eq_t'] at hs_eq
        exact hs_eq.symm

end BudgetEvolution

-- ============================================================================
-- 7. KEY LEMMAS FOR EJR PROOF
-- ============================================================================

section EJRProof

variable {inst : ABCInstance V C}

-- First, we need to track what a voter paid in total
def total_paid (w : MESWitness V C inst) (i : V) : ℚ :=
  ∑ t : Fin w.num_rounds,
    if (w.rounds t).selected ∈ inst.approves i
    then min (w.rounds t).selected_rho ((w.rounds t).start_budgets i)
    else 0

-- The number of committee members that voter i approves
def voter_utility (w : MESWitness V C inst) (i : V) : ℕ :=
  (w.committee ∩ inst.approves i).card

-- The set of rounds where voter i paid (approved the selected candidate)
def paying_rounds (w : MESWitness V C inst) (i : V) : Finset (Fin w.num_rounds) :=
  Finset.univ.filter (fun t => (w.rounds t).selected ∈ inst.approves i)

-- Paying rounds before t
def paying_rounds_before (w : MESWitness V C inst) (i : V) (t : Fin w.num_rounds) :
    Finset (Fin w.num_rounds) :=
  Finset.univ.filter (fun s => s.val < t.val ∧ (w.rounds s).selected ∈ inst.approves i)

-- Utility before round t (number of approved candidates selected before t)
def utility_before (w : MESWitness V C inst) (i : V) (t : Fin w.num_rounds) : ℕ :=
  (paying_rounds_before w i t).card

-- paying_rounds_before is a subset of paying_rounds
lemma paying_rounds_before_subset (w : MESWitness V C inst) (i : V) (t : Fin w.num_rounds) :
    paying_rounds_before w i t ⊆ paying_rounds w i := by
  intro s hs
  simp only [paying_rounds_before, paying_rounds, Finset.mem_filter, Finset.mem_univ,
    true_and] at hs ⊢
  exact hs.2

-- utility_before ≤ voter_utility (final utility) - proved after paying_rounds_card_eq_utility
-- (forward declaration style - the actual lemma is below)

-- ============================================================================
-- UNIFIED ROUND INVARIANTS
-- ============================================================================

-- Start budget at round t equals 1 minus sum of payments before t
-- This is the key budget tracking lemma for intermediate rounds
lemma start_budget_eq (w : MESWitness V C inst) (i : V) (hi : i ∈ inst.voters)
    (t : Fin w.num_rounds) :
    (w.rounds t).start_budgets i = 1 -
      ∑ s ∈ paying_rounds_before w i t,
        min (w.rounds s).selected_rho ((w.rounds s).start_budgets i) := by
  unfold paying_rounds_before
  obtain ⟨tval, htval⟩ := t
  induction tval with
  | zero =>
    -- t = 0: start_budgets = 1, no rounds before
    have hstart := congrFun (w.initial_budgets htval) i
    simp only [hstart]
    have hfilt : Finset.univ.filter (fun s : Fin w.num_rounds =>
        s.val < 0 ∧ (w.rounds s).selected ∈ inst.approves i) = ∅ := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt_zero', false_and,
        Finset.notMem_empty]
    simp only [hfilt, Finset.sum_empty, sub_zero]
  | succ n ih =>
    -- t.val = n + 1: start_budgets[t] = end_budgets[t-1]
    have hn_lt : n < w.num_rounds := Nat.lt_of_succ_lt htval
    have ih' := ih hn_lt
    let t' : Fin w.num_rounds := ⟨n, hn_lt⟩
    -- Link: end_budgets[t'] = start_budgets[t]
    have hlink : (w.rounds t').end_budgets i = (w.rounds ⟨n + 1, htval⟩).start_budgets i := by
      have hsucc : t'.val + 1 < w.num_rounds := htval
      have hlinked := w.budgets_linked t' hsucc
      exact congrFun hlinked i
    have hevol := (w.rounds t').budget_evolution i hi
    -- end_budgets[t'] = start_budgets[t'] - payment at t'
    rw [← hlink, hevol, ih']
    -- Split the filter: {s | s < n+1 ∧ ...} = {s | s < n ∧ ...} ∪ ({t'} if approved)
    have hfilt : Finset.univ.filter (fun s : Fin w.num_rounds =>
          s.val < n + 1 ∧ (w.rounds s).selected ∈ inst.approves i) =
        Finset.univ.filter (fun s : Fin w.num_rounds =>
          s.val < n ∧ (w.rounds s).selected ∈ inst.approves i) ∪
        (if (w.rounds t').selected ∈ inst.approves i then {t'} else ∅) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, t']
      constructor
      · intro ⟨hs_lt, hs_app⟩
        by_cases hs : s.val < n
        · left; exact ⟨hs, hs_app⟩
        · right
          have hs_eq : s.val = n := by omega
          have hs_eq' : s = ⟨n, hn_lt⟩ := Fin.ext hs_eq
          subst hs_eq'
          simp only [hs_app, ↓reduceIte, Finset.mem_singleton]
      · intro h
        rcases h with ⟨hs_lt, hs_app⟩ | h_eq
        · exact ⟨by omega, hs_app⟩
        · split_ifs at h_eq with happ
          · simp only [Finset.mem_singleton] at h_eq
            rw [h_eq]
            simp only [t']
            exact ⟨by omega, happ⟩
          · simp only [Finset.notMem_empty] at h_eq
    rw [hfilt]
    split_ifs with h
    · -- Voter approved the candidate at round t'
      have hdisj : Disjoint (Finset.univ.filter (fun s : Fin w.num_rounds =>
            s.val < n ∧ (w.rounds s).selected ∈ inst.approves i)) {t'} := by
        rw [Finset.disjoint_singleton_right, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and, not_and, t']
        intro _; omega
      rw [Finset.sum_union hdisj, Finset.sum_singleton]
      -- Need to show the sum form equals after substitution
      simp only [ih', t']
      ring
    · -- Voter did not approve
      simp only [Finset.union_empty]

-- Budget is always non-negative (payment ≤ current budget)
-- Proved by induction: at each step, payment ≤ current budget
lemma start_budget_nonneg (w : MESWitness V C inst) (i : V) (hi : i ∈ inst.voters)
    (t : Fin w.num_rounds) :
    (w.rounds t).start_budgets i ≥ 0 := by
  -- Direct induction on t.val
  obtain ⟨tval, htval⟩ := t
  induction tval with
  | zero =>
    -- At round 0, budget = 1
    have hstart := congrFun (w.initial_budgets htval) i
    simp only [hstart]
    norm_num
  | succ n ih =>
    -- At round n+1, budget = end_budget of round n
    have hn_lt : n < w.num_rounds := Nat.lt_of_succ_lt htval
    have ih' := ih hn_lt
    let t' : Fin w.num_rounds := ⟨n, hn_lt⟩
    -- Link: end_budgets[t'] = start_budgets[n+1]
    have hlink : (w.rounds t').end_budgets i = (w.rounds ⟨n + 1, htval⟩).start_budgets i := by
      have hlinked := w.budgets_linked t' htval
      exact congrFun hlinked i
    -- Budget evolution at round t'
    have hevol := (w.rounds t').budget_evolution i hi
    rw [← hlink, hevol]
    split_ifs with h
    · -- Voter approved: budget = start - min(ρ, start)
      -- This is non-negative since min(ρ, start) ≤ start
      have h_payment_le : min (w.rounds t').selected_rho ((w.rounds t').start_budgets i) ≤
          (w.rounds t').start_budgets i := min_le_right _ _
      linarith
    · -- Voter didn't approve: budget unchanged
      exact ih'

-- Key lemma: If all ρ values before t were ≤ bound, then budget ≥ 1 - utility_before × bound
lemma start_budget_lower_bound (w : MESWitness V C inst) (i : V) (hi : i ∈ inst.voters)
    (t : Fin w.num_rounds) (bound : ℚ) (_ : 0 ≤ bound)
    (h_rho : ∀ s : Fin w.num_rounds, s.val < t.val →
      (w.rounds s).selected ∈ inst.approves i → (w.rounds s).selected_rho ≤ bound) :
    (w.rounds t).start_budgets i ≥ 1 - (utility_before w i t : ℚ) * bound := by
  rw [start_budget_eq w i hi t]
  -- Sum over paying_rounds_before ≤ |paying_rounds_before| * bound = utility_before * bound
  have h_sum_le : ∑ s ∈ paying_rounds_before w i t,
      min (w.rounds s).selected_rho ((w.rounds s).start_budgets i) ≤
      (utility_before w i t : ℚ) * bound := by
    unfold utility_before
    calc ∑ s ∈ paying_rounds_before w i t,
          min (w.rounds s).selected_rho ((w.rounds s).start_budgets i)
        ≤ ∑ s ∈ paying_rounds_before w i t, (w.rounds s).selected_rho := by
          apply Finset.sum_le_sum
          intro s _
          exact min_le_left _ _
      _ ≤ ∑ _ ∈ paying_rounds_before w i t, bound := by
          apply Finset.sum_le_sum
          intro s hs
          simp only [paying_rounds_before, Finset.mem_filter, Finset.mem_univ, true_and] at hs
          exact h_rho s hs.1 hs.2
      _ = (paying_rounds_before w i t).card * bound := by
          simp [Finset.sum_const, nsmul_eq_mul]
  linarith

-- Number of paying rounds equals voter utility
lemma paying_rounds_card_eq_utility (w : MESWitness V C inst) (i : V) :
    (paying_rounds w i).card = voter_utility w i := by
  unfold paying_rounds voter_utility
  unfold MESWitness.committee
  have h_inj : Function.Injective (fun t => (w.rounds t).selected) := by
    intro s t hst
    by_contra h
    exact w.selected_distinct s t h hst
  rw [← Finset.card_image_of_injective _ h_inj]
  congr 1
  ext c
  simp only [mem_filter, mem_univ, true_and, mem_inter, mem_image, Fin.exists_iff]
  aesop

-- Final budget equals 1 minus total paid (main budget tracking lemma)
-- This is proved by induction on rounds, tracking that budget evolves correctly
lemma final_budget_eq (w : MESWitness V C inst) (i : V) (hi : i ∈ inst.voters) :
    w.final_budgets i = 1 - total_paid w i := by
  unfold total_paid
  cases' Nat.eq_zero_or_pos w.num_rounds with h0 hpos
  · -- No rounds: final_budgets = 1, sum is empty
    have huniv : (Finset.univ : Finset (Fin w.num_rounds)) = ∅ := by
      rw [h0]; rfl
    simp only [huniv, Finset.sum_empty, sub_zero]
    have hfinal := w.final_budgets_correct
    simp only [h0] at hfinal
    exact congrFun hfinal i
  · -- At least one round: use induction to track budget
    -- We'll prove by strong induction that end_budgets after round t equals
    -- 1 minus sum of payments through round t
    have hlast : w.num_rounds - 1 < w.num_rounds := Nat.sub_lt hpos Nat.one_pos
    -- Key claim: for any round t, end_budgets equals 1 - payments through t
    have hend : ∀ t : Fin w.num_rounds,
        (w.rounds t).end_budgets i = 1 - ∑ s ∈ Finset.univ.filter (·.val ≤ t.val),
          if (w.rounds s).selected ∈ inst.approves i
          then min (w.rounds s).selected_rho ((w.rounds s).start_budgets i)
          else 0 := by
      intro t
      induction' hn : t.val with n ih_n generalizing t
      · -- Base case: t = 0
        have ht0 : t = ⟨0, t.pos⟩ := Fin.ext hn
        rw [ht0]
        -- start_budgets at round 0 is 1
        have hstart : (w.rounds ⟨0, t.pos⟩).start_budgets i = 1 := by
          have := w.initial_budgets t.pos
          exact congrFun this i
        -- Use budget_evolution
        have hevol := (w.rounds ⟨0, t.pos⟩).budget_evolution i hi
        rw [hevol, hstart]
        -- Filter for ≤ 0 is just {0}
        have hfilt : Finset.univ.filter (fun s : Fin w.num_rounds => s.val ≤ 0) = {⟨0, t.pos⟩} := by
          ext s
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
          omega
        rw [hfilt, Finset.sum_singleton]
        simp only [hstart]; split_ifs with h <;> ring
      · -- Inductive case: t.val = n + 1
        have hn_lt : n < w.num_rounds := by omega
        let t' : Fin w.num_rounds := ⟨n, hn_lt⟩
        have ih := ih_n t' rfl
        -- Link: end of t' = start of t
        have hlink : (w.rounds t').end_budgets i = (w.rounds t).start_budgets i := by
          have hsucc : t'.val + 1 < w.num_rounds := by simp only [t']; omega
          have hlinked := w.budgets_linked t' hsucc
          have ht_eq : t = ⟨n + 1, by omega⟩ := Fin.ext hn
          rw [ht_eq]
          exact congrFun hlinked i
        -- Use evolution at round t
        have hevol := (w.rounds t).budget_evolution i hi
        rw [hevol, ← hlink, ih]
        -- Filter for ≤ t.val = filter for ≤ n ∪ {t}
        have hfilt : Finset.univ.filter (fun s : Fin w.num_rounds => s.val ≤ t.val) =
            Finset.univ.filter (fun s : Fin w.num_rounds => s.val ≤ n) ∪ {t} := by
          ext s
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
            Finset.mem_singleton, Fin.ext_iff, hn]
          omega
        have hdisj : Disjoint (Finset.univ.filter (fun s : Fin w.num_rounds => s.val ≤ n)) {t} := by
          rw [Finset.disjoint_singleton_right]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hn]
          omega
        rw [← hn, hfilt, Finset.sum_union hdisj, Finset.sum_singleton]
        -- Express start_budgets in terms of sum
        have hstart_eq : (w.rounds t).start_budgets i = 1 - ∑ x ∈ Finset.univ.filter (fun s : Fin w.num_rounds => s.val ≤ n),
            if (w.rounds x).selected ∈ inst.approves i then min (w.rounds x).selected_rho ((w.rounds x).start_budgets i) else 0 := by
          rw [← hlink, ih]
        split_ifs with h
        · simp only [← hstart_eq]; linarith
        · ring
    -- Apply hend to last round
    have hfinal := w.final_budgets_correct
    simp only [hpos, dite_true] at hfinal
    rw [congrFun hfinal i, hend ⟨w.num_rounds - 1, hlast⟩]
    -- Show filter for ≤ (num_rounds - 1) equals univ
    have hfilter : Finset.univ.filter (fun s : Fin w.num_rounds => s.val ≤ w.num_rounds - 1) = Finset.univ := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      omega
    simp only [hfilter]

-- Final budget is non-negative (corollary of start_budget_nonneg)
lemma final_budget_nonneg (w : MESWitness V C inst) (i : V) (hi : i ∈ inst.voters) :
    w.final_budgets i ≥ 0 := by
  have hfinal := w.final_budgets_correct
  cases' Nat.eq_zero_or_pos w.num_rounds with h0 hpos
  · -- No rounds: final_budgets = 1
    simp only [h0] at hfinal
    rw [congrFun hfinal i]
    norm_num
  · -- At least one round: final_budgets = end_budgets of last round
    simp only [hpos, dite_true] at hfinal
    rw [congrFun hfinal i]
    -- end_budgets = start_budgets - payment (or unchanged)
    let last : Fin w.num_rounds := ⟨w.num_rounds - 1, Nat.sub_lt hpos Nat.one_pos⟩
    have hevol := (w.rounds last).budget_evolution i hi
    rw [hevol]
    split_ifs with h
    · -- Voter approved: end = start - min(ρ, start) ≥ 0
      have hstart_nonneg := start_budget_nonneg w i hi last
      have hpay_le : min (w.rounds last).selected_rho ((w.rounds last).start_budgets i) ≤
          (w.rounds last).start_budgets i := min_le_right _ _
      linarith
    · -- Voter didn't approve: end = start ≥ 0
      exact start_budget_nonneg w i hi last

-- An ℓ-large group has |S|/ℓ ≥ n/k = price
lemma l_large_card_ge_price (S : Finset V) (ℓ : ℕ) (hℓ_pos : 0 < ℓ)
    (hS_large : inst.is_l_large S ℓ) : S.card * (1 / ℓ : ℚ) ≥ inst.price := by
  unfold price is_l_large at *
  have hk_pos : (inst.k : ℚ) > 0 := Nat.cast_pos.mpr inst.k_pos
  have hℓ_pos' : (ℓ : ℚ) > 0 := Nat.cast_pos.mpr hℓ_pos
  calc S.card * (1 / ℓ : ℚ) = (S.card : ℚ) / ℓ := by ring
    _ ≥ inst.voters.card / inst.k := by
        have h1 : (inst.voters.card : ℚ) * ℓ ≤ S.card * inst.k := by
          calc (inst.voters.card : ℚ) * ℓ = ℓ * inst.voters.card := by ring
            _ ≤ S.card * inst.k := by exact_mod_cast hS_large
        field_simp
        linarith

-- If an ℓ-large group S all approve candidate c, and each voter in S has budget ≥ 1/ℓ,
-- then the supporter budget for c is at least the price
lemma supporter_budget_ge_price_of_cohesive (S : Finset V) (c : C) (ℓ : ℕ)
    (budgets : V → ℚ)
    (hℓ_pos : 0 < ℓ)
    (hS_voters : S ⊆ inst.voters)
    (hS_large : inst.is_l_large S ℓ)
    (hc_approved : ∀ i ∈ S, c ∈ inst.approves i)
    (h_budgets_nonneg : ∀ i ∈ inst.supporters c, i ∉ S → 0 ≤ budgets i)
    (h_budget_ge : ∀ i ∈ S, budgets i ≥ 1 / ℓ) :
    inst.supporter_budget budgets c ≥ inst.price := by
  unfold supporter_budget
  have hS_sub_supporters : S ⊆ inst.supporters c := by
    intro i hi
    unfold supporters
    exact Finset.mem_filter.mpr ⟨hS_voters hi, hc_approved i hi⟩
  calc ∑ i ∈ inst.supporters c, budgets i
      ≥ ∑ i ∈ S, budgets i :=
        Finset.sum_le_sum_of_subset_of_nonneg hS_sub_supporters h_budgets_nonneg
    _ ≥ ∑ _ ∈ S, (1 / ℓ : ℚ) := Finset.sum_le_sum h_budget_ge
    _ = S.card * (1 / ℓ) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≥ inst.price := l_large_card_ge_price S ℓ hℓ_pos hS_large

-- Case ℓ = 1: If voter has 0 representatives, they paid nothing, so budget = 1
lemma budget_eq_one_of_no_reps (w : MESWitness V C inst) (i : V) (hi : i ∈ inst.voters)
    (h_no_reps : voter_utility w i = 0) :
    w.final_budgets i = 1 := by
  rw [final_budget_eq w i hi]
  have h_no_payments : total_paid w i = 0 := by
    unfold total_paid
    apply Finset.sum_eq_zero
    intro t _
    split_ifs with h
    · -- If i approved selected candidate at round t, it would be in committee ∩ approves i
      exfalso
      have : (w.rounds t).selected ∈ w.committee ∩ inst.approves i := by
        simp only [mem_inter, h, and_true]
        unfold MESWitness.committee
        exact mem_image_of_mem _ (mem_univ t)
      rw [voter_utility, Finset.card_eq_zero] at h_no_reps
      exact Finset.notMem_empty _ (h_no_reps ▸ this)
    · rfl
  linarith

-- Case ℓ ≥ 2: If voter has ≤ ℓ-1 representatives and each ρ was ≤ 1/ℓ,
-- then final budget ≥ 1/ℓ
-- (Note: This proof divides by ℓ-1, so requires ℓ ≥ 2)
lemma budget_lower_bound (w : MESWitness V C inst) (i : V) (hi : i ∈ inst.voters)
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (h_utility : voter_utility w i ≤ ℓ - 1)
    (h_rho : ∀ t : Fin w.num_rounds, (w.rounds t).selected ∈ inst.approves i →
      (w.rounds t).selected_rho ≤ 1 / ℓ) :
    w.final_budgets i ≥ 1 / ℓ := by
  rw [final_budget_eq w i hi]
  -- total_paid ≤ (number of payments) * (max payment per round)
  -- number of payments = voter_utility ≤ ℓ - 1
  -- max payment ≤ ρ ≤ 1/ℓ (by h_rho)
  -- So total_paid ≤ (ℓ - 1) * (1/ℓ) = 1 - 1/ℓ
  -- Hence final_budget ≥ 1 - (1 - 1/ℓ) = 1/ℓ
  have h_total_bound : total_paid w i ≤ (ℓ - 1 : ℕ) * (1 / ℓ : ℚ) := by
    -- Each payment is at most ρ, which is at most 1/ℓ
    have h_payment_bound : ∀ t : Fin w.num_rounds,
        (if (w.rounds t).selected ∈ inst.approves i
         then min (w.rounds t).selected_rho ((w.rounds t).start_budgets i)
         else 0 : ℚ) ≤
        (if (w.rounds t).selected ∈ inst.approves i then 1 / ℓ else 0 : ℚ) := by
      intro t
      split_ifs with h
      · exact le_trans (min_le_left _ _) (h_rho t h)
      · rfl
    -- total_paid is the sum of such terms
    have h1 : total_paid w i ≤ ∑ t : Fin w.num_rounds,
        (if (w.rounds t).selected ∈ inst.approves i then 1 / ℓ else 0 : ℚ) := by
      unfold total_paid
      exact Finset.sum_le_sum (fun t _ => h_payment_bound t)
    -- This sum equals (number of paying rounds) * (1/ℓ)
    have h2 : ∑ t : Fin w.num_rounds,
        (if (w.rounds t).selected ∈ inst.approves i then 1 / ℓ else 0 : ℚ) =
        (paying_rounds w i).card * (1 / ℓ) := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rfl
    -- paying_rounds has size = voter_utility
    have h3 : (paying_rounds w i).card * (1 / ℓ : ℚ) = (voter_utility w i : ℚ) * (1 / ℓ) := by
      rw [paying_rounds_card_eq_utility]
    -- voter_utility ≤ ℓ - 1
    have h4 : (voter_utility w i : ℚ) * (1 / ℓ) ≤ (ℓ - 1 : ℕ) * (1 / ℓ : ℚ) := by
      have : (voter_utility w i : ℚ) ≤ (ℓ - 1 : ℕ) := by exact_mod_cast h_utility
      have hpos : (0 : ℚ) ≤ 1 / ℓ := by positivity
      exact mul_le_mul_of_nonneg_right this hpos
    linarith
  have hℓ_pos : (ℓ : ℚ) > 0 := by positivity
  have h1 : (ℓ - 1 : ℕ) * (1 / ℓ : ℚ) = 1 - 1 / ℓ := by
    have hsub : ((ℓ - 1 : ℕ) : ℚ) = (ℓ : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ ℓ)]
      simp
    rw [hsub]
    field_simp
  linarith [h_total_bound, h1]

end EJRProof

-- ============================================================================
-- 8. MAIN THEOREM: MES SATISFIES EJR
-- ============================================================================

/--
The Method of Equal Shares satisfies EJR.

**Proof sketch (from the paper):**
Consider an ℓ-cohesive group S. Assume for contradiction that every voter in S
has fewer than ℓ representatives in W.

1. When the algorithm stopped, some voter i ∈ S must have budget < p/|S|.
   (Otherwise, a commonly-approved candidate would be (p/|S|)-affordable.)

2. Since i has ≤ ℓ-1 representatives, for some representative i must have paid > (1 - p/|S|)/(ℓ-1).

3. Consider the first candidate c' selected where some voter from S paid > 1/ℓ.
   At that moment, c' is not (1/ℓ)-affordable.

4. But each voter in S had ≤ ℓ-1 representatives so far, each costing ≤ 1/ℓ,
   so each has budget ≥ 1/ℓ.

5. Since |S| ≥ ℓn/k, we have |S|·(1/ℓ) ≥ n/k = p.
   So a commonly-approved candidate is (1/ℓ)-affordable, contradiction.
-/
theorem mes_satisfies_ejr (inst : ABCInstance V C) (W : Finset C)
    (h_mes : inst.is_mes_outcome W) : inst.is_ejr W := by
  obtain ⟨w, hw⟩ := h_mes
  -- EJR property: for every ℓ-cohesive group S, some voter has ≥ ℓ representatives
  unfold is_ejr
  intro S ℓ hS_voters hℓ_pos hS_cohesive
  -- By contradiction: suppose every voter in S has < ℓ representatives
  by_contra h_no_reps
  push_neg at h_no_reps
  -- h_no_reps : ∀ i ∈ S, (W ∩ inst.approves i).card < ℓ
  -- This means voter_utility w i ≤ ℓ - 1 for all i ∈ S
  have h_utility : ∀ i ∈ S, voter_utility w i ≤ ℓ - 1 := by
    intro i hi
    have := h_no_reps i hi
    unfold voter_utility
    rw [hw]
    omega
  -- Key: |S| ≥ ℓ * n / k, and common_approvals S has ≥ ℓ candidates
  obtain ⟨hS_large, hS_common⟩ := hS_cohesive
  -- S is nonempty (since it's ℓ-large with ℓ ≥ 1)
  have hS_ne : S.Nonempty := l_large_nonempty inst S ℓ hℓ_pos hS_large
  -- Get a commonly-approved candidate not in W
  -- (If all common approvals are in W, then any voter in S has ≥ ℓ reps, contradiction)
  have hcommon_ne : (inst.common_approvals S).Nonempty :=
    Finset.card_pos.mp (Nat.lt_of_lt_of_le (by omega : 0 < ℓ) hS_common)
  -- There exists c ∈ common_approvals S with c ∉ W
  -- (If all were in W, each voter in S would have ≥ ℓ reps)
  have h_exists_outside : ∃ c ∈ inst.common_approvals S, c ∉ W := by
    by_contra h_all_in
    push_neg at h_all_in
    -- h_all_in : common_approvals S ⊆ W
    -- Then any voter in S has ≥ ℓ approved candidates in W
    obtain ⟨i, hi⟩ := hS_ne
    have hinter : (W ∩ inst.approves i).card ≥ ℓ := by
      have h_sub : inst.common_approvals S ⊆ W ∩ inst.approves i := by
        intro c hc
        have hc' := (mem_common_approvals_iff inst S c).mp hc
        exact Finset.mem_inter.mpr ⟨h_all_in c hc, hc'.2 i hi⟩
      exact le_trans hS_common (Finset.card_le_card h_sub)
    exact Nat.lt_irrefl ℓ (Nat.lt_of_le_of_lt hinter (h_no_reps i hi))
  obtain ⟨c, hc_common, hc_not_in_W⟩ := h_exists_outside
  rw [mem_common_approvals_iff] at hc_common
  obtain ⟨hc_cand, hc_approved⟩ := hc_common
  -- c was not selected in any round
  have hc_not_selected : ∀ t : Fin w.num_rounds, (w.rounds t).selected ≠ c := by
    intro t habs
    apply hc_not_in_W
    rw [← hw]
    unfold MESWitness.committee
    rw [← habs]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
  -- Case split: ℓ = 1 vs ℓ ≥ 2
  rcases Nat.eq_or_lt_of_le hℓ_pos with hℓ_eq | hℓ_ge2
  · -- Case ℓ = 1: All voters in S have 0 representatives, so full budget = 1 ≥ 1/ℓ
    subst hℓ_eq
    have h_budget_one : ∀ i ∈ S, w.final_budgets i = 1 := fun i hi =>
      budget_eq_one_of_no_reps w i (hS_voters hi) (Nat.eq_zero_of_le_zero (h_utility i hi))
    have h_supporter_budget : inst.supporter_budget w.final_budgets c ≥ inst.price :=
      supporter_budget_ge_price_of_cohesive S c 1 w.final_budgets (by omega) hS_voters hS_large
        hc_approved
        (fun i hi _ => final_budget_nonneg w i ((Finset.mem_filter.mp hi).1))
        (fun i hi => by simp [h_budget_one i hi])
    linarith [w.termination c hc_cand hc_not_selected]
  · -- Case ℓ ≥ 2: Use the paper's argument
    -- The key insight is: either all voters in S maintained budget ≥ 1/ℓ throughout,
    -- or at some point someone paid > 1/ℓ for a candidate.
    -- In the first case, c is (1/ℓ)-affordable at termination.
    -- In the second case, at the moment of first "overpayment", a better candidate existed.

    have hℓ2 : 2 ≤ ℓ := hℓ_ge2

    -- Key claim: if all payments in S were ≤ 1/ℓ, then all voters in S have budget ≥ 1/ℓ
    -- at termination, making c (1/ℓ)-affordable, contradicting termination.

    -- First, show that if all ρ-values for candidates selected where S voters paid were ≤ 1/ℓ,
    -- then by budget_lower_bound, all voters in S have final budget ≥ 1/ℓ.

    -- Case analysis: either all payments by S voters were ≤ 1/ℓ, or some payment was > 1/ℓ
    by_cases h_all_small : ∀ t : Fin w.num_rounds, ∀ i ∈ S,
        (w.rounds t).selected ∈ inst.approves i → (w.rounds t).selected_rho ≤ 1 / ℓ
    · -- All payments ≤ 1/ℓ: Each voter in S has budget ≥ 1/ℓ at termination
      have h_budget_ge : ∀ i ∈ S, w.final_budgets i ≥ 1 / ℓ := fun i hi =>
        budget_lower_bound w i (hS_voters hi) ℓ hℓ2 (h_utility i hi) (h_all_small · i hi)
      have h_supporter_budget : inst.supporter_budget w.final_budgets c ≥ inst.price :=
        supporter_budget_ge_price_of_cohesive S c ℓ w.final_budgets hℓ_pos hS_voters hS_large
          hc_approved
          (fun i hi _ => final_budget_nonneg w i ((Finset.mem_filter.mp hi).1))
          h_budget_ge
      linarith [w.termination c hc_cand hc_not_selected]

    · -- Some payment was > 1/ℓ
      -- This is the more complex case from the paper
      push_neg at h_all_small
      -- There exists t, i ∈ S such that i approved selected[t] and ρ[t] > 1/ℓ
      obtain ⟨t₀, i₀, hi₀_S, hi₀_approved, hρ_large⟩ := h_all_small

      -- Step 1: Find the FIRST round where some voter in S paid > 1/ℓ
      -- Define the set of "bad" rounds
      let bad_rounds := Finset.univ.filter (fun t : Fin w.num_rounds =>
        ∃ i ∈ S, (w.rounds t).selected ∈ inst.approves i ∧
                 (w.rounds t).selected_rho > 1 / ℓ)

      have h_bad_nonempty : bad_rounds.Nonempty := by
        use t₀
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, bad_rounds]
        exact ⟨i₀, hi₀_S, hi₀_approved, hρ_large⟩

      -- Get the first bad round
      let t_star := bad_rounds.min' h_bad_nonempty

      have ht_star_bad : t_star ∈ bad_rounds := Finset.min'_mem bad_rounds h_bad_nonempty
      have ht_star_min : ∀ t ∈ bad_rounds, t_star ≤ t := fun t ht => Finset.min'_le bad_rounds t ht

      -- Extract witness from t_star being bad
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, bad_rounds] at ht_star_bad
      obtain ⟨i_star, hi_star_S, hi_star_approved, hρ_star_large⟩ := ht_star_bad

      -- Step 2: At round t_star, c was still available (not in already_selected)
      have hc_available : c ∉ (w.rounds t_star).already_selected := by
        -- c is never selected, so c ∉ already_selected at any round
        intro hc_in
        rw [mem_already_selected_iff inst w t_star c] at hc_in
        obtain ⟨s, _, hs_eq⟩ := hc_in
        exact hc_not_selected s hs_eq

      -- Step 3: Before round t_star, all payments by S voters were ≤ 1/ℓ
      have h_prior_small : ∀ t : Fin w.num_rounds, t.val < t_star.val →
          ∀ i ∈ S, (w.rounds t).selected ∈ inst.approves i →
          (w.rounds t).selected_rho ≤ 1 / ℓ := by
        intro t ht_lt i hi happroves
        by_contra h_large
        push_neg at h_large
        -- Then t would be a bad round, contradicting minimality of t_star
        have ht_bad : t ∈ bad_rounds := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, bad_rounds]
          exact ⟨i, hi, happroves, h_large⟩
        have : t_star ≤ t := ht_star_min t ht_bad
        omega

      -- Step 4: At start of round t_star, all voters in S have budget ≥ 1/ℓ
      -- Because they paid ≤ 1/ℓ for each of their ≤ (ℓ-1) representatives so far
      have h_budget_at_tstar : ∀ i ∈ S, (w.rounds t_star).start_budgets i ≥ 1 / ℓ := by
        intro i hi
        have hi_voter := hS_voters hi
        -- All ρ values before t_star for rounds where i paid were ≤ 1/ℓ
        have h_rho_bound : ∀ s : Fin w.num_rounds, s.val < t_star.val →
            (w.rounds s).selected ∈ inst.approves i → (w.rounds s).selected_rho ≤ 1 / ℓ :=
          fun s hs_lt hs_app => h_prior_small s hs_lt i hi hs_app
        have hℓ_pos' : (0 : ℚ) ≤ 1 / ℓ := by positivity
        -- Use start_budget_lower_bound: budget ≥ 1 - utility_before * (1/ℓ)
        have hbound := start_budget_lower_bound w i hi_voter t_star (1 / ℓ) hℓ_pos' h_rho_bound
        -- utility_before ≤ paying_rounds.card = voter_utility ≤ ℓ - 1
        have h_util_before_le : utility_before w i t_star ≤ voter_utility w i := by
          unfold utility_before paying_rounds_before
          rw [← paying_rounds_card_eq_utility w i]
          apply Finset.card_le_card
          exact paying_rounds_before_subset w i t_star
        have h_util_bound : (utility_before w i t_star : ℚ) ≤ (ℓ - 1 : ℕ) := by
          have h1 : (utility_before w i t_star : ℚ) ≤ voter_utility w i := by
            exact_mod_cast h_util_before_le
          calc (utility_before w i t_star : ℚ) ≤ voter_utility w i := h1
            _ ≤ (ℓ - 1 : ℕ) := by exact_mod_cast h_utility i hi
        -- 1 - utility_before * (1/ℓ) ≥ 1 - (ℓ-1) * (1/ℓ) = 1/ℓ
        have hℓ_pos'' : (ℓ : ℚ) > 0 := by positivity
        calc (w.rounds t_star).start_budgets i ≥ 1 - (utility_before w i t_star : ℚ) * (1 / ℓ) := hbound
          _ ≥ 1 - (ℓ - 1 : ℕ) * (1 / ℓ) := by
              have : (utility_before w i t_star : ℚ) * (1 / ℓ) ≤ (ℓ - 1 : ℕ) * (1 / ℓ) := by
                apply mul_le_mul_of_nonneg_right h_util_bound
                positivity
              linarith
          _ = 1 / ℓ := by
              have hsub : ((ℓ - 1 : ℕ) : ℚ) = (ℓ : ℚ) - 1 := by
                rw [Nat.cast_sub (by omega : 1 ≤ ℓ)]
                simp
              rw [hsub]
              field_simp
              ring

      -- Step 5: c is (1/ℓ)-affordable at round t_star
      -- i.e., ∑_{i ∈ supporters c} min(1/ℓ, budget_i) ≥ price
      have hc_affordable : (w.rounds t_star).rho c ≠ ⊤ ∧
          ∃ ρ_c : ℚ, (w.rounds t_star).rho c = ↑ρ_c ∧ ρ_c ≤ 1 / ℓ := by
        have hS_sub_supporters : S ⊆ inst.supporters c := by
          intro i hi
          exact Finset.mem_filter.mpr ⟨hS_voters hi, hc_approved i hi⟩
        have h_supp_budget : inst.supporter_budget (w.rounds t_star).start_budgets c ≥ inst.price :=
          supporter_budget_ge_price_of_cohesive S c ℓ _ hℓ_pos hS_voters hS_large hc_approved
            (fun i hi _ => start_budget_nonneg w i ((Finset.mem_filter.mp hi).1) t_star)
            h_budget_at_tstar
        -- c is affordable (rho ≠ ⊤) since supporter_budget ≥ price
        have hc_affordable' : (w.rounds t_star).rho c ≠ ⊤ := by
          intro habs
          have := ((w.rounds t_star).rho_infinite_iff c hc_cand).mp habs
          linarith
        refine ⟨hc_affordable', ?_⟩
        -- Get the actual ρ value and show it's ≤ 1/ℓ
        obtain ⟨ρ_c, h⟩ := WithTop.ne_top_iff_exists.mp hc_affordable'
        refine ⟨ρ_c, h.symm, ?_⟩
        -- Show ρ_c ≤ 1/ℓ by contradiction: if ρ_c > 1/ℓ, sum exceeds price
        by_contra h_rho_big
        push_neg at h_rho_big
        have h_eq := (w.rounds t_star).rho_equality c hc_cand ρ_c h.symm
        -- For i ∈ S: budget ≥ 1/ℓ, so min(ρ_c, budget) ≥ 1/ℓ
        have h_min_ge : ∀ i ∈ S, min ρ_c ((w.rounds t_star).start_budgets i) ≥ 1 / ℓ := by
          intro i hi
          calc min ρ_c ((w.rounds t_star).start_budgets i)
              ≥ min (1 / (ℓ : ℚ)) ((w.rounds t_star).start_budgets i) :=
                min_le_min_right _ (le_of_lt h_rho_big)
            _ = 1 / ℓ := min_eq_left (h_budget_at_tstar i hi)
        have h_nonneg' : ∀ i ∈ inst.supporters c, i ∉ S →
            0 ≤ min ρ_c ((w.rounds t_star).start_budgets i) := fun i hi _ =>
          le_min (by linarith [h_rho_big, (by positivity : (1 : ℚ) / ℓ > 0)])
            (start_budget_nonneg w i ((Finset.mem_filter.mp hi).1) t_star)
        -- Get witness: some supporter has budget ≥ ρ_c, contributing strictly more than 1/ℓ
        obtain ⟨i_w, hi_w_supp, hi_w_budget⟩ := (w.rounds t_star).rho_witness c hc_cand ρ_c h.symm
        have h_iw_contrib : min ρ_c ((w.rounds t_star).start_budgets i_w) = ρ_c :=
          min_eq_left hi_w_budget
        -- The sum strictly exceeds S.card/ℓ ≥ price, contradicting rho_equality
        have h_sum_strict : ∑ i ∈ inst.supporters c,
            min ρ_c ((w.rounds t_star).start_budgets i) > inst.price := by
          have h_Scard_ge : S.card * (1 / ℓ : ℚ) ≥ inst.price := l_large_card_ge_price S ℓ hℓ_pos hS_large
          by_cases hi_w_S : i_w ∈ S
          · -- Witness in S: contributes ρ_c > 1/ℓ, giving strict inequality
            calc ∑ i ∈ inst.supporters c, min ρ_c ((w.rounds t_star).start_budgets i)
                ≥ ∑ i ∈ S, min ρ_c ((w.rounds t_star).start_budgets i) :=
                  Finset.sum_le_sum_of_subset_of_nonneg hS_sub_supporters h_nonneg'
              _ > ∑ _ ∈ S, (1 / ℓ : ℚ) :=
                  Finset.sum_lt_sum h_min_ge ⟨i_w, hi_w_S, by rw [h_iw_contrib]; exact h_rho_big⟩
              _ = S.card * (1 / ℓ) := by simp [Finset.sum_const, nsmul_eq_mul]
              _ ≥ inst.price := h_Scard_ge
          · -- Witness outside S: S contributes ≥ S.card/ℓ, witness adds positive amount
            have h_iw_pos : min ρ_c ((w.rounds t_star).start_budgets i_w) > 0 := by
              rw [h_iw_contrib]; linarith [h_rho_big, (by positivity : (1 : ℚ) / ℓ > 0)]
            have h_S_sum : ∑ i ∈ S, min ρ_c ((w.rounds t_star).start_budgets i) ≥
                S.card * (1 / ℓ : ℚ) := by
              calc ∑ i ∈ S, min ρ_c ((w.rounds t_star).start_budgets i)
                  ≥ ∑ _ ∈ S, (1 / ℓ : ℚ) := Finset.sum_le_sum h_min_ge
                _ = S.card * (1 / ℓ) := by simp [Finset.sum_const, nsmul_eq_mul]
            have h_rest_pos : ∑ i ∈ inst.supporters c \ S,
                min ρ_c ((w.rounds t_star).start_budgets i) > 0 :=
              Finset.sum_pos' (fun i hi => h_nonneg' i (Finset.mem_sdiff.mp hi).1
                (Finset.mem_sdiff.mp hi).2) ⟨i_w, Finset.mem_sdiff.mpr ⟨hi_w_supp, hi_w_S⟩, h_iw_pos⟩
            have h_union_subset : S ∪ (inst.supporters c \ S) ⊆ inst.supporters c := by
              intro x hx
              rcases Finset.mem_union.mp hx with hxS | hxR
              · exact hS_sub_supporters hxS
              · exact (Finset.mem_sdiff.mp hxR).1
            calc ∑ i ∈ inst.supporters c, min ρ_c ((w.rounds t_star).start_budgets i)
                ≥ ∑ i ∈ S, min ρ_c ((w.rounds t_star).start_budgets i) +
                  ∑ i ∈ inst.supporters c \ S, min ρ_c ((w.rounds t_star).start_budgets i) := by
                    rw [← Finset.sum_union Finset.disjoint_sdiff]
                    exact Finset.sum_le_sum_of_subset_of_nonneg h_union_subset
                      (fun i hi hiU => h_nonneg' i hi (fun hiS => hiU (Finset.mem_union_left _ hiS)))
              _ > S.card * (1 / ℓ : ℚ) + 0 := by linarith
              _ = S.card * (1 / ℓ : ℚ) := by ring
              _ ≥ inst.price := h_Scard_ge
        linarith

      -- Step 6: Contradiction via selected_minimal
      -- selected[t_star] has ρ > 1/ℓ, but c is available with ρ ≤ 1/ℓ
      obtain ⟨_, ρ_c, hρ_c_eq, hρ_c_le⟩ := hc_affordable
      have h_minimal := (w.rounds t_star).selected_minimal c
        (Finset.mem_sdiff.mpr ⟨hc_cand, hc_available⟩)
      -- selected_minimal says: rho(selected) ≤ rho(c)
      -- But rho(selected) = selected_rho > 1/ℓ ≥ ρ_c = rho(c)
      have h_sel_rho := (w.rounds t_star).selected_has_rho
      rw [h_sel_rho, hρ_c_eq] at h_minimal
      simp only [WithTop.coe_le_coe] at h_minimal
      linarith

end ABCInstance
