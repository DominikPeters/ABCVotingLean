import ABCVoting.Basic
import Mathlib.Order.WithBot

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- BASIC DEFINITIONS
-- ============================================================================

/--
ρ-value: either a rational number or ⊤ (representing "unaffordable").
Used to track the cost-sharing ratio for each candidate in MES.
-/
abbrev RhoValue := WithTop ℚ

/--
Price per candidate: n/k, where n is the number of voters and k is the committee size.
This is the total cost that must be covered by supporters of a candidate.
-/
def price (inst : ABCInstance V C k) : ℚ := inst.voters.card / k

/--
Total remaining budget of a candidate's supporters.

Given a budget function (tracking each voter's remaining budget),
this sums the budgets of all voters who support the candidate.
-/
def supporter_budget (inst : ABCInstance V C k) (budgets : V → ℚ) (c : C) : ℚ :=
  ∑ i ∈ inst.supporters c, budgets i

-- ============================================================================
-- MES ROUND STRUCTURE
-- ============================================================================

/--
A single round of MES (Method of Equal Shares) execution.

Each round tracks:
- **Budgets**: The budget each voter has at the start and end of this round
- **ρ-values**: For each candidate, the cost-share ratio needed for affordability (⊤ if unaffordable)
- **already_selected**: The set of candidates selected in previous rounds
- **selected**: The candidate selected in this round (the one with minimal ρ)
- **Properties**: Various constraints ensuring the round is valid and consistent

The round satisfies:
1. The selected candidate is new (not previously selected)
2. ρ values correctly reflect affordability (⊤ iff total budget < price)
3. For affordable candidates, the ρ value solves the equation: ∑ min(ρ, budget_i) = price
4. Budgets evolve correctly: supporters pay min(ρ, budget), others pay nothing
-/
structure MESRound (V C : Type*) [DecidableEq V] [DecidableEq C]
    (inst : ABCInstance V C k) where
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
-- MES WITNESS STRUCTURE
-- ============================================================================

/--
A witness for an MES (Method of Equal Shares) execution.

This captures a complete execution trace of the algorithm, including:
- **Rounds**: All rounds of the algorithm, with budgets, ρ-values, and selections
- **Consistency**: Budgets link correctly between rounds
- **Termination**: When the algorithm stops, all remaining candidates are unaffordable

The witness structure allows us to define what it means for a committee to be
an MES outcome, and to prove properties about MES outcomes without implementing
the algorithm itself.
-/
structure MESWitness (V C : Type*) [DecidableEq V] [DecidableEq C]
    (inst : ABCInstance V C k) where
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
-- MES OUTCOME DEFINITION
-- ============================================================================

variable (inst : ABCInstance V C k) in
/--
The resulting committee from an MES witness.

Extracts the set of selected candidates from all rounds.
-/
def MESWitness.committee (w : MESWitness V C inst) : Finset C :=
  Finset.image (fun t => (w.rounds t).selected) Finset.univ

/--
Definition: A committee W is an MES (Method of Equal Shares) outcome if
there exists a valid witness w such that w.committee = W.

This allows us to reason about MES outcomes without implementing the algorithm.
-/
def is_mes_outcome (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∃ w : MESWitness V C inst, w.committee = W

-- ============================================================================
-- BASIC LEMMAS ABOUT MES ROUNDS
-- ============================================================================

/--
Payment is non-negative: min(ρ, budget) ≥ 0 when both ρ and budget are non-negative.
-/
lemma payment_nonneg (budgets : V → ℚ) (i : V) (ρ : ℚ) (hρ : 0 ≤ ρ) (hb : 0 ≤ budgets i) :
    0 ≤ min ρ (budgets i) := le_min hρ hb

/--
Payment is at most the budget: min(ρ, budget) ≤ budget.
-/
lemma payment_le_budget (budgets : V → ℚ) (i : V) (ρ : ℚ) :
    min ρ (budgets i) ≤ budgets i := min_le_right ρ (budgets i)

/--
Payment is at most ρ: min(ρ, budget) ≤ ρ.
-/
lemma payment_le_rho (budgets : V → ℚ) (i : V) (ρ : ℚ) :
    min ρ (budgets i) ≤ ρ := min_le_left ρ (budgets i)

end ABCInstance
