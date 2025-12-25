/-
# MES Algorithm Implementation

This file provides a computable implementation of the Method of Equal Shares (MES)
algorithm, complementing the witness-based definition in Defs.lean.

The main purpose is to enable verification of concrete examples via `decide`,
making counterexamples (e.g., "MES fails property X") easy to state and check.

## Main Definitions
- `compute_rho`: Compute the ρ-value for a candidate given current budgets
- `mes_step`: Execute one round of MES
- `mes_algorithm`: The full MES algorithm returning a committee

## References
- Peters et al., "Proportional Participatory Budgeting with Additive Utilities"
-/

import ABCVoting.Rules.MES.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] [LinearOrder V] [LinearOrder C] {k : ℕ}

-- ============================================================================
-- COMPUTING ρ FOR A SINGLE CANDIDATE
-- ============================================================================

/--
Get a sorted list of supporters (sorted by voter ID, which gives a canonical order).
-/
def supporters_list (inst : ABCInstance V C k) (c : C) : List V :=
  (inst.supporters c).sort (· ≤ ·)

/--
Sort supporters by their budget in increasing order.
Returns a list of budgets sorted in increasing order.
-/
def sorted_budgets (inst : ABCInstance V C k) (budgets : V → ℚ) (c : C) : List ℚ :=
  let voters := supporters_list inst c
  let voter_budgets := voters.map budgets
  voter_budgets.mergeSort (· ≤ ·)

/--
Given a sorted list of budgets and a target sum (price), compute ρ.

The algorithm finds the breakpoint j where:
- The first j voters pay their full budget
- The remaining (n-j) voters each pay ρ
- Total equals price

Returns `none` if the candidate is unaffordable (total budget < price).
-/
def compute_rho_from_sorted (sorted_budgets : List ℚ) (price : ℚ) : Option ℚ :=
  let n := sorted_budgets.length
  if n = 0 then none
  else
    -- Compute prefix sums: prefix_sum[j] = sum of first j budgets
    let prefix_sums := sorted_budgets.scanl (· + ·) 0
    -- Try each breakpoint j from 0 to n
    -- At breakpoint j: first j pay full budget, remaining (n-j) pay ρ
    -- ρ = (price - prefix_sum[j]) / (n - j)
    let find_rho := fun (j : ℕ) =>
      if h : j < prefix_sums.length ∧ j ≤ n then
        let remaining := n - j
        if remaining = 0 then none
        else
          let psum := prefix_sums.get ⟨j, h.1⟩
          let rho := (price - psum) / remaining
          -- Check validity: ρ must be ≤ budget of voter j (if j < n)
          -- and ≥ budget of voter j-1 (if j > 0)
          let valid_upper : Bool := j == n ||
            (match sorted_budgets[j]? with
             | some b => decide (rho ≤ b)
             | none => true)
          let valid_lower : Bool := j == 0 ||
            (match sorted_budgets[j - 1]? with
             | some b => decide (b ≤ rho)
             | none => true)
          if valid_upper && valid_lower && decide (0 ≤ rho) then some rho else none
      else none
    -- Find the first valid breakpoint
    (List.range (n + 1)).findSome? find_rho

/--
Compute the ρ-value for a candidate.

Returns `⊤` (infinity) if the candidate is unaffordable,
otherwise returns the minimal ρ such that Σ min(ρ, bᵢ) = price.
-/
def compute_rho (inst : ABCInstance V C k) (budgets : V → ℚ) (c : C) : RhoValue :=
  let sbudgets := sorted_budgets inst budgets c
  match compute_rho_from_sorted sbudgets inst.price with
  | some ρ => ↑ρ
  | none => ⊤

-- ============================================================================
-- MES ALGORITHM STATE
-- ============================================================================

/--
State of the MES algorithm during execution.
-/
structure MESState (V C : Type*) [DecidableEq V] [DecidableEq C] (k : ℕ)
    (inst : ABCInstance V C k) where
  /-- Current budgets for each voter -/
  budgets : V → ℚ
  /-- Candidates selected so far -/
  selected : Finset C
  /-- Number of rounds remaining -/
  rounds_remaining : ℕ

/--
Initial state: all voters have budget 1, no candidates selected.
-/
def mes_initial_state (inst : ABCInstance V C k) (max_rounds : ℕ) : MESState V C k inst where
  budgets := fun _ => 1
  selected := ∅
  rounds_remaining := max_rounds

-- ============================================================================
-- SINGLE MES STEP
-- ============================================================================

/--
Find the candidate with minimal ρ-value among those not yet selected.
Returns `none` if no candidate is affordable.
-/
def mes_find_best_candidate (inst : ABCInstance V C k) (budgets : V → ℚ)
    (already_selected : Finset C) : Option (C × ℚ) :=
  let available := (inst.candidates \ already_selected).sort (· ≤ ·)
  -- Compute ρ for each available candidate
  let candidates_with_rho := available.filterMap fun c =>
    match compute_rho inst budgets c with
    | ⊤ => none
    | (some ρ) => some (c, ρ)
  -- Find the one with minimal ρ (using foldl to find minimum)
  match candidates_with_rho with
  | [] => none
  | (c, ρ) :: rest =>
    some <| rest.foldl (fun (best : C × ℚ) (cur : C × ℚ) =>
      if cur.2 < best.2 then cur else best) (c, ρ)

/--
Update budgets after selecting a candidate.
Each supporter pays min(ρ, their_budget).
-/
def update_budgets (inst : ABCInstance V C k) (budgets : V → ℚ) (c : C) (ρ : ℚ) : V → ℚ :=
  fun v =>
    if c ∈ inst.approves v then
      budgets v - min ρ (budgets v)
    else
      budgets v

/--
Execute one step of MES.
Returns the updated state, or the same state if no candidate is affordable.
-/
def mes_step (inst : ABCInstance V C k) (state : MESState V C k inst) : MESState V C k inst :=
  if state.rounds_remaining = 0 then state
  else
    match mes_find_best_candidate inst state.budgets state.selected with
    | none => { state with rounds_remaining := 0 }  -- No affordable candidate, terminate
    | some (c, ρ) =>
      { budgets := update_budgets inst state.budgets c ρ
        selected := state.selected ∪ {c}
        rounds_remaining := state.rounds_remaining - 1 }

-- ============================================================================
-- FULL MES ALGORITHM
-- ============================================================================

/--
Run MES for a fixed number of iterations.
-/
def mes_loop (inst : ABCInstance V C k) (state : MESState V C k inst) : Finset C :=
  if h : state.rounds_remaining = 0 then state.selected
  else
    let new_state := mes_step inst state
    if new_state.rounds_remaining = state.rounds_remaining then
      -- No progress made (no affordable candidate)
      state.selected
    else
      have : new_state.rounds_remaining < state.rounds_remaining := by
        simp only [new_state, mes_step, h, ↓reduceIte]
        split
        · exact Nat.pos_of_ne_zero h
        · simp only []; omega
      mes_loop inst new_state
termination_by state.rounds_remaining

/--
The MES algorithm: returns the committee selected by MES.

This runs MES starting with all voters having budget 1, selecting candidates
until either k candidates are selected or no candidate is affordable.
-/
def mes_algorithm (inst : ABCInstance V C k) : Finset C :=
  mes_loop inst (mes_initial_state inst k)

-- ============================================================================
-- ALTERNATIVE: LIST-BASED OUTPUT (for ordered results)
-- ============================================================================

/--
Run MES and return the selection order as a list.
-/
def mes_loop_list (inst : ABCInstance V C k) (state : MESState V C k inst)
    (acc : List C) : List C :=
  if h : state.rounds_remaining = 0 then acc.reverse
  else
    match mes_find_best_candidate inst state.budgets state.selected with
    | none => acc.reverse
    | some (c, ρ) =>
      let new_state : MESState V C k inst :=
        { budgets := update_budgets inst state.budgets c ρ
          selected := state.selected ∪ {c}
          rounds_remaining := state.rounds_remaining - 1 }
      have : new_state.rounds_remaining < state.rounds_remaining := by
        simp [new_state]
        omega
      mes_loop_list inst new_state (c :: acc)
termination_by state.rounds_remaining

/--
The MES algorithm returning the selection order.
-/
def mes_algorithm_list (inst : ABCInstance V C k) : List C :=
  mes_loop_list inst (mes_initial_state inst k) []

-- ============================================================================
-- BASIC PROPERTIES (for connecting to witness definition)
-- ============================================================================

/--
The committee returned by mes_algorithm is a subset of candidates.
-/
theorem mes_algorithm_subset (inst : ABCInstance V C k) :
    mes_algorithm inst ⊆ inst.candidates := by
  sorry  -- TODO: prove this

/--
The committee returned by mes_algorithm has size at most k.
-/
theorem mes_algorithm_card_le (inst : ABCInstance V C k) :
    (mes_algorithm inst).card ≤ k := by
  sorry  -- TODO: prove this

end ABCInstance

-- ============================================================================
-- TEST EXAMPLE
-- ============================================================================

namespace MESTest

open ABCInstance Finset

/-- Test instance: 3 voters, 5 candidates, k = 3
- Voter 0 approves {0, 1, 2}
- Voter 1 approves {0, 1, 2}
- Voter 2 approves {3, 4}
Expected: MES selects something like {0, 1, 3} or {0, 1, 4}
-/

abbrev V := Fin 3
abbrev C := Fin 5

def test_approves : V → Finset C
  | ⟨0, _⟩ => {0, 1, 2}
  | ⟨1, _⟩ => {0, 1, 2}
  | ⟨2, _⟩ => {3, 4}

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

-- First, let's see what the algorithm produces using #eval
#eval mes_algorithm_list test_inst

-- Test with native_decide (works but discouraged in Mathlib)
-- For Mathlib-compatible proofs, we'd need to construct MESWitness manually
-- or prove the equivalence theorem and transfer via that
set_option linter.style.nativeDecide false in
example : mes_algorithm test_inst = {0, 1, 3} := by native_decide

-- Verify the algorithm step by step:
-- price = n/k = 3/3 = 1
-- Round 1: candidates 0,1,2 have ρ=1/2 (2 supporters), candidates 3,4 have ρ=1 (1 supporter)
--          Select candidate 0 (first by tie-breaking), each supporter pays 1/2
-- Round 2: candidates 1,2 still have ρ=1/2, select candidate 1
-- Round 3: candidate 2 has ρ=1 (supporters have 0 budget), candidates 3,4 have ρ=1
--          Select candidate 3 (first available with ρ=1)
#eval mes_algorithm_list test_inst  -- [0, 1, 3]

end MESTest
