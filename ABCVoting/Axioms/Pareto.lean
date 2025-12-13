import ABCVoting.Basic

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- PARETO OPTIMALITY
-- ============================================================================

/--
Pareto dominance: Committee W' Pareto dominates W if:
1. Every voter is weakly better off under W' (has utility ≥ utility under W)
2. At least one voter is strictly better off under W'

This is a classic preference relation in social choice theory.
-/
def pareto_dominates (inst : ABCInstance V C k) (W' W : Finset C) : Prop :=
  (∀ i ∈ inst.voters, inst.utility W' i ≥ inst.utility W i) ∧
  (∃ i ∈ inst.voters, inst.utility W' i > inst.utility W i)

/--
Pareto optimality (for committees of size k): A committee W is Pareto optimal if:
1. W has size k
2. No other committee of size k Pareto dominates W

This means we cannot improve at least one voter's utility without harming another.
-/
def is_pareto_optimal (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  W ⊆ inst.candidates ∧ W.card = k ∧
  ∀ W' ⊆ inst.candidates, W'.card = k → ¬inst.pareto_dominates W' W

end ABCInstance
