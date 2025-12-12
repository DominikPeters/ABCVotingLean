import ABCVoting.Basic

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- JUSTIFIED REPRESENTATION (JR) AXIOMS
-- ============================================================================

/--
Extended Justified Representation (EJR): A committee W satisfies EJR if for every
ℓ-cohesive group S (a group of voters large enough and with common approved candidates),
there is at least one voter in S who approves at least ℓ candidates in W.

More formally:
- An ℓ-cohesive group S requires:
  1. S is ℓ-large: |S| ≥ ℓn/k
  2. Common approvals: |common_approvals(S)| ≥ ℓ

If both conditions hold, then some voter in S must have utility ≥ ℓ.

Note: We do not require W.card = k; any committee can satisfy EJR, and any completion
of an EJR committee preserves EJR.
-/
def is_ejr (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∀ (S : Finset V) (l : ℕ),
    S ⊆ inst.voters →
    l ≥ 1 →
    inst.is_l_large S l ∧ (inst.common_approvals S).card ≥ l →
    ∃ i ∈ S, (W ∩ inst.approves i).card ≥ l

/--
EJR Plus (EJR+): A stronger variant of EJR. A committee W satisfies EJR+ if for every
ℓ-large group S where all voters agree on some candidate c ∉ W,
there is at least one voter in S who approves at least ℓ candidates in W.

More formally: If S is ℓ-large and there exists c ∈ candidates \ W such that
all voters in S approve c, then some voter in S must have utility ≥ ℓ.

Note: Like EJR, we do not require W.card = k.
-/
def is_ejr_plus (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∀ (S : Finset V) (l : ℕ),
    S ⊆ inst.voters →
    l ≥ 1 →
    inst.is_l_large S l ∧
    (∃ c ∈ inst.candidates \ W, ∀ i ∈ S, c ∈ inst.approves i) →
    ∃ i ∈ S, (W ∩ inst.approves i).card ≥ l

end ABCInstance
