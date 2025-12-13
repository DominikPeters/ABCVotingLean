import ABCVoting.Basic

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- JUSTIFIED REPRESENTATION (JR) AXIOMS
-- ============================================================================

/--
Justified Representation (JR): A committee W satisfies JR if for every
1-cohesive group S (a group of voters of size ≥ n/k with a common approved candidate),
there is at least one voter in S who approves at least 1 candidate in W.

This is the simplest justified representation axiom, essentially EJR with ℓ = 1.

Note: We do not require W.card = k.
-/
def is_jr (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∀ (S : Finset V),
    S ⊆ inst.voters →
    inst.is_l_large S 1 ∧ (inst.common_approvals S).card ≥ 1 →
    ∃ i ∈ S, (W ∩ inst.approves i).card ≥ 1

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
Proportional Justified Representation (PJR): A committee W satisfies PJR if for every
ℓ-cohesive group S, the committee contains at least ℓ candidates approved by the coalition.

The key difference from EJR: instead of requiring some voter to have individual utility ≥ ℓ,
we require the coalition's collective coverage to be ≥ ℓ.

Formally: |W ∩ (⋃_{i∈S} A_i)| ≥ ℓ

Note: PJR is weaker than EJR since max utility ≥ ℓ implies collective coverage ≥ ℓ.
-/
def is_pjr (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∀ (S : Finset V) (l : ℕ),
    S ⊆ inst.voters →
    l ≥ 1 →
    inst.is_l_large S l ∧ (inst.common_approvals S).card ≥ l →
    (W ∩ inst.union_approvals S).card ≥ l

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

/--
PJR Plus (PJR+): A stronger variant of PJR. A committee W satisfies PJR+ if for every
ℓ-large group S where all voters agree on some candidate c ∉ W,
the committee contains at least ℓ candidates approved by the coalition.

More formally: If S is ℓ-large and there exists c ∈ candidates \ W such that
all voters in S approve c, then |W ∩ (⋃_{i∈S} A_i)| ≥ ℓ.

Note: Like PJR, we do not require W.card = k.
-/
def is_pjr_plus (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∀ (S : Finset V) (l : ℕ),
    S ⊆ inst.voters →
    l ≥ 1 →
    inst.is_l_large S l ∧
    (∃ c ∈ inst.candidates \ W, ∀ i ∈ S, c ∈ inst.approves i) →
    (W ∩ inst.union_approvals S).card ≥ l

/--
Fully Justified Representation (FJR): A committee W satisfies FJR if for every
ℓ-large group S and every set of candidates T with |T| ≤ ℓ such that every voter
in S approves at least β candidates from T, there is a voter in S with utility ≥ β.

FJR generalizes EJR by allowing the "witness set" T to be any small set of candidates
(not necessarily commonly approved), and requiring that voters approve β candidates
from T (not necessarily all of T).

Note: We do not require W.card = k.
-/
def is_fjr (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∀ (S : Finset V) (T : Finset C) (l β : ℕ),
    S ⊆ inst.voters →
    T ⊆ inst.candidates →
    l ≥ 1 →
    β ≥ 1 →
    inst.is_l_large S l ∧ T.card ≤ l ∧ (∀ i ∈ S, (inst.approves i ∩ T).card ≥ β) →
    ∃ i ∈ S, (W ∩ inst.approves i).card ≥ β

/--
Fully Proportional Justified Representation (FPJR): A committee W satisfies FPJR if for every
ℓ-large group S and every set of candidates T with |T| ≤ ℓ such that every voter
in S approves at least β candidates from T, the committee covers at least β candidates
from the coalition's union of approvals.

FPJR is to FJR as PJR is to EJR: it relaxes the individual utility requirement to
a collective coverage requirement.

Note: We do not require W.card = k.
-/
def is_fpjr (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∀ (S : Finset V) (T : Finset C) (l β : ℕ),
    S ⊆ inst.voters →
    T ⊆ inst.candidates →
    l ≥ 1 →
    β ≥ 1 →
    inst.is_l_large S l ∧ T.card ≤ l ∧ (∀ i ∈ S, (inst.approves i ∩ T).card ≥ β) →
    (W ∩ inst.union_approvals S).card ≥ β

end ABCInstance
