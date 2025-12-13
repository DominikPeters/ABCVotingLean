import ABCVoting.Basic

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- THE CORE
-- ============================================================================

/--
The Core: A committee W is in the core if no coalition can block it by proposing
an alternative. Specifically, for every ℓ-large group S and every set of candidates
T with |T| ≤ ℓ, there must be some voter in S who weakly prefers W to T.

This means no coalition S can unanimously agree that some alternative T
(that they could "afford" given their size) is strictly better for all of them.

Formally: For all S, T with |S| ≥ ℓn/k and |T| ≤ ℓ, there exists i ∈ S such that
u_i(W) ≥ u_i(T).

Note: We do not require W.card = k.
-/
def is_in_core (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∀ (S : Finset V) (T : Finset C) (l : ℕ),
    S ⊆ inst.voters →
    T ⊆ inst.candidates →
    l ≥ 1 →
    inst.is_l_large S l ∧ T.card ≤ l →
    ∃ i ∈ S, (W ∩ inst.approves i).card ≥ (T ∩ inst.approves i).card

/--
Disjoint Core: A weaker version of the core where the blocking coalition can only
propose alternatives T that are disjoint from the current committee W.

This captures the idea that a coalition can only block by proposing candidates
that are not already in the committee.
-/
def is_in_disjoint_core (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∀ (S : Finset V) (T : Finset C) (l : ℕ),
    S ⊆ inst.voters →
    T ⊆ inst.candidates →
    Disjoint W T →
    l ≥ 1 →
    inst.is_l_large S l ∧ T.card ≤ l →
    ∃ i ∈ S, (W ∩ inst.approves i).card ≥ (T ∩ inst.approves i).card

end ABCInstance
