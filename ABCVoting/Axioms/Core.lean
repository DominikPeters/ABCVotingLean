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

/--
Sub-core: A committee W lies in the sub-core if no coalition can deviate to a committee
where every member strictly improves (i.e., their approved candidates in the new committee
form a proper superset of their approved candidates in the original committee).

Formally: For all nonempty S ⊆ V and T ⊆ C with |T| ≤ |S|·k/n, there exists i ∈ S such that
it is NOT the case that (W ∩ A_i) ⊊ (T ∩ A_i).

This is weaker than the core: any committee in the core is also in the sub-core.

Reference: "Auditing for Core Stability in Participatory Budgeting"
by Munagala, Shen, Wang (WINE 2022)
-/
def is_in_sub_core (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∀ (S : Finset V) (T : Finset C),
    S ⊆ inst.voters →
    T ⊆ inst.candidates →
    S.Nonempty →
    T.card * inst.voters.card ≤ S.card * k →
    ∃ i ∈ S, ¬((W ∩ inst.approves i) ⊂ (T ∩ inst.approves i))

end ABCInstance
