import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

open Finset BigOperators

-- ============================================================================
-- THE SETUP
-- ============================================================================

/--
An ABC instance consists of:
- A finite set of voters V
- A finite set of candidates C
- An approval function: each voter approves a subset of candidates
- A target committee size k

The structure guarantees:
- All approvals are within the candidate set
- There is at least one voter
- k is positive and ≤ the number of candidates
-/
structure ABCInstance (V C : Type*) [DecidableEq V] [DecidableEq C] (k : ℕ) where
  voters : Finset V
  candidates : Finset C
  approves : V → Finset C
  approves_subset : ∀ v ∈ voters, approves v ⊆ candidates
  voters_nonempty : voters.Nonempty
  k_pos : 0 < k
  k_le_m : k ≤ candidates.card

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- UTILITY AND BASIC HELPER DEFINITIONS
-- ============================================================================

/--
Utility function: the number of approved candidates in a committee for a voter.
This counts how many candidates in the committee voter i approves.
-/
def utility (inst : ABCInstance V C k) (W : Finset C) (i : V) : ℕ :=
  (W ∩ inst.approves i).card

/--
Supporters of a candidate: the voters who approve that candidate.
-/
def supporters (inst : ABCInstance V C k) (c : C) : Finset V :=
  inst.voters.filter (c ∈ inst.approves ·)

/--
The set of candidates commonly approved by all voters in a group.
-/
def common_approvals (inst : ABCInstance V C k) (S : Finset V) : Finset C :=
  inst.candidates.filter fun c => ∀ v ∈ S, c ∈ inst.approves v

/--
The union of all candidates approved by any voter in a group S.
-/
def union_approvals (inst : ABCInstance V C k) (S : Finset V) : Finset C :=
  S.biUnion inst.approves

/--
A sorted list of candidates (for canonical iteration order).
-/
def candidates_list (inst : ABCInstance V C k) [LinearOrder C] : List C :=
  inst.candidates.sort (· ≤ ·)

/--
A group S is ℓ-large if it contains at least ℓn/k voters.
Formally: ℓ * |voters| ≤ |S| * k
-/
def is_l_large (inst : ABCInstance V C k) (S : Finset V) (l : ℕ) : Prop :=
  l * inst.voters.card ≤ S.card * k

-- ============================================================================
-- HELPER LEMMAS
-- ============================================================================

/--
If a group is ℓ-large with ℓ ≥ 1, then it must be nonempty.
-/
lemma l_large_nonempty (inst : ABCInstance V C k) (S : Finset V) (l : ℕ)
    (hl : l ≥ 1) (h_large : inst.is_l_large S l) : S.Nonempty := by
  unfold is_l_large at h_large
  exact Finset.card_pos.mp <| Nat.pos_of_mul_pos_right <|
    (Nat.mul_pos hl (Finset.card_pos.mpr inst.voters_nonempty)).trans_le h_large

/--
Characterization of membership in common_approvals.
-/
lemma mem_common_approvals_iff (inst : ABCInstance V C k) (S : Finset V) (c : C) :
    c ∈ inst.common_approvals S ↔ c ∈ inst.candidates ∧ ∀ v ∈ S, c ∈ inst.approves v := by
  simp [common_approvals, Finset.mem_filter]

end ABCInstance
