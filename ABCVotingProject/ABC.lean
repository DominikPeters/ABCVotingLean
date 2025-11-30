import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold -- For Finset.inf (bounded intersection)
import Mathlib.Data.Fintype.Lattice -- For Finset.mem_inf
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset BigOperators

-- 1. THE SETUP
-- We bundle the Context into a structure.
-- This guarantees k is valid and ties the profile to the voters.
structure ABCInstance (V C : Type*) [DecidableEq V] [DecidableEq C] where
  voters : Finset V
  candidates : Finset C
  approves : V → Finset C
  approves_subset : ∀ v ∈ voters, approves v ⊆ candidates
  voters_nonempty : voters.Nonempty
  k : ℕ
  k_pos : 0 < k
  k_le_m : k ≤ candidates.card

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C]

-- 2. PAV FORMALIZATION

-- Harmonic number: 1 + 1/2 + ... + 1/n
def harmonic (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (1 : ℚ) / (i + 1)

-- The PAV score for a specific committee W
def pav_score (inst : ABCInstance V C) (W : Finset C) : ℚ :=
  ∑ i ∈ inst.voters, harmonic (W ∩ inst.approves i).card

-- Definition of a winner: A committee W is a winner if it has size k
-- and maximizes the score.
def is_pav_winner (inst : ABCInstance V C) (W : Finset C) : Prop :=
  W.card = inst.k ∧
  ∀ W' : Finset C, W'.card = inst.k → inst.pav_score W' ≤ inst.pav_score W

-- 3. EJR FORMALIZATION

-- Helper: The set of candidates approved by ALL voters in group S
def common_approvals (inst : ABCInstance V C) (S : Finset V) : Finset C :=
  inst.candidates.filter fun c => ∀ v ∈ S, c ∈ inst.approves v

-- A group S is l-large if |S| >= l * n / k (equivalently, l * n <= |S| * k)
def is_l_large (inst : ABCInstance V C) (S : Finset V) (l : ℕ) : Prop :=
  l * inst.voters.card ≤ S.card * inst.k

-- A group S is l-cohesive if they are large enough AND agree on enough candidates.
def is_l_cohesive (inst : ABCInstance V C) (S : Finset V) (l : ℕ) : Prop :=
  inst.is_l_large S l ∧
  (inst.common_approvals S).card ≥ l

-- Axiom EJR: A committee W satisfies EJR if for every l-cohesive group S,
-- there is at least one voter in S who approves at least l candidates in W.
def is_ejr (inst : ABCInstance V C) (W : Finset C) : Prop :=
  W.card = inst.k ∧
  ∀ (S : Finset V) (l : ℕ),
    S ⊆ inst.voters →
    l ≥ 1 →
    inst.is_l_cohesive S l →
    ∃ i ∈ S, (W ∩ inst.approves i).card ≥ l

-- Axiom EJR+: A committee W satisfies EJR+ if for every l-large group S
-- who all approve some candidate c not in W,
-- there is at least one voter in S who approves at least l candidates in W.
def is_ejr_plus (inst : ABCInstance V C) (W : Finset C) : Prop :=
  W.card = inst.k ∧
  ∀ (S : Finset V) (l : ℕ),
    S ⊆ inst.voters →
    l ≥ 1 →
    inst.is_l_large S l ∧
    (∃ c ∈ inst.candidates \ W, ∀ i ∈ S, c ∈ inst.approves i) →
    ∃ i ∈ S, (W ∩ inst.approves i).card ≥ l

-- 4. HELPER LEMMAS

-- If a group is l-large with l >= 1, then it must be nonempty
lemma l_large_nonempty (inst : ABCInstance V C) (S : Finset V) (l : ℕ)
    (hl : l ≥ 1) (h_large : inst.is_l_large S l) : S.Nonempty := by
  unfold is_l_large at h_large
  have h_voters_pos : 0 < inst.voters.card := Finset.card_pos.mpr inst.voters_nonempty
  have h_lhs_pos : 0 < l * inst.voters.card := Nat.mul_pos hl h_voters_pos
  have h_rhs_pos : 0 < S.card * inst.k := lt_of_lt_of_le h_lhs_pos h_large
  exact Finset.card_pos.mp (Nat.pos_of_mul_pos_right h_rhs_pos)

-- Helper lemma: characterize membership in common_approvals
lemma mem_common_approvals_iff (inst : ABCInstance V C) (S : Finset V) (c : C) :
    c ∈ inst.common_approvals S ↔ c ∈ inst.candidates ∧ ∀ v ∈ S, c ∈ inst.approves v := by
  simp [common_approvals, Finset.mem_filter]

-- 5. THEOREM: EJR+ implies EJR

theorem ejr_plus_implies_ejr (inst : ABCInstance V C) (W : Finset C) :
    inst.is_ejr_plus W → inst.is_ejr W := by
  intro ⟨h_card, h_ejr_plus⟩
  refine ⟨h_card, ?_⟩
  intro S l h_S_subset hl_pos ⟨h_large, h_common⟩
  -- We'll prove this by contradiction
  by_contra h_not
  push_neg at h_not
  -- h_not says: for all i in S, utility of i is < l
  -- Since everyone in S has utility < l, and they have l common approvals,
  -- at least one common approval must not be in W
  -- S is l-large with l >= 1, so it's nonempty
  have h_S_nonempty := l_large_nonempty inst S l hl_pos h_large
  -- Key insight: if everyone has < l in W, but there are ≥ l common approvals,
  -- some common approval must be outside W
  have h_exists_missing : ∃ c ∈ inst.common_approvals S, c ∉ W := by
    by_contra h_all_in
    push_neg at h_all_in
    obtain ⟨i, hi_mem⟩ := h_S_nonempty
    have h_common_subset : inst.common_approvals S ⊆ W ∩ inst.approves i := by
      intro c hc
      simp only [Finset.mem_inter]
      exact ⟨h_all_in c hc, (mem_common_approvals_iff inst S c).mp hc |>.2 i hi_mem⟩
    have : (W ∩ inst.approves i).card ≥ l :=
      h_common.trans (Finset.card_le_card h_common_subset)
    exact Nat.not_lt.mpr this (h_not i hi_mem)
  -- Now we have c ∈ common_approvals S but c ∉ W
  obtain ⟨c, hc_common, hc_not_in_W⟩ := h_exists_missing
  -- c is approved by all voters in S
  have hc_approved : ∀ j ∈ S, c ∈ inst.approves j :=
    (mem_common_approvals_iff inst S c).mp hc_common |>.2
  -- Now apply EJR+ with S, l, and c
  have hc_witness : c ∈ inst.candidates \ W := by
    simp only [Finset.mem_sdiff]
    exact ⟨(mem_common_approvals_iff inst S c).mp hc_common |>.1, hc_not_in_W⟩
  obtain ⟨i, hi_mem, hi_utility⟩ :=
    h_ejr_plus S l h_S_subset hl_pos ⟨h_large, c, hc_witness, hc_approved⟩
  -- This gives us some i in S with utility >= l, but h_not says all i in S have utility < l
  exact Nat.not_lt.mpr hi_utility (h_not i hi_mem)

end ABCInstance
