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
-- We use 'inf'' (infimum/intersection) which requires nonempty S
def common_approvals (inst : ABCInstance V C) (S : Finset V) : Finset C :=
  if h : S.Nonempty then S.inf' h inst.approves else ∅

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
  -- Use Finset.one_le_card: 1 ≤ S.card ↔ S.Nonempty
  rw [← Finset.one_le_card]
  -- h_large says: l * voters.card ≤ S.card * k
  unfold is_l_large at h_large
  -- Since voters is nonempty, voters.card ≥ 1
  have h_voters_card : 1 ≤ inst.voters.card := Finset.one_le_card.mpr inst.voters_nonempty
  -- Since k > 0, if S.card = 0 then S.card * k = 0
  -- But l * voters.card ≥ l * 1 = l ≥ 1, contradiction
  by_contra h_S_empty
  rw [Finset.one_le_card] at h_S_empty
  simp [Finset.not_nonempty_iff_eq_empty] at h_S_empty
  rw [h_S_empty, Finset.card_empty] at h_large
  simp at h_large
  -- h_large now says l = 0 ∨ inst.voters = ∅
  cases h_large with
  | inl h_l_zero =>
    -- l = 0 contradicts hl : l ≥ 1
    rw [h_l_zero] at hl
    omega
  | inr h_voters_empty =>
    -- inst.voters = ∅ contradicts voters_nonempty
    have : inst.voters.Nonempty := inst.voters_nonempty
    rw [h_voters_empty] at this
    exact Finset.not_nonempty_empty this


-- 5. THEOREM: EJR+ implies EJR

theorem ejr_plus_implies_ejr (inst : ABCInstance V C) (W : Finset C) :
    inst.is_ejr_plus W → inst.is_ejr W := by
  intro h_ejr_plus
  -- Unfold the definitions
  unfold is_ejr is_ejr_plus at *
  constructor
  · -- W has the right size
    exact h_ejr_plus.1
  · -- For any l-cohesive group S, someone in S has utility >= l
    intro S l h_S_subset hl_pos h_cohesive
    -- We'll prove this by contradiction
    by_contra h_not
    push_neg at h_not
    -- h_not says: for all i in S, utility of i is < l
    -- Since everyone in S has utility < l, and they have l common approvals,
    -- at least one common approval must not be in W
    unfold is_l_cohesive at h_cohesive
    have ⟨h_large, h_common⟩ := h_cohesive
    -- S is l-large with l >= 1, so it's nonempty
    have h_S_nonempty := l_large_nonempty inst S l hl_pos h_large
    -- Simplify common_approvals S using the nonempty fact
    have h_common_approvals_eq : inst.common_approvals S = S.inf' h_S_nonempty inst.approves := by
      unfold common_approvals
      simp [h_S_nonempty]
    -- The common approvals have size >= l
    -- We need to show that some common approval is not in W
    have h_exists_missing : ∃ c ∈ inst.common_approvals S, c ∉ W := by
      -- If all common approvals were in W, then for any i in S,
      -- W ∩ approves(i) would contain all common approvals, so >= l
      by_contra h_all_in
      push_neg at h_all_in
      -- h_all_in says: all common approvals are in W
      -- Pick any voter i in S
      obtain ⟨i, hi_mem⟩ := h_S_nonempty
      -- For this voter i, W ∩ approves(i) contains all common approvals
      have h_common_subset : inst.common_approvals S ⊆ W ∩ inst.approves i := by
        intro c hc
        rw [Finset.mem_inter]
        constructor
        · -- c ∈ W because all common approvals are in W
          exact h_all_in c hc
        · -- c ∈ approves(i) because c is a common approval
          rw [h_common_approvals_eq] at hc
          rw [Finset.mem_inf'] at hc
          exact hc i hi_mem
      -- So the size is at least l
      have : (W ∩ inst.approves i).card ≥ l := by
        calc (W ∩ inst.approves i).card
          _ ≥ (inst.common_approvals S).card := Finset.card_le_card h_common_subset
          _ ≥ l := h_common
      -- But this contradicts h_not
      exact Nat.not_lt.mpr this (h_not i hi_mem)
    -- Now we have c ∈ common_approvals S but c ∉ W
    obtain ⟨c, hc_common, hc_not_in_W⟩ := h_exists_missing
    -- c is approved by all voters in S
    have hc_approved : ∀ j ∈ S, c ∈ inst.approves j := by
      intro j hj
      rw [h_common_approvals_eq] at hc_common
      rw [Finset.mem_inf'] at hc_common
      exact hc_common j hj
    -- Now apply EJR+ with S, l, and c
    have hc_witness : c ∈ inst.candidates \ W := by
      rw [Finset.mem_sdiff]
      constructor
      · -- c ∈ inst.candidates
        -- Since S is nonempty, pick any voter i in S
        obtain ⟨i, hi_mem⟩ := h_S_nonempty
        -- c is approved by i (from hc_approved)
        have : c ∈ inst.approves i := hc_approved i hi_mem
        -- Since i is a voter (from S ⊆ voters), approves i ⊆ candidates
        have hi_voter : i ∈ inst.voters := h_S_subset hi_mem
        have : inst.approves i ⊆ inst.candidates := inst.approves_subset i hi_voter
        exact this (hc_approved i hi_mem)
      · -- c ∉ W
        exact hc_not_in_W
    have h_ejr_plus_result := h_ejr_plus.2 S l h_S_subset hl_pos ⟨h_large, c, hc_witness, hc_approved⟩
    -- This gives us some i in S with utility >= l
    obtain ⟨i, hi_mem, hi_utility⟩ := h_ejr_plus_result
    -- But h_not says all i in S have utility < l
    have hi_low := h_not i hi_mem
    -- Contradiction!
    omega

end ABCInstance
