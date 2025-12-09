import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic

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
-- Note: We do not require W.card = k; any committee (including partial ones)
-- can satisfy EJR, and any completion of an EJR committee preserves EJR.
def is_ejr (inst : ABCInstance V C) (W : Finset C) : Prop :=
  ∀ (S : Finset V) (l : ℕ),
    S ⊆ inst.voters →
    l ≥ 1 →
    inst.is_l_cohesive S l →
    ∃ i ∈ S, (W ∩ inst.approves i).card ≥ l

-- Axiom EJR+: A committee W satisfies EJR+ if for every l-large group S
-- who all approve some candidate c not in W,
-- there is at least one voter in S who approves at least l candidates in W.
-- Note: We do not require W.card = k (same reasoning as EJR).
def is_ejr_plus (inst : ABCInstance V C) (W : Finset C) : Prop :=
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
  exact Finset.card_pos.mp <| Nat.pos_of_mul_pos_right <|
    (Nat.mul_pos hl (Finset.card_pos.mpr inst.voters_nonempty)).trans_le h_large

-- Helper lemma: characterize membership in common_approvals
lemma mem_common_approvals_iff (inst : ABCInstance V C) (S : Finset V) (c : C) :
    c ∈ inst.common_approvals S ↔ c ∈ inst.candidates ∧ ∀ v ∈ S, c ∈ inst.approves v := by
  simp [common_approvals, Finset.mem_filter]

-- 5. THEOREM: EJR+ implies EJR

theorem ejr_plus_implies_ejr (inst : ABCInstance V C) (W : Finset C) :
    inst.is_ejr_plus W → inst.is_ejr W := by
  intro h_ejr_plus
  intro S l h_S_subset hl_pos ⟨h_large, h_common⟩
  -- Either all common approvals are in W, or some is missing
  by_cases h_sub : inst.common_approvals S ⊆ W
  -- Case 1: All common approvals in W → any voter in S has ≥ l in W
  · obtain ⟨i, hi⟩ := l_large_nonempty inst S l hl_pos h_large
    refine ⟨i, hi, h_common.trans (Finset.card_le_card ?_)⟩
    exact fun c hc => Finset.mem_inter.mpr
      ⟨h_sub hc, (mem_common_approvals_iff inst S c).mp hc |>.2 i hi⟩
  -- Case 2: Some common approval c ∉ W → apply EJR+
  · obtain ⟨c, hc_common, hc_not_in_W⟩ := Finset.not_subset.mp h_sub
    have hc := (mem_common_approvals_iff inst S c).mp hc_common
    exact h_ejr_plus S l h_S_subset hl_pos
      ⟨h_large, c, Finset.mem_sdiff.mpr ⟨hc.1, hc_not_in_W⟩, hc.2⟩

-- ============================================================================
-- 6. PARETO OPTIMALITY
-- ============================================================================

-- Utility function: number of approved candidates in committee
-- (This is what we already use implicitly; making it explicit)
def utility (inst : ABCInstance V C) (W : Finset C) (i : V) : ℕ :=
  (W ∩ inst.approves i).card

-- Pareto dominance: W' Pareto dominates W if everyone is weakly better off
-- under W' and at least one voter is strictly better off
def pareto_dominates (inst : ABCInstance V C) (W' W : Finset C) : Prop :=
  (∀ i ∈ inst.voters, inst.utility W' i ≥ inst.utility W i) ∧
  (∃ i ∈ inst.voters, inst.utility W' i > inst.utility W i)

-- Pareto optimality: no committee of size k Pareto dominates W
def is_pareto_optimal (inst : ABCInstance V C) (W : Finset C) : Prop :=
  W.card = inst.k ∧
  ∀ W' : Finset C, W'.card = inst.k → ¬inst.pareto_dominates W' W

-- ============================================================================
-- 7. HELPER LEMMAS FOR HARMONIC FUNCTION
-- ============================================================================

-- Each term in the harmonic sum is positive
lemma harmonic_term_pos (i : ℕ) : (0 : ℚ) < 1 / (i + 1) := by
  exact one_div_pos.mpr (by exact_mod_cast Nat.succ_pos i)

-- Harmonic is weakly monotone
lemma harmonic_mono {m n : ℕ} (h : m ≤ n) : harmonic m ≤ harmonic n := by
  unfold harmonic
  gcongr

-- Harmonic is strictly monotone
lemma harmonic_strict_mono {m n : ℕ} (h : m < n) : harmonic m < harmonic n := by
  unfold harmonic
  exact Finset.sum_lt_sum_of_subset (Finset.range_mono (le_of_lt h)) (Finset.mem_range.mpr h)
    (Finset.notMem_range_self) (harmonic_term_pos m) (fun j _ _ => le_of_lt (harmonic_term_pos j))

-- ============================================================================
-- 8. KEY LEMMA: Pareto dominance implies higher PAV score
-- ============================================================================

-- If W' Pareto dominates W, then PAV score of W' is strictly higher
lemma pareto_dominates_implies_higher_score (inst : ABCInstance V C) (W W' : Finset C)
    (h_dom : inst.pareto_dominates W' W) :
    inst.pav_score W < inst.pav_score W' := by
  obtain ⟨h_all_weak, j, hj_voter, hj_strict⟩ := h_dom
  unfold pav_score
  apply Finset.sum_lt_sum
  · exact fun i hi => harmonic_mono (h_all_weak i hi)
  · exact ⟨j, hj_voter, harmonic_strict_mono hj_strict⟩

-- ============================================================================
-- 9. MAIN THEOREM: PAV winners are Pareto optimal
-- ============================================================================

/--
PAV winners satisfy Pareto optimality.

**Proof sketch:** Suppose W is a PAV winner but not Pareto optimal.
Then there exists W' of size k that Pareto dominates W.
By `pareto_dominates_implies_higher_score`, pav_score W' > pav_score W.
But W being a PAV winner means pav_score W' ≤ pav_score W for all W' of size k.
Contradiction.
-/
theorem pav_winner_is_pareto_optimal (inst : ABCInstance V C) (W : Finset C)
    (h_winner : inst.is_pav_winner W) : inst.is_pareto_optimal W := by
  obtain ⟨h_card, h_max⟩ := h_winner
  refine ⟨h_card, ?_⟩
  intro W' h_card' h_dom
  have h_score_strict : inst.pav_score W < inst.pav_score W' :=
    pareto_dominates_implies_higher_score inst W W' h_dom
  have h_score_le : inst.pav_score W' ≤ inst.pav_score W := h_max W' h_card'
  exact absurd h_score_strict (not_lt_of_ge h_score_le)

end ABCInstance
