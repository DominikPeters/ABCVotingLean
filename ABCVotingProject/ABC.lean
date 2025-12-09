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

-- ============================================================================
-- 10. PAV SATISFIES EJR+
-- ============================================================================

-- Key identity: harmonic(n+1) - harmonic(n) = 1/(n+1)
lemma harmonic_succ_sub (n : ℕ) : harmonic (n + 1) - harmonic n = 1 / (n + 1) := by
  simp only [harmonic, Finset.sum_range_succ, add_sub_cancel_left]

-- The score contribution from adding a candidate c to committee W for voter i
-- If i approves c: gain is 1/(u_i(W) + 1), otherwise 0
lemma score_gain_voter (inst : ABCInstance V C) (W : Finset C) (c : C) (i : V)
    (hc : c ∉ W) :
    harmonic ((W ∪ {c}) ∩ inst.approves i).card - harmonic (W ∩ inst.approves i).card =
    if c ∈ inst.approves i then 1 / ((W ∩ inst.approves i).card + 1 : ℚ) else 0 := by
  split_ifs with hci
  · have h : (W ∪ {c}) ∩ inst.approves i = insert c (W ∩ inst.approves i) := by
      ext x
      simp only [mem_inter, mem_union, mem_singleton, mem_insert]
      constructor
      · rintro ⟨hxW | rfl, hxa⟩
        · right; exact ⟨hxW, hxa⟩
        · left; rfl
      · rintro (rfl | ⟨hxW, hxa⟩)
        · exact ⟨Or.inr rfl, hci⟩
        · exact ⟨Or.inl hxW, hxa⟩
    have hc' : c ∉ W ∩ inst.approves i := fun h => hc (mem_inter.mp h).1
    rw [h, card_insert_of_notMem hc', harmonic_succ_sub]
  · have h : (W ∪ {c}) ∩ inst.approves i = W ∩ inst.approves i := by
      ext x
      simp only [mem_inter, mem_union, mem_singleton]
      constructor
      · rintro ⟨hxW | rfl, hxa⟩
        · exact ⟨hxW, hxa⟩
        · exact absurd hxa hci
      · rintro ⟨hxW, hxa⟩
        exact ⟨Or.inl hxW, hxa⟩
    rw [h, sub_self]

-- PAV score change when adding a candidate
lemma pav_score_add_candidate (inst : ABCInstance V C) (W : Finset C) (c : C)
    (hc : c ∉ W) :
    inst.pav_score (W ∪ {c}) - inst.pav_score W =
    ∑ i ∈ inst.voters.filter (fun i => c ∈ inst.approves i),
      1 / ((W ∩ inst.approves i).card + 1 : ℚ) := by
  unfold pav_score
  rw [← Finset.sum_sub_distrib]
  trans (∑ i ∈ inst.voters, if c ∈ inst.approves i
      then 1 / ((W ∩ inst.approves i).card + 1 : ℚ) else 0)
  · congr 1 with i
    exact score_gain_voter inst W c i hc
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]

-- The score contribution from removing a candidate c from committee W for voter i
lemma score_loss_voter (inst : ABCInstance V C) (W : Finset C) (c : C) (i : V)
    (hc : c ∈ W) :
    harmonic (W ∩ inst.approves i).card - harmonic ((W \ {c}) ∩ inst.approves i).card =
    if c ∈ inst.approves i then 1 / ((W ∩ inst.approves i).card : ℚ) else 0 := by
  split_ifs with hci
  · have h : W ∩ inst.approves i = insert c ((W \ {c}) ∩ inst.approves i) := by
      ext x
      simp only [mem_inter, mem_insert, mem_sdiff, mem_singleton]
      constructor
      · rintro ⟨hxW, hxa⟩
        by_cases hxc : x = c
        · left; exact hxc
        · right; exact ⟨⟨hxW, hxc⟩, hxa⟩
      · rintro (rfl | ⟨⟨hxW, _⟩, hxa⟩)
        · exact ⟨hc, hci⟩
        · exact ⟨hxW, hxa⟩
    have hc' : c ∉ (W \ {c}) ∩ inst.approves i := fun hx =>
      (mem_sdiff.mp (mem_inter.mp hx).1).2 (mem_singleton.mpr rfl)
    rw [h, card_insert_of_notMem hc', harmonic_succ_sub]; simp
  · have h : (W \ {c}) ∩ inst.approves i = W ∩ inst.approves i := by
      ext x
      simp only [mem_inter, mem_sdiff, mem_singleton]
      constructor
      · rintro ⟨⟨hxW, _⟩, hxa⟩
        exact ⟨hxW, hxa⟩
      · rintro ⟨hxW, hxa⟩
        refine ⟨⟨hxW, ?_⟩, hxa⟩
        rintro rfl
        exact hci hxa
    rw [h, sub_self]

-- PAV score change when removing a candidate
lemma pav_score_remove_candidate (inst : ABCInstance V C) (W : Finset C) (c : C)
    (hc : c ∈ W) :
    inst.pav_score W - inst.pav_score (W \ {c}) =
    ∑ i ∈ inst.voters.filter (fun i => c ∈ inst.approves i),
      1 / ((W ∩ inst.approves i).card : ℚ) := by
  unfold pav_score
  rw [← Finset.sum_sub_distrib]
  trans (∑ i ∈ inst.voters, if c ∈ inst.approves i
      then 1 / ((W ∩ inst.approves i).card : ℚ) else 0)
  · congr 1 with i
    exact score_loss_voter inst W c i hc
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]

-- Sum of removal costs over all candidates equals number of voters with positive utility
-- ∑_{c ∈ W} ∑_{i : c ∈ A_i} 1/u_i(W) = ∑_{i ∈ N} ∑_{c ∈ A_i ∩ W} 1/u_i(W)
--                                    = #{i ∈ N : u_i(W) > 0}
lemma sum_removal_costs (inst : ABCInstance V C) (W : Finset C) :
    ∑ c ∈ W, ∑ i ∈ inst.voters.filter (fun i => c ∈ inst.approves i),
      1 / ((W ∩ inst.approves i).card : ℚ) =
    (inst.voters.filter (fun i => (W ∩ inst.approves i).Nonempty)).card := by
  -- Rewrite using indicator functions to enable sum_comm
  trans (∑ c ∈ W, ∑ i ∈ inst.voters,
      if c ∈ inst.approves i then 1 / ((W ∩ inst.approves i).card : ℚ) else 0)
  · congr 1 with c
    rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  -- Now the outer sum is over voters; inner sum simplifies since filter matches intersection
  trans (∑ i ∈ inst.voters, ∑ c ∈ W ∩ inst.approves i, 1 / ((W ∩ inst.approves i).card : ℚ))
  · congr 1 with i
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext c; simp only [mem_filter, mem_inter]
    · intros; rfl
  -- For each voter, sum of |W ∩ A_i| copies of 1/|W ∩ A_i| equals 1 (if nonempty) or 0
  trans (∑ i ∈ inst.voters, if (W ∩ inst.approves i).Nonempty then (1 : ℚ) else 0)
  · congr 1 with i
    by_cases hne : (W ∩ inst.approves i).Nonempty
    · simp only [hne, ↓reduceIte]
      have hcard_pos : 0 < (W ∩ inst.approves i).card := card_pos.mpr hne
      have hcard_ne : ((W ∩ inst.approves i).card : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hcard_pos)
      rw [Finset.sum_const, nsmul_eq_mul, mul_one_div, div_self hcard_ne]
    · simp [not_nonempty_iff_eq_empty.mp hne]
  -- Convert to cardinality
  rw [← Finset.sum_boole]

-- Corollary: The sum of removal costs is at most n
lemma sum_removal_costs_le_voters (inst : ABCInstance V C) (W : Finset C) :
    ∑ c ∈ W, ∑ i ∈ inst.voters.filter (fun i => c ∈ inst.approves i),
      1 / ((W ∩ inst.approves i).card : ℚ) ≤ inst.voters.card := by
  rw [sum_removal_costs]
  exact_mod_cast Finset.card_filter_le inst.voters _

-- Lower bound on gain from adding a candidate that everyone in S approves
-- when everyone in S has utility < l
lemma score_gain_lower_bound (inst : ABCInstance V C) (W : Finset C) (c : C) (S : Finset V)
    (l : ℕ) (hl : 1 ≤ l)
    (hc : c ∉ W)
    (hS_sub : S ⊆ inst.voters)
    (hS_approves : ∀ i ∈ S, c ∈ inst.approves i)
    (h_util_bound : ∀ i ∈ S, (W ∩ inst.approves i).card < l) :
    (S.card : ℚ) / l ≤ inst.pav_score (W ∪ {c}) - inst.pav_score W := by
  rw [pav_score_add_candidate inst W c hc]
  -- The sum over voters who approve c includes S
  calc (S.card : ℚ) / l
      = ∑ _ ∈ S, (1 : ℚ) / l := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ ∑ i ∈ S, 1 / ((W ∩ inst.approves i).card + 1 : ℚ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hbound := h_util_bound i hi
        have h1 : (W ∩ inst.approves i).card + 1 ≤ l := hbound
        have h2 : (1 : ℚ) ≤ l := by exact_mod_cast hl
        have h3 : (0 : ℚ) < (W ∩ inst.approves i).card + 1 := by norm_cast; omega
        have h4 : (0 : ℚ) < l := by linarith
        exact one_div_le_one_div_of_le h3 (by exact_mod_cast h1)
    _ ≤ ∑ i ∈ inst.voters.filter (fun i => c ∈ inst.approves i),
          1 / ((W ∩ inst.approves i).card + 1 : ℚ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [mem_filter]
          exact ⟨hS_sub hi, hS_approves i hi⟩
        · intro i _ _; positivity

-- Main theorem: PAV winners satisfy EJR+
theorem pav_winner_satisfies_ejr_plus (inst : ABCInstance V C) (W : Finset C)
    (h_winner : inst.is_pav_winner W) : inst.is_ejr_plus W := by
  obtain ⟨h_card, h_max⟩ := h_winner
  intro S l hS_sub hl ⟨h_large, c, hc_cand, hS_approves⟩
  -- Assume for contradiction that everyone in S has utility < l
  by_contra h_neg
  push_neg at h_neg
  -- h_neg : ∀ i ∈ S, (W ∩ inst.approves i).card < l
  -- Let W̃ = W ∪ {c}
  let W' := W ∪ {c}
  have hc_not_in_W : c ∉ W := (mem_sdiff.mp hc_cand).2

  -- Step 1: Score gain from adding c is ≥ |S|/l ≥ n/k
  have h_gain : (S.card : ℚ) / l ≤ inst.pav_score W' - inst.pav_score W :=
    score_gain_lower_bound inst W c S l hl hc_not_in_W hS_sub hS_approves h_neg

  -- From l-large: |S| ≥ l * n / k, so |S|/l ≥ n/k
  have h_large_ineq : (inst.voters.card : ℚ) / inst.k ≤ (S.card : ℚ) / l := by
    unfold is_l_large at h_large
    have hk_pos : (0 : ℚ) < inst.k := Nat.cast_pos.mpr inst.k_pos
    have hl_pos : (0 : ℚ) < l := Nat.cast_pos.mpr hl
    field_simp
    calc (inst.voters.card : ℚ) * l = l * inst.voters.card := by ring
      _ ≤ S.card * inst.k := by exact_mod_cast h_large
      _ = inst.k * S.card := by ring

  have h_gain' : (inst.voters.card : ℚ) / inst.k ≤ inst.pav_score W' - inst.pav_score W :=
    le_trans h_large_ineq h_gain

  -- Step 2: Sum of removal costs over W' is ≤ n
  have h_W'_card : W'.card = inst.k + 1 := by
    simp only [W', union_singleton, card_insert_of_notMem hc_not_in_W, h_card]

  have h_sum_le : ∑ c' ∈ W', ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
      1 / ((W' ∩ inst.approves i).card : ℚ) ≤ inst.voters.card :=
    sum_removal_costs_le_voters inst W'

  -- Step 3: By pigeonhole, there exists c† with removal cost < n/(k+1) < n/k
  -- Sum over k+1 elements is ≤ n, so there exists one element with value < n/k
  -- (since if all ≥ n/k, sum would be ≥ (k+1) * n/k > n)
  have h_exists_small : ∃ c' ∈ W',
      ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
        1 / ((W' ∩ inst.approves i).card : ℚ) < (inst.voters.card : ℚ) / inst.k := by
    by_contra h_all_large
    push_neg at h_all_large
    have h_sum_ge : (inst.k + 1) * ((inst.voters.card : ℚ) / inst.k) ≤
        ∑ c' ∈ W', ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
          1 / ((W' ∩ inst.approves i).card : ℚ) := by
      calc (inst.k + 1) * ((inst.voters.card : ℚ) / inst.k)
          = ∑ _ ∈ W', (inst.voters.card : ℚ) / inst.k := by
            simp only [Finset.sum_const, h_W'_card, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        _ ≤ ∑ c' ∈ W', ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
              1 / ((W' ∩ inst.approves i).card : ℚ) :=
            Finset.sum_le_sum (fun c' hc' => h_all_large c' hc')
    have h_arith : (inst.voters.card : ℚ) < (inst.k + 1) * ((inst.voters.card : ℚ) / inst.k) := by
      have hk_pos : (0 : ℚ) < inst.k := Nat.cast_pos.mpr inst.k_pos
      have hn_pos : (0 : ℚ) < inst.voters.card :=
        Nat.cast_pos.mpr (card_pos.mpr inst.voters_nonempty)
      field_simp
      linarith
    linarith

  obtain ⟨c', hc'_in_W', h_small⟩ := h_exists_small

  -- Step 4: W' \ {c'} has size k and higher PAV score than W
  have hc'_in : c' ∈ W' := hc'_in_W'
  have h_size : (W' \ {c'}).card = inst.k := by
    simp only [card_sdiff, card_singleton, h_W'_card, singleton_inter_of_mem hc'_in]
    omega

  -- PAV score of W' \ {c'} = PAV(W') - removal cost of c'
  have h_score_eq : inst.pav_score (W' \ {c'}) =
      inst.pav_score W' - ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
        1 / ((W' ∩ inst.approves i).card : ℚ) := by
    have := pav_score_remove_candidate inst W' c' hc'_in
    linarith

  -- So PAV(W' \ {c'}) > PAV(W') - n/k ≥ PAV(W)
  have h_better : inst.pav_score W < inst.pav_score (W' \ {c'}) := by
    calc inst.pav_score W
        = inst.pav_score W' - (inst.pav_score W' - inst.pav_score W) := by ring
      _ ≤ inst.pav_score W' - (inst.voters.card : ℚ) / inst.k := by linarith
      _ < inst.pav_score W' - ∑ i ∈ inst.voters.filter (fun i => c' ∈ inst.approves i),
            1 / ((W' ∩ inst.approves i).card : ℚ) := by linarith
      _ = inst.pav_score (W' \ {c'}) := by linarith

  -- This contradicts W being a PAV winner
  have h_le := h_max (W' \ {c'}) h_size
  linarith

end ABCInstance
