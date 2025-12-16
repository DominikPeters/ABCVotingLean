/-
# PAV Satisfies the Core for k ≤ 7

This file proves that PAV (Proportional Approval Voting) winners satisfy the core
property when the committee size k is at most 7.

The proof follows the paper "The Core of Approval-Based Committee Elections with
Few Candidates" by Dominik Peters.

## Main Results
- `local_pav_in_core`: Local PAV committees are in the core when k ≤ 7
- `pav_winner_in_core`: Global PAV winners are in the core when k ≤ 7
-/

import ABCVoting.Rules.PAV.Defs
import ABCVoting.Rules.PAV.CoreInequality
import ABCVoting.Axioms.Core

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- LOCAL PAV COMMITTEES
-- ============================================================================

/--
A swap replaces candidate x in W with candidate y not in W.
-/
def swap (W : Finset C) (x y : C) : Finset C := (W \ {x}) ∪ {y}

/--
A committee W is a local PAV committee if no single swap improves the PAV score.
-/
def is_local_pav_winner (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  W ⊆ inst.candidates ∧ W.card = k ∧
  ∀ x ∈ W, ∀ y ∈ inst.candidates \ W,
    inst.pav_score W ≥ inst.pav_score (swap W x y)

/--
Every global PAV winner is also a local PAV winner.
-/
theorem global_pav_is_local (inst : ABCInstance V C k) (W : Finset C)
    (hW : inst.is_pav_winner W) : inst.is_local_pav_winner W := by
  obtain ⟨hW_sub, hW_card, hW_max⟩ := hW
  refine ⟨hW_sub, hW_card, ?_⟩
  intro x hx y hy
  apply hW_max
  · intro c hc
    simp only [swap, mem_union, mem_sdiff, mem_singleton] at hc
    rcases hc with ⟨hcW, _⟩ | rfl
    · exact hW_sub hcW
    · exact (mem_sdiff.mp hy).1
  · simp only [swap]
    have hy_not : y ∉ W := (mem_sdiff.mp hy).2
    have hdisj : Disjoint (W \ {x}) {y} := by
      rw [disjoint_singleton_right, mem_sdiff, not_and, not_not]
      tauto
    simp only [card_union_of_disjoint hdisj, card_singleton, card_sdiff, singleton_inter_of_mem hx, hW_card]
    have hk_pos : k ≥ 1 := by rw [← hW_card]; exact card_pos.mpr ⟨x, hx⟩
    omega

-- ============================================================================
-- DELTA FOR A VOTER
-- ============================================================================

/--
The δ value for voter i: contribution to the sum of PAV score differences
from all swaps (x ∈ W \ T, y ∈ T \ W).

δ_i = [(|W \ T| - a) · c] / (a + b + 1) - [a · (|T \ W| - c)] / (a + b)

where:
- a = |(W \ T) ∩ A_i| (approved candidates in W \ T)
- b = |(W ∩ T) ∩ A_i| (approved candidates in W ∩ T)
- c = |(T \ W) ∩ A_i| (approved candidates in T \ W)
-/
noncomputable def delta_voter (inst : ABCInstance V C k) (W T : Finset C) (i : V) : ℚ :=
  let a := ((W \ T) ∩ inst.approves i).card
  let b := ((W ∩ T) ∩ inst.approves i).card
  let c := ((T \ W) ∩ inst.approves i).card
  let W_minus_T := (W \ T).card
  let T_minus_W := (T \ W).card
  delta_A W_minus_T T_minus_W a b c

/--
A voter prefers T to W if they have strictly higher utility from T.
-/
def prefers (inst : ABCInstance V C k) (i : V) (T W : Finset C) : Prop :=
  inst.utility T i > inst.utility W i

-- ============================================================================
-- KEY LEMMAS ABOUT DELTA
-- ============================================================================

/--
The utility of W equals a + b where a, b are the approved candidates in W \ T and W ∩ T.
-/
lemma utility_eq_a_plus_b (inst : ABCInstance V C k) (W T : Finset C) (i : V) :
    inst.utility W i = ((W \ T) ∩ inst.approves i).card + ((W ∩ T) ∩ inst.approves i).card := by
  unfold utility
  have h : W ∩ inst.approves i = ((W \ T) ∩ inst.approves i) ∪ ((W ∩ T) ∩ inst.approves i) := by
    ext c
    simp only [mem_inter, mem_union, mem_sdiff]
    constructor
    · intro ⟨hcW, hca⟩
      by_cases hcT : c ∈ T
      · right; exact ⟨⟨hcW, hcT⟩, hca⟩
      · left; exact ⟨⟨hcW, hcT⟩, hca⟩
    · rintro (⟨⟨hcW, _⟩, hca⟩ | ⟨⟨hcW, _⟩, hca⟩)
      · exact ⟨hcW, hca⟩
      · exact ⟨hcW, hca⟩
  rw [h, card_union_of_disjoint]
  rw [disjoint_iff_ne]
  intro x hx y hy
  simp only [mem_inter, mem_sdiff] at hx hy
  intro heq
  rw [heq] at hx
  exact hx.1.2 hy.1.2

/--
The utility of T equals b + c where b, c are the approved candidates in W ∩ T and T \ W.
-/
lemma utility_T_eq_b_plus_c (inst : ABCInstance V C k) (W T : Finset C) (i : V) :
    inst.utility T i = ((W ∩ T) ∩ inst.approves i).card + ((T \ W) ∩ inst.approves i).card := by
  unfold utility
  have h : T ∩ inst.approves i = ((W ∩ T) ∩ inst.approves i) ∪ ((T \ W) ∩ inst.approves i) := by
    ext c
    simp only [mem_inter, mem_union, mem_sdiff]
    constructor
    · intro ⟨hcT, hca⟩
      by_cases hcW : c ∈ W
      · left; exact ⟨⟨hcW, hcT⟩, hca⟩
      · right; exact ⟨⟨hcT, hcW⟩, hca⟩
    · rintro (⟨⟨_, hcT⟩, hca⟩ | ⟨⟨hcT, _⟩, hca⟩)
      · exact ⟨hcT, hca⟩
      · exact ⟨hcT, hca⟩
  rw [h, card_union_of_disjoint]
  rw [disjoint_iff_ne]
  intro x hx y hy
  simp only [mem_inter, mem_sdiff] at hx hy
  intro heq
  rw [heq] at hx
  exact hy.1.2 hx.1.1

/--
A voter prefers T to W iff c > a (where c = |(T \ W) ∩ A_i| and a = |(W \ T) ∩ A_i|).
-/
lemma prefers_iff_c_gt_a (inst : ABCInstance V C k) (W T : Finset C) (i : V) :
    prefers inst i T W ↔
    ((T \ W) ∩ inst.approves i).card > ((W \ T) ∩ inst.approves i).card := by
  unfold prefers
  rw [utility_eq_a_plus_b inst W T, utility_T_eq_b_plus_c inst W T]
  omega

/--
Trivial lower bound on δ: for any voter, δ_i ≥ -|T \ W|.
-/
lemma delta_voter_ge_neg (inst : ABCInstance V C k) (W T : Finset C) (i : V) :
    delta_voter inst W T i ≥ -((T \ W).card : ℚ) := by
  unfold delta_voter delta_A
  -- The first term is non-negative, so δ ≥ -second_term ≥ -|T \ W|
  have ha_le : ((W \ T) ∩ inst.approves i).card ≤ (W \ T).card := card_le_card inter_subset_left
  have hc_le : ((T \ W) ∩ inst.approves i).card ≤ (T \ W).card := card_le_card inter_subset_left
  set a := ((W \ T) ∩ inst.approves i).card
  set b := ((W ∩ T) ∩ inst.approves i).card
  set c := ((T \ W) ∩ inst.approves i).card
  set W_minus_T := (W \ T).card
  set T_minus_W := (T \ W).card
  -- The first term (W_minus_T - a) * c / (a + b + 1) is ≥ 0
  have h_first_nonneg : (0 : ℚ) ≤ (W_minus_T - a : ℚ) * c / (a + b + 1) := by
    apply div_nonneg
    · apply mul_nonneg
      · have : (a : ℚ) ≤ W_minus_T := by exact_mod_cast ha_le
        linarith
      · exact Nat.cast_nonneg c
    · have : (0 : ℚ) < a + b + 1 := by positivity
      linarith
  -- The second term a * (T_minus_W - c) / (a + b) is ≤ T_minus_W when a + b > 0
  by_cases hab : a + b = 0
  · -- When a + b = 0, second term is 0/0 which is 0 in Lean
    obtain ⟨ha0, hb0⟩ := Nat.add_eq_zero_iff.mp hab
    simp only [ha0, hb0, Nat.cast_zero, add_zero, zero_mul, zero_div, sub_zero, zero_add, div_one]
    have h1 : (0 : ℚ) ≤ W_minus_T := Nat.cast_nonneg _
    have h2 : (0 : ℚ) ≤ c := Nat.cast_nonneg _
    have h3 : (0 : ℚ) ≤ T_minus_W := Nat.cast_nonneg _
    nlinarith
  · have hab_pos : (0 : ℚ) < (a : ℚ) + b := by
      have h : 0 < a + b := Nat.pos_of_ne_zero hab
      have h' : (0 : ℚ) < ((a + b : ℕ) : ℚ) := by
        exact_mod_cast h
      simpa [Nat.cast_add] using h'
    have h_second_le : (a : ℚ) * (T_minus_W - c) / (a + b) ≤ T_minus_W := by
      have ha_le_ab : (a : ℚ) ≤ (a : ℚ) + b := by
        have hb : (0 : ℚ) ≤ b := Nat.cast_nonneg b
        linarith
      have hc_le' : (c : ℚ) ≤ T_minus_W := by exact_mod_cast hc_le
      calc (a : ℚ) * (T_minus_W - c) / (a + b)
          ≤ (a + b) * (T_minus_W - c) / (a + b) := by
            apply div_le_div_of_nonneg_right _ hab_pos.le
            apply mul_le_mul_of_nonneg_right ha_le_ab
            linarith
        _ = T_minus_W - c := by field_simp
        _ ≤ T_minus_W := by linarith
    linarith

/--
Better bound for voters who prefer T to W: δ_i > (k/|T| - 1) · |T \ W|.
This connects to our verified inequality from CoreInequality.lean.
-/
lemma delta_voter_of_prefers (inst : ABCInstance V C k) (W T : Finset C) (i : V)
    (hW_card : W.card = k) (hT_size : 1 ≤ T.card) (hT_bound : T.card < k) (hk : k ≤ 7)
    (hWT_disj : (W ∩ T).card < T.card) -- ensures T \ W is nonempty
    (h_prefers : prefers inst i T W) :
    delta_voter inst W T i > core_rhs k T.card (T \ W).card := by
  unfold delta_voter
  -- Extract the quantities
  set a := ((W \ T) ∩ inst.approves i).card
  set b := ((W ∩ T) ∩ inst.approves i).card
  set c := ((T \ W) ∩ inst.approves i).card
  -- Show c > a from the preference
  have hca : c > a := (prefers_iff_c_gt_a inst W T i).mp h_prefers
  -- Show the bounds on parameters
  have ha_bound : a ≤ (W \ T).card := card_le_card inter_subset_left
  have hb_bound : b ≤ (W ∩ T).card := card_le_card inter_subset_left
  have hc_bound : c ≤ (T \ W).card := card_le_card inter_subset_left
  -- Relate W \ T to k and W ∩ T
  have hWT_eq : (W \ T).card = k - (W ∩ T).card := by
    rw [card_sdiff, hW_card, inter_comm]
  have hTW_eq : (T \ W).card = T.card - (W ∩ T).card := by
    rw [card_sdiff]
  -- Use the verified inequality based on k
  rw [hWT_eq, hTW_eq]
  -- Apply the core inequality theorem
  have h_ineq : core_ineq_holds k T.card (W ∩ T).card a b c := by
    have hk_ge2 : 2 ≤ k := by omega
    have ha' : a ≤ k - (W ∩ T).card := by
      simpa [hWT_eq] using ha_bound
    have hb' : b ≤ (W ∩ T).card := hb_bound
    have hc' : c ≤ T.card - (W ∩ T).card := by
      simpa [hTW_eq] using hc_bound
    have hk_cases : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · have hT_eq : T.card = 1 := by omega
      have h_ineq2 : core_ineq_holds 2 1 (W ∩ T).card a b c :=
        core_ineq_k2_t1 (W ∩ T).card a b c
          (by simpa [hT_eq] using hWT_disj)
          (by simpa using ha')
          (by simpa using hb')
          (by simpa [hT_eq] using hc')
          hca
      simpa [hT_eq] using h_ineq2
    · exact core_ineq_k3 T.card (W ∩ T).card a b c
        hT_size (by omega) hWT_disj (by simpa using ha') (by simpa using hb') (by simpa using hc') hca
    · exact core_ineq_k4 T.card (W ∩ T).card a b c
        hT_size (by omega) hWT_disj (by simpa using ha') (by simpa using hb') (by simpa using hc') hca
    · exact core_ineq_k5 T.card (W ∩ T).card a b c
        hT_size (by omega) hWT_disj (by simpa using ha') (by simpa using hb') (by simpa using hc') hca
    · exact core_ineq_k6 T.card (W ∩ T).card a b c
        hT_size (by omega) hWT_disj (by simpa using ha') (by simpa using hb') (by simpa using hc') hca
    · exact core_ineq_k7 T.card (W ∩ T).card a b c
        hT_size (by omega) hWT_disj (by simpa using ha') (by simpa using hb') (by simpa using hc') hca
  simpa [core_ineq_holds] using h_ineq

/-!
## Auxiliary inequality for `|T| = |W| = k`

When `T.card = k`, we have `core_rhs k T.card _ = 0`. For the main core argument we
only need that a voter who strictly prefers `T` to `W` has strictly positive `δ`.
-/

lemma delta_A_pos_of_eq (M a b c : ℕ) (ha : a ≤ M) (hc : c ≤ M) (hca : c > a) :
    delta_A M M a b c > 0 := by
  classical
  have hc0 : 0 < c := lt_of_le_of_lt (Nat.zero_le a) hca
  have hM0 : 0 < M := lt_of_lt_of_le hc0 hc
  unfold delta_A
  by_cases hab : a + b = 0
  · obtain ⟨ha0, hb0⟩ := Nat.add_eq_zero_iff.mp hab
    subst ha0; subst hb0
    have hMc : (0 : ℚ) < (M : ℚ) * (c : ℚ) :=
      mul_pos (Nat.cast_pos.mpr hM0) (Nat.cast_pos.mpr hc0)
    simpa using hMc
  · have hs_pos_nat : 0 < a + b := Nat.pos_of_ne_zero hab
    have hs_pos : (0 : ℚ) < (a + b : ℚ) := by exact_mod_cast hs_pos_nat
    have hs1_pos : (0 : ℚ) < (a + b + 1 : ℚ) := by positivity
    have hs0 : (a + b : ℚ) ≠ 0 := ne_of_gt hs_pos
    have hs1 : (a + b + 1 : ℚ) ≠ 0 := ne_of_gt hs1_pos

    have hc_ge : a + 1 ≤ c := Nat.succ_le_iff.2 hca
    have hMc_le : M - c ≤ M - (a + 1) := Nat.sub_le_sub_left hc_ge M

    have hcast_Ma : ((M - a : ℕ) : ℚ) = (M : ℚ) - a := by
      simpa using (Nat.cast_sub ha)
    have hcast_Mc : ((M - c : ℕ) : ℚ) = (M : ℚ) - c := by
      simpa using (Nat.cast_sub hc)
    have hcast_Ma1 : ((M - (a + 1) : ℕ) : ℚ) = (M : ℚ) - (a + 1) := by
      have ha1 : a + 1 ≤ M := le_trans hc_ge hc
      simpa using (Nat.cast_sub ha1)

    have hterm1_le : ((M - a : ℕ) : ℚ) * (a + 1) / (a + b + 1)
        ≤ ((M - a : ℕ) : ℚ) * c / (a + b + 1) := by
      have hcaQ : (a + 1 : ℚ) ≤ c := by exact_mod_cast hc_ge
      have hMa_nonneg : (0 : ℚ) ≤ ((M - a : ℕ) : ℚ) := by exact_mod_cast Nat.zero_le _
      have hmul : ((M - a : ℕ) : ℚ) * (a + 1 : ℚ) ≤ ((M - a : ℕ) : ℚ) * (c : ℚ) :=
        mul_le_mul_of_nonneg_left hcaQ hMa_nonneg
      exact div_le_div_of_nonneg_right hmul (show (0 : ℚ) ≤ (a + b + 1 : ℚ) from by positivity)

    have hterm2_le : (a : ℚ) * ((M - c : ℕ) : ℚ) / (a + b)
        ≤ (a : ℚ) * ((M - (a + 1) : ℕ) : ℚ) / (a + b) := by
      have hsub : ((M - c : ℕ) : ℚ) ≤ ((M - (a + 1) : ℕ) : ℚ) := by
        exact_mod_cast hMc_le
      have ha_nonneg : (0 : ℚ) ≤ a := Nat.cast_nonneg a
      have hmul :
          (a : ℚ) * ((M - c : ℕ) : ℚ) ≤ (a : ℚ) * ((M - (a + 1) : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left hsub ha_nonneg
      exact div_le_div_of_nonneg_right hmul (show (0 : ℚ) ≤ (a + b : ℚ) from le_of_lt hs_pos)

    have hdelta_ge :
        ((M - a : ℕ) : ℚ) * (a + 1) / (a + b + 1) -
            (a : ℚ) * ((M - (a + 1) : ℕ) : ℚ) / (a + b)
          ≤
        ((M - a : ℕ) : ℚ) * c / (a + b + 1) -
            (a : ℚ) * ((M - c : ℕ) : ℚ) / (a + b) := by
      linarith

    have hdelta1_eq :
        ((M - a : ℕ) : ℚ) * (a + 1) / (a + b + 1) -
            (a : ℚ) * ((M - (a + 1) : ℕ) : ℚ) / (a + b)
          =
        ((a : ℚ) * (a + 1) + (M : ℚ) * b) / ((a + b + 1 : ℚ) * (a + b : ℚ)) := by
      simp [hcast_Ma, hcast_Ma1]
      field_simp [hs0, hs1]
      ring_nf

    have hnum_pos : (0 : ℚ) < (a : ℚ) * (a + 1) + (M : ℚ) * b := by
      by_cases ha0 : a = 0
      · subst ha0
        have hbpos : 0 < b := by simpa using hs_pos_nat
        have : (0 : ℚ) < (M : ℚ) * (b : ℚ) :=
          mul_pos (Nat.cast_pos.mpr hM0) (Nat.cast_pos.mpr hbpos)
        nlinarith
      · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
        have haQ : (0 : ℚ) < a := by exact_mod_cast ha_pos
        have ha1Q : (0 : ℚ) < (a + 1 : ℚ) := by positivity
        have : (0 : ℚ) < (a : ℚ) * (a + 1 : ℚ) := mul_pos haQ ha1Q
        nlinarith

    have hden_pos : (0 : ℚ) < (a + b + 1 : ℚ) * (a + b : ℚ) :=
      mul_pos hs1_pos hs_pos

    have hdelta1_pos :
        0 <
          ((M - a : ℕ) : ℚ) * (a + 1) / (a + b + 1) -
            (a : ℚ) * ((M - (a + 1) : ℕ) : ℚ) / (a + b) := by
      rw [hdelta1_eq]
      exact div_pos hnum_pos hden_pos

    have hdelta_pos :
        0 <
          ((M - a : ℕ) : ℚ) * c / (a + b + 1) -
            (a : ℚ) * ((M - c : ℕ) : ℚ) / (a + b) :=
      lt_of_lt_of_le hdelta1_pos hdelta_ge

    simpa [hcast_Ma, hcast_Mc] using hdelta_pos

lemma delta_voter_pos_of_prefers_same_size (inst : ABCInstance V C k) (W T : Finset C) (i : V)
    (hW_card : W.card = k) (hT_card : T.card = k) (h_prefers : prefers inst i T W) :
    delta_voter inst W T i > 0 := by
  classical
  unfold delta_voter
  set a := ((W \ T) ∩ inst.approves i).card
  set b := ((W ∩ T) ∩ inst.approves i).card
  set c := ((T \ W) ∩ inst.approves i).card
  set W_minus_T := (W \ T).card
  set T_minus_W := (T \ W).card
  have hca : c > a := (prefers_iff_c_gt_a inst W T i).mp h_prefers
  have ha_bound : a ≤ W_minus_T := card_le_card inter_subset_left
  have hc_bound : c ≤ T_minus_W := card_le_card inter_subset_left
  have hWm_eq : W_minus_T = k - (W ∩ T).card := by
    -- `card_sdiff` gives `#(W \ T) = #W - #(T ∩ W)`
    simpa [W_minus_T, hW_card, inter_comm] using (card_sdiff (s := T) (t := W))
  have hTm_eq : T_minus_W = k - (W ∩ T).card := by
    simpa [T_minus_W, hT_card] using (card_sdiff (s := W) (t := T))
  have hWmTm : W_minus_T = T_minus_W := by simpa [hWm_eq, hTm_eq]
  -- reduce to `delta_A M M a b c > 0`
  simpa [a, b, c, W_minus_T, T_minus_W, hWmTm] using
    (delta_A_pos_of_eq T_minus_W a b c (by simpa [hWmTm] using ha_bound) hc_bound hca)

-- ============================================================================
-- SWAPPING SUM DECOMPOSITION (TODO)
-- ============================================================================

/--
Sum of all swap contributions equals sum of delta over voters.
-/
theorem swapping_sum_eq_delta_sum (inst : ABCInstance V C k) (W T : Finset C) :
    ∑ x ∈ W \ T, ∑ y ∈ T \ W, (inst.pav_score (swap W x y) - inst.pav_score W) =
    ∑ i ∈ inst.voters, delta_voter inst W T i := by
  classical
  -- Expand the PAV scores; `swap` is definitionally `insert` after simplifying.
  simp [pav_score, swap]
  -- Commute the triple sum to sum over voters first.
  have hTriple :
      (∑ x ∈ W \ T, ∑ y ∈ T \ W, ∑ i ∈ inst.voters,
          harmonic #(insert y (W \ {x}) ∩ inst.approves i)) =
        ∑ i ∈ inst.voters, ∑ x ∈ W \ T, ∑ y ∈ T \ W,
          harmonic #(insert y (W \ {x}) ∩ inst.approves i) := by
    -- swap `y` and `i` inside the `x`-sum, then swap `x` and `i`
    have h1 :
        (∑ x ∈ W \ T, ∑ y ∈ T \ W, ∑ i ∈ inst.voters,
            harmonic #(insert y (W \ {x}) ∩ inst.approves i)) =
          ∑ x ∈ W \ T, ∑ i ∈ inst.voters, ∑ y ∈ T \ W,
            harmonic #(insert y (W \ {x}) ∩ inst.approves i) := by
      apply Finset.sum_congr rfl
      intro x hx
      simpa using
        (Finset.sum_comm (s := T \ W) (t := inst.voters)
          (f := fun y i => harmonic #(insert y (W \ {x}) ∩ inst.approves i)))
    have h2 :
        (∑ x ∈ W \ T, ∑ i ∈ inst.voters, ∑ y ∈ T \ W,
            harmonic #(insert y (W \ {x}) ∩ inst.approves i)) =
          ∑ i ∈ inst.voters, ∑ x ∈ W \ T, ∑ y ∈ T \ W,
            harmonic #(insert y (W \ {x}) ∩ inst.approves i) := by
      simpa using
        (Finset.sum_comm (s := W \ T) (t := inst.voters)
          (f := fun x i => ∑ y ∈ T \ W, harmonic #(insert y (W \ {x}) ∩ inst.approves i)))
    exact h1.trans h2

  -- Rewrite the constant term as a sum over voters.
  have hConst :
      (↑(#(W \ T)) : ℚ) * ((↑(#(T \ W)) : ℚ) * ∑ i ∈ inst.voters, harmonic #(W ∩ inst.approves i)) =
        ∑ i ∈ inst.voters,
          (↑(#(W \ T)) : ℚ) * ((↑(#(T \ W)) : ℚ) * harmonic #(W ∩ inst.approves i)) := by
    -- push the multipliers inside the voter sum
    have hY :
        (↑(#(T \ W)) : ℚ) * ∑ i ∈ inst.voters, harmonic #(W ∩ inst.approves i) =
          ∑ i ∈ inst.voters, (↑(#(T \ W)) : ℚ) * harmonic #(W ∩ inst.approves i) := by
      simpa using
        (Finset.mul_sum (s := inst.voters) (f := fun i => harmonic #(W ∩ inst.approves i))
          (a := (↑(#(T \ W)) : ℚ)))
    -- now multiply by `#(W \ T)` and push in again
    calc
      (↑(#(W \ T)) : ℚ) * ((↑(#(T \ W)) : ℚ) * ∑ i ∈ inst.voters, harmonic #(W ∩ inst.approves i))
          = (↑(#(W \ T)) : ℚ) * (∑ i ∈ inst.voters,
              (↑(#(T \ W)) : ℚ) * harmonic #(W ∩ inst.approves i)) := by
              simp [hY]
      _ = ∑ i ∈ inst.voters, (↑(#(W \ T)) : ℚ) *
            ((↑(#(T \ W)) : ℚ) * harmonic #(W ∩ inst.approves i)) := by
            simpa [mul_assoc] using
              (Finset.mul_sum (s := inst.voters)
                (f := fun i => (↑(#(T \ W)) : ℚ) * harmonic #(W ∩ inst.approves i))
                (a := (↑(#(W \ T)) : ℚ)))

  -- Combine everything into a single voter-wise sum.
  rw [hTriple, hConst, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi

  -- Convert the constant product into a double sum, then apply `sum_sub_distrib`.
  have hConst2 :
      (↑(#(W \ T)) : ℚ) * ((↑(#(T \ W)) : ℚ) * harmonic #(W ∩ inst.approves i)) =
        ∑ x ∈ W \ T, ∑ y ∈ T \ W, harmonic #(W ∩ inst.approves i) := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  -- Reduce to the sum of harmonic differences for voter `i`.
  have hDiff :
      (∑ x ∈ W \ T, ∑ y ∈ T \ W, harmonic #(insert y (W \ {x}) ∩ inst.approves i)) -
          (↑(#(W \ T)) : ℚ) * ((↑(#(T \ W)) : ℚ) * harmonic #(W ∩ inst.approves i)) =
        ∑ x ∈ W \ T, ∑ y ∈ T \ W,
          (harmonic #(insert y (W \ {x}) ∩ inst.approves i) - harmonic #(W ∩ inst.approves i)) := by
    -- rewrite the constant as a sum over all pairs and use distributivity of `∑` over `-`
    rw [hConst2]
    -- turn `A - B` into a sum of differences by applying `sum_sub_distrib` twice
    -- (first over `x`, then over `y`)
    have :
        (∑ x ∈ W \ T, ∑ y ∈ T \ W, harmonic #(insert y (W \ {x}) ∩ inst.approves i)) -
            (∑ x ∈ W \ T, ∑ y ∈ T \ W, harmonic #(W ∩ inst.approves i)) =
          ∑ x ∈ W \ T, ((∑ y ∈ T \ W, harmonic #(insert y (W \ {x}) ∩ inst.approves i)) -
            (∑ y ∈ T \ W, harmonic #(W ∩ inst.approves i))) := by
      simpa [Finset.sum_sub_distrib]
        using (Finset.sum_sub_distrib (s := W \ T)
          (f := fun x => ∑ y ∈ T \ W, harmonic #(insert y (W \ {x}) ∩ inst.approves i))
          (g := fun x => ∑ y ∈ T \ W, harmonic #(W ∩ inst.approves i))).symm
    -- expand the inner difference over `y`
    calc
      (∑ x ∈ W \ T, ∑ y ∈ T \ W, harmonic #(insert y (W \ {x}) ∩ inst.approves i)) -
          (∑ x ∈ W \ T, ∑ y ∈ T \ W, harmonic #(W ∩ inst.approves i))
          = ∑ x ∈ W \ T, ((∑ y ∈ T \ W, harmonic #(insert y (W \ {x}) ∩ inst.approves i)) -
              (∑ y ∈ T \ W, harmonic #(W ∩ inst.approves i))) := this
      _ = ∑ x ∈ W \ T, ∑ y ∈ T \ W,
            (harmonic #(insert y (W \ {x}) ∩ inst.approves i) - harmonic #(W ∩ inst.approves i)) := by
          apply Finset.sum_congr rfl
          intro x hx
          simpa [Finset.sum_sub_distrib]
            using (Finset.sum_sub_distrib (s := T \ W)
              (f := fun y => harmonic #(insert y (W \ {x}) ∩ inst.approves i))
              (g := fun _y => harmonic #(W ∩ inst.approves i))).symm

  -- Now compute the double sum explicitly; this is exactly `delta_voter`.
  -- Abbreviations matching the `delta_voter` definition.
  set Ai : Finset C := inst.approves i
  set a : ℕ := ((W \ T) ∩ Ai).card
  set b : ℕ := ((W ∩ T) ∩ Ai).card
  set c : ℕ := ((T \ W) ∩ Ai).card
  set u : ℕ := (W ∩ Ai).card
  have hu : u = a + b := by
    -- this is just the partition of `W ∩ Ai` into `(W \ T) ∩ Ai` and `(W ∩ T) ∩ Ai`
    simpa [utility, Ai, a, b, u] using (utility_eq_a_plus_b inst W T i)

  -- Split the swap sum into the two nontrivial cases:
  -- (x not approved, y approved) gives +1/(u+1),
  -- (x approved, y not approved) gives -1/u.
  have hMain :
      (∑ x ∈ W \ T, ∑ y ∈ T \ W,
          (harmonic #(insert y (W \ {x}) ∩ inst.approves i) - harmonic #(W ∩ inst.approves i))) =
        delta_A (W \ T).card (T \ W).card a b c := by
    -- Define the local difference function.
    let diff : C → C → ℚ := fun x y =>
      harmonic #(insert y (W \ {x}) ∩ Ai) - harmonic u
    have hdiff_rw :
        (∑ x ∈ W \ T, ∑ y ∈ T \ W,
            (harmonic #(insert y (W \ {x}) ∩ inst.approves i) - harmonic #(W ∩ inst.approves i))) =
          ∑ x ∈ W \ T, ∑ y ∈ T \ W, diff x y := by
      simp [diff, Ai, u]
    rw [hdiff_rw]

    -- Helpers for the two harmonic increments.
    have hInc : harmonic (u + 1) - harmonic u = 1 / (u + 1) := by
      simpa using (harmonic_succ_sub u)
    have hDec : harmonic (u - 1) - harmonic u = - (1 / u) := by
      by_cases hu0 : u = 0
      · simp [hu0, harmonic, sub_eq_add_neg]
      · have hu1 : 1 ≤ u := by
          -- `u ≠ 0` implies `0 < u` and hence `1 ≤ u`
          have : 0 < u := Nat.pos_of_ne_zero hu0
          simpa using (Nat.succ_le_iff.2 this)
        have hu_eq : (u - 1) + 1 = u := Nat.sub_add_cancel hu1
        have h' := harmonic_succ_sub (u - 1)
        -- `harmonic u - harmonic (u-1) = 1/u`
        have hu_eq_rat : ((u - 1 : ℕ) : ℚ) + 1 = (u : ℚ) := by
          have := congrArg (fun n : ℕ => (n : ℚ)) hu_eq
          simpa [Nat.cast_add, Nat.cast_one] using this
        have h'' : harmonic u - harmonic (u - 1) = 1 / (((u - 1 : ℕ) : ℚ) + 1) := by
          simpa [hu_eq] using h'
        have : harmonic u - harmonic (u - 1) = 1 / u := by
          simpa [hu_eq_rat] using h''
        -- rearrange
        linarith

    -- Use filters to count the relevant swap pairs.
    let X : Finset C := W \ T
    let Y : Finset C := T \ W
    let Xyes : Finset C := X.filter (fun x => x ∈ Ai)
    let Xno : Finset C := X.filter (fun x => x ∉ Ai)
    let Yyes : Finset C := Y.filter (fun y => y ∈ Ai)
    let Yno : Finset C := Y.filter (fun y => y ∉ Ai)

    have hXyes : Xyes = X ∩ Ai := by
      simpa [Xyes, Finset.filter_mem_eq_inter, X, Ai]
    have hYyes : Yyes = Y ∩ Ai := by
      simpa [Yyes, Finset.filter_mem_eq_inter, Y, Ai]

    have hXyes_card : Xyes.card = a := by
      simpa [hXyes, X, a]
    have hYyes_card : Yyes.card = c := by
      simpa [hYyes, Y, c]

    have hXsplit :
        Xyes.card + Xno.card = X.card := by
      simpa [Xyes, Xno] using (Finset.filter_card_add_filter_neg_card_eq_card (s := X) (p := fun x => x ∈ Ai))
    have hYsplit :
        Yyes.card + Yno.card = Y.card := by
      simpa [Yyes, Yno] using (Finset.filter_card_add_filter_neg_card_eq_card (s := Y) (p := fun y => y ∈ Ai))

    have hXno_card : Xno.card = X.card - a := by
      -- from `Xyes.card + Xno.card = X.card`
      have h : Xno.card + a = X.card := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, hXyes_card] using hXsplit
      exact Nat.eq_sub_of_add_eq h
    have hYno_card : Yno.card = Y.card - c := by
      have h : Yno.card + c = Y.card := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, hYyes_card] using hYsplit
      exact Nat.eq_sub_of_add_eq h

    -- Compute the value of `diff` on the two relevant regions.
    have hdiff_inc :
        ∀ {x y}, x ∈ Xno → y ∈ Yyes → diff x y = 1 / (u + 1) := by
      intro x y hx hy
      have hxX : x ∈ X := (Finset.mem_filter.mp hx).1
      have hxA : x ∉ Ai := (Finset.mem_filter.mp hx).2
      have hyY : y ∈ Y := (Finset.mem_filter.mp hy).1
      have hyA : y ∈ Ai := (Finset.mem_filter.mp hy).2
      have hyW : y ∉ W := (Finset.mem_sdiff.mp hyY).2
      have hy_not_in : y ∉ (W \ {x}) := by
        intro hy'
        exact hyW (Finset.mem_sdiff.mp hy').1
      have hremove :
          #((W \ {x}) ∩ Ai) = u := by
        -- removing `x` does not change the intersection since `x ∉ Ai`
        have hx_not : x ∉ W ∩ Ai := by
          have hxW : x ∈ W := (Finset.mem_sdiff.mp hxX).1
          simpa [Finset.mem_inter, hxW, hxA]
        -- `(W \ {x}) ∩ Ai = (W ∩ Ai) \ {x}`
        have hEq : (W \ {x}) ∩ Ai = (W ∩ Ai) \ {x} := by
          ext z
          simp [Finset.mem_inter, Finset.mem_sdiff, and_left_comm, and_assoc, and_comm]
        -- and `x` is not in `W ∩ Ai`, so the erase is unchanged
        have : (W ∩ Ai) \ {x} = (W ∩ Ai) := by
          simpa [Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem hx_not]
        simpa [u, hEq, this]
      -- inserting an approved `y` (not already present) increases the count by 1
      have hcard :
          #(insert y (W \ {x}) ∩ Ai) = u + 1 := by
        have hEq : insert y (W \ {x}) ∩ Ai = insert y ((W \ {x}) ∩ Ai) := by
          simpa [Finset.insert_inter_of_mem hyA]
        have hy_not2 : y ∉ ((W \ {x}) ∩ Ai) := by
          intro hy'
          exact hy_not_in (Finset.mem_inter.mp hy').1
        simpa [hEq, hremove, Finset.card_insert_of_notMem hy_not2, add_comm, add_left_comm, add_assoc]
      -- conclude
      simp [diff, u, hcard, hInc]

    have hdiff_dec :
        ∀ {x y}, x ∈ Xyes → y ∈ Yno → diff x y = - (1 / u) := by
      intro x y hx hy
      have hxX : x ∈ X := (Finset.mem_filter.mp hx).1
      have hxA : x ∈ Ai := (Finset.mem_filter.mp hx).2
      have hyY : y ∈ Y := (Finset.mem_filter.mp hy).1
      have hyA : y ∉ Ai := (Finset.mem_filter.mp hy).2
      have hxW : x ∈ W := (Finset.mem_sdiff.mp hxX).1
      -- y not approved, so inserting it doesn't change the intersection with `Ai`
      have hEqIns : insert y (W \ {x}) ∩ Ai = (W \ {x}) ∩ Ai := by
        simpa [Finset.insert_inter_of_notMem hyA]
      -- removing an approved `x` decreases by 1
      have hremove :
          #((W \ {x}) ∩ Ai) = u - 1 := by
        have hx_mem : x ∈ W ∩ Ai := by simpa [Finset.mem_inter, hxW, hxA]
        have hEq : (W \ {x}) ∩ Ai = (W ∩ Ai) \ {x} := by
          ext z
          simp [Finset.mem_inter, Finset.mem_sdiff, and_left_comm, and_assoc, and_comm]
        -- rewrite to erase and use `card_erase_of_mem`
        have : ((W ∩ Ai) \ {x}).card = u - 1 := by
          simp [Finset.sdiff_singleton_eq_erase, u, Finset.card_erase_of_mem hx_mem]
        simpa [hEq] using this
      have hcard :
          #(insert y (W \ {x}) ∩ Ai) = u - 1 := by
        simpa [hEqIns] using hremove
      simp [diff, u, hcard, hDec]

    -- The other two regions have zero net effect.
    have hdiff_zero₁ :
        ∀ {x y}, x ∈ Xyes → y ∈ Yyes → diff x y = 0 := by
      intro x y hx hy
      have hxX : x ∈ X := (Finset.mem_filter.mp hx).1
      have hxA : x ∈ Ai := (Finset.mem_filter.mp hx).2
      have hyY : y ∈ Y := (Finset.mem_filter.mp hy).1
      have hyA : y ∈ Ai := (Finset.mem_filter.mp hy).2
      have hyW : y ∉ W := (Finset.mem_sdiff.mp hyY).2
      have hy_not_in : y ∉ (W \ {x}) := by
        intro hy'
        exact hyW (Finset.mem_sdiff.mp hy').1
      have hxW : x ∈ W := (Finset.mem_sdiff.mp hxX).1
      have hx_mem : x ∈ W ∩ Ai := by simpa [Finset.mem_inter, hxW, hxA]
      have hEq1 : (W \ {x}) ∩ Ai = (W ∩ Ai) \ {x} := by
        ext z
        simp [Finset.mem_inter, Finset.mem_sdiff, and_left_comm, and_assoc, and_comm]
      have hremove : #((W \ {x}) ∩ Ai) = u - 1 := by
        simpa [hEq1, Finset.sdiff_singleton_eq_erase, u, Finset.card_erase_of_mem hx_mem]
      have hEq2 : insert y (W \ {x}) ∩ Ai = insert y ((W \ {x}) ∩ Ai) := by
        simpa [Finset.insert_inter_of_mem hyA]
      have hy_not2 : y ∉ ((W \ {x}) ∩ Ai) := by
        intro hy'
        exact hy_not_in (Finset.mem_inter.mp hy').1
      have hcard :
          #(insert y (W \ {x}) ∩ Ai) = u := by
        have hu_pos : 1 ≤ u := by
          have : 0 < u := Finset.card_pos.mpr ⟨x, hx_mem⟩
          simpa using (Nat.succ_le_iff.2 this)
        have hu_eq : (u - 1) + 1 = u := Nat.sub_add_cancel hu_pos
        have hins :
            #(insert y (W \ {x}) ∩ Ai) = #((W \ {x}) ∩ Ai) + 1 := by
          have hEq : insert y (W \ {x}) ∩ Ai = insert y ((W \ {x}) ∩ Ai) := by
            simpa [Finset.insert_inter_of_mem hyA]
          simpa [hEq] using (Finset.card_insert_of_notMem hy_not2)
        calc
          #(insert y (W \ {x}) ∩ Ai)
              = #((W \ {x}) ∩ Ai) + 1 := hins
          _ = (u - 1) + 1 := by simpa [hremove]
          _ = u := by simpa [hu_eq]
      simp [diff, u, hcard]

    have hdiff_zero₂ :
        ∀ {x y}, x ∈ Xno → y ∈ Yno → diff x y = 0 := by
      intro x y hx hy
      have hxX : x ∈ X := (Finset.mem_filter.mp hx).1
      have hxA : x ∉ Ai := (Finset.mem_filter.mp hx).2
      have hyY : y ∈ Y := (Finset.mem_filter.mp hy).1
      have hyA : y ∉ Ai := (Finset.mem_filter.mp hy).2
      -- neither removal nor insertion affects `Ai`-intersection
      have hEqIns : insert y (W \ {x}) ∩ Ai = (W \ {x}) ∩ Ai := by
        simpa [Finset.insert_inter_of_notMem hyA]
      have hremove :
          #((W \ {x}) ∩ Ai) = u := by
        have hx_not : x ∉ W ∩ Ai := by
          have hxW : x ∈ W := (Finset.mem_sdiff.mp hxX).1
          simpa [Finset.mem_inter, hxW, hxA]
        have hEq : (W \ {x}) ∩ Ai = (W ∩ Ai) \ {x} := by
          ext z
          simp [Finset.mem_inter, Finset.mem_sdiff, and_left_comm, and_assoc, and_comm]
        have : (W ∩ Ai) \ {x} = (W ∩ Ai) := by
          simpa [Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem hx_not]
        simpa [u, hEq, this]
      have hcard : #(insert y (W \ {x}) ∩ Ai) = u := by
        simpa [hEqIns] using hremove
      simp [diff, u, hcard]

    -- Put the four regions together and evaluate the constant sums.
    have hSplitX :
        (∑ x ∈ X, ∑ y ∈ Y, diff x y) =
          (∑ x ∈ Xyes, ∑ y ∈ Yyes, diff x y) +
          (∑ x ∈ Xyes, ∑ y ∈ Yno, diff x y) +
          (∑ x ∈ Xno, ∑ y ∈ Yyes, diff x y) +
          (∑ x ∈ Xno, ∑ y ∈ Yno, diff x y) := by
      -- expand `X` into approved/nonapproved, then expand `Y` similarly
      -- (uses disjoint union decomposition for `filter`/`filter ¬`)
      have hX : Xyes ∪ Xno = X := by
        simpa [Xyes, Xno] using (Finset.filter_union_filter_neg_eq (s := X) (p := fun x => x ∈ Ai))
      have hXdisj : Disjoint Xyes Xno := by
        simpa [Xyes, Xno] using
          (Finset.disjoint_filter_filter_neg (s := X) (t := X) (p := fun x => x ∈ Ai))
      have hY : Yyes ∪ Yno = Y := by
        simpa [Yyes, Yno] using (Finset.filter_union_filter_neg_eq (s := Y) (p := fun y => y ∈ Ai))
      have hYdisj : Disjoint Yyes Yno := by
        simpa [Yyes, Yno] using
          (Finset.disjoint_filter_filter_neg (s := Y) (t := Y) (p := fun y => y ∈ Ai))
      -- Split the outer sum over `Xyes ∪ Xno`.
      rw [← hX]
      rw [Finset.sum_union hXdisj]
      -- Split the inner `Y`-sum in each branch and distribute.
      have hYsplit' :
          ∀ x, (∑ y ∈ Y, diff x y) = (∑ y ∈ Yyes, diff x y) + (∑ y ∈ Yno, diff x y) := by
        intro x
        rw [← hY]
        simpa [Finset.sum_union hYdisj, add_assoc, add_comm, add_left_comm]
      -- Apply the `Y` split and distribute over `+`.
      simp [hYsplit', Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

    -- Evaluate each block.
    rw [hSplitX]
    have hYY : (∑ x ∈ Xyes, ∑ y ∈ Yyes, diff x y) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      refine Finset.sum_eq_zero ?_
      intro y hy
      exact hdiff_zero₁ hx hy
    have hNN : (∑ x ∈ Xno, ∑ y ∈ Yno, diff x y) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      refine Finset.sum_eq_zero ?_
      intro y hy
      exact hdiff_zero₂ hx hy

    have hIncSum :
        (∑ x ∈ Xno, ∑ y ∈ Yyes, diff x y) =
          (Xno.card : ℚ) * ((Yyes.card : ℚ) * (1 / (↑u + 1))) := by
      have hInner :
          ∀ x ∈ Xno, (∑ y ∈ Yyes, diff x y) = (Yyes.card : ℚ) * (1 / (↑u + 1)) := by
        intro x hx
        have :
            (∑ y ∈ Yyes, diff x y) = ∑ y ∈ Yyes, ((1 : ℚ) / (↑u + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          simp [hdiff_inc hx hy]
        simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc] using this
      -- now the outer sum is constant as well
      have :
          (∑ x ∈ Xno, ∑ y ∈ Yyes, diff x y) =
            ∑ x ∈ Xno, (Yyes.card : ℚ) * (1 / (↑u + 1)) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        simpa using hInner x hx
      -- sum a constant over `Xno`
      simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using this

    have hDecSum :
        (∑ x ∈ Xyes, ∑ y ∈ Yno, diff x y) =
          (Xyes.card : ℚ) * ((Yno.card : ℚ) * (-(1 / (u : ℚ)))) := by
      have hInner :
          ∀ x ∈ Xyes, (∑ y ∈ Yno, diff x y) = (Yno.card : ℚ) * (-(1 / (u : ℚ))) := by
        intro x hx
        have :
            (∑ y ∈ Yno, diff x y) = ∑ y ∈ Yno, (-(1 / (u : ℚ))) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          simp [hdiff_dec hx hy]
        simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc] using this
      have :
          (∑ x ∈ Xyes, ∑ y ∈ Yno, diff x y) =
            ∑ x ∈ Xyes, (Yno.card : ℚ) * (-(1 / (u : ℚ))) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        simpa using hInner x hx
      simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using this

    -- Finish the arithmetic: only the `(+1)` and `(-1)` blocks contribute.
    -- Rewrite card equalities and `u = a + b`, then match `delta_A`.
    -- 1. Establish inequalities to handle Nat subtraction casting to Rat
    have ha_le : a ≤ X.card := by
      rw [←hXyes_card]
      exact Finset.card_le_card (Finset.filter_subset _ _)

    have hc_le : c ≤ Y.card := by
      rw [←hYyes_card]
      exact Finset.card_le_card (Finset.filter_subset _ _)

    -- 2. Simplify, explicitly adding Nat.cast_sub to handle the subtraction
    simp [hYY, hNN, hIncSum, hDecSum, hXyes_card, hYyes_card, hXno_card, hYno_card,
      hu, delta_A, X, Y, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, sub_eq_add_neg, Nat.cast_sub ha_le, Nat.cast_sub hc_le]

    -- 3. Solve the resulting Rational ring equality
    ring

  -- Finish: the computed delta is exactly `delta_voter`.
  rw [hDiff]
  -- unfold `delta_voter` to match `hMain`
  simpa [delta_voter, delta_A, Ai, a, b, c, u] using hMain

-- ============================================================================
-- MAIN THEOREM
-- ============================================================================

/--
For a local PAV committee W, the sum of deltas over all voters is ≤ 0.
-/
lemma delta_sum_nonpos_of_local_pav (inst : ABCInstance V C k) (W T : Finset C)
    (hW : inst.is_local_pav_winner W) (hT_sub : T ⊆ inst.candidates) :
    ∑ i ∈ inst.voters, delta_voter inst W T i ≤ 0 := by
  rw [← swapping_sum_eq_delta_sum]
  apply Finset.sum_nonpos
  intro x hx
  apply Finset.sum_nonpos
  intro y hy
  have hx' : x ∈ W := (mem_sdiff.mp hx).1
  have hy_T : y ∈ T := (mem_sdiff.mp hy).1
  have hy_W : y ∉ W := (mem_sdiff.mp hy).2
  have hy' : y ∈ inst.candidates \ W := by
    rw [mem_sdiff]
    exact ⟨hT_sub hy_T, hy_W⟩
  have := hW.2.2 x hx' y hy'
  linarith

/--
**Main Theorem**: Local PAV committees are in the core when k ≤ 7.
-/
theorem local_pav_in_core (inst : ABCInstance V C k) (W : Finset C)
    (hW : inst.is_local_pav_winner W) (hk : k ≤ 7) :
    inst.is_in_core W := by
  intro S T l hS_sub hT_sub hl ⟨h_large, hT_card⟩
  -- We need to find a voter in S who doesn't strictly prefer T to W
  by_contra h_all_prefer
  push_neg at h_all_prefer
  -- All voters in S strictly prefer T to W
  have h_prefers : ∀ i ∈ S, prefers inst i T W := by
    intro i hi
    have h := h_all_prefer i hi
    simpa [prefers, gt_iff_lt, utility] using h
  -- Sum of deltas is ≤ 0
  have h_sum_le : ∑ i ∈ inst.voters, delta_voter inst W T i ≤ 0 :=
    delta_sum_nonpos_of_local_pav inst W T hW hT_sub
  classical
  have hW_card : W.card = k := hW.2.1
  have hS_nonempty : S.Nonempty := l_large_nonempty inst S l hl h_large
  obtain ⟨i0, hi0S⟩ := hS_nonempty
  have hT_nonempty : T.Nonempty := by
    have h0 : inst.utility T i0 > 0 := by
      have := h_prefers i0 hi0S
      exact lt_of_le_of_lt (Nat.zero_le _) this
    -- `utility T i0 ≤ T.card`
    have hle : inst.utility T i0 ≤ T.card := by
      unfold utility
      exact card_le_card (inter_subset_left)
    exact card_pos.mp (lt_of_lt_of_le h0 hle)
  have hT_size : 1 ≤ T.card := by
    have : 0 < T.card := card_pos.mpr hT_nonempty
    simpa using (Nat.succ_le_iff.2 this)

  -- From ℓ-large and `S ⊆ voters`, we get `l ≤ k` and hence `T.card ≤ k`.
  have hS_card_le : S.card ≤ inst.voters.card := card_le_card hS_sub
  have hn_pos : 0 < inst.voters.card := card_pos.mpr inst.voters_nonempty
  have hl_le_k : l ≤ k := by
    have hmul : inst.voters.card * l ≤ inst.voters.card * k := by
      have : l * inst.voters.card ≤ inst.voters.card * k := by
        calc
          l * inst.voters.card ≤ S.card * k := h_large
          _ ≤ inst.voters.card * k := Nat.mul_le_mul_right k hS_card_le
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    exact Nat.le_of_mul_le_mul_left hmul hn_pos
  have hT_le_k : T.card ≤ k := le_trans hT_card hl_le_k

  -- `T \\ W` is nonempty, hence `(W ∩ T).card < T.card`.
  have hTW_nonempty : (T \ W).Nonempty := by
    have hca0 : ((T \ W) ∩ inst.approves i0).card > 0 := by
      have hca : ((T \ W) ∩ inst.approves i0).card >
          ((W \ T) ∩ inst.approves i0).card :=
        (prefers_iff_c_gt_a inst W T i0).mp (h_prefers i0 hi0S)
      exact lt_of_le_of_lt (Nat.zero_le _) hca
    exact nonempty_iff_ne_empty.2 (by
      intro hE
      simp [hE] at hca0)
  have hWT_disj : (W ∩ T).card < T.card := by
    obtain ⟨y, hy⟩ := hTW_nonempty
    have hyT : y ∈ T := (mem_sdiff.mp hy).1
    have hyW : y ∉ W := (mem_sdiff.mp hy).2
    have hss : W ∩ T ⊂ T := by
      refine (ssubset_iff_subset_ne).2 ?_
      refine ⟨inter_subset_right, ?_⟩
      intro hEq
      have hyWT : y ∈ W ∩ T := by simpa [hEq] using hyT
      exact hyW (Finset.mem_inter.mp hyWT).1
    exact Finset.card_lt_card hss

  -- We now lower-bound the total sum of deltas using:
  -- - voters in S: δ_i > core_rhs
  -- - voters outside S: δ_i ≥ -|T \\ W|
  let tMinus : ℕ := (T \ W).card
  let rhs : ℚ := core_rhs k T.card tMinus

  have hDeltaS : ∀ i ∈ S, delta_voter inst W T i > rhs := by
    intro i hi
    have hi_pref : prefers inst i T W := h_prefers i hi
    rcases lt_or_eq_of_le hT_le_k with hT_lt | hT_eq
    · exact delta_voter_of_prefers inst W T i hW_card hT_size hT_lt hk hWT_disj hi_pref
    · -- Here `T.card = k`, so `rhs = 0` and we just need `δ_i > 0`.
      have hpos : delta_voter inst W T i > 0 :=
        delta_voter_pos_of_prefers_same_size inst W T i hW_card hT_eq hi_pref
      -- simplify `rhs`
      have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt inst.k_pos)
      have : rhs = 0 := by
        subst rhs
        simp [core_rhs, hT_eq, hk0]
      simpa [this] using hpos

  have hSumS : (∑ i ∈ S, rhs) < ∑ i ∈ S, delta_voter inst W T i := by
    refine Finset.sum_lt_sum ?_ ?_
    · intro i hi
      exact (hDeltaS i hi).le
    · exact ⟨i0, hi0S, hDeltaS i0 hi0S⟩

  have hSumComp : (∑ i ∈ inst.voters \ S, (-(tMinus : ℚ))) ≤
      ∑ i ∈ inst.voters \ S, delta_voter inst W T i := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have := delta_voter_ge_neg inst W T i
    -- `-(tMinus : ℚ) ≤ δ_i`
    simpa [tMinus] using this

  have hSplit :
      (∑ i ∈ inst.voters, delta_voter inst W T i) =
        (∑ i ∈ S, delta_voter inst W T i) + (∑ i ∈ inst.voters \ S, delta_voter inst W T i) := by
    have hDisj : Disjoint S (inst.voters \ S) := disjoint_sdiff
    have hUnion : S ∪ (inst.voters \ S) = inst.voters := union_sdiff_of_subset hS_sub
    -- `sum_union` gives a sum over `S ∪ (voters \\ S)`, so rewrite that union to `voters`.
    simpa [hUnion] using (Finset.sum_union hDisj (f := fun i => delta_voter inst W T i))

  have hTotalPos : (0 : ℚ) < ∑ i ∈ inst.voters, delta_voter inst W T i := by
    -- combine the S and complement estimates
    have hAdd :
        (∑ i ∈ S, rhs) + (∑ i ∈ inst.voters \ S, (-(tMinus : ℚ))) <
          (∑ i ∈ S, delta_voter inst W T i) + (∑ i ∈ inst.voters \ S, delta_voter inst W T i) :=
      add_lt_add_of_lt_of_le hSumS hSumComp
    have hLeft :
        0 ≤ (∑ i ∈ S, rhs) + (∑ i ∈ inst.voters \ S, (-(tMinus : ℚ))) := by
      have hS_const : (∑ _i ∈ S, rhs) = (S.card : ℚ) * rhs := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      have hComp_const :
          (∑ _i ∈ inst.voters \ S, (-(tMinus : ℚ))) =
            ((inst.voters \ S).card : ℚ) * (-(tMinus : ℚ)) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      have htminus_nonneg : (0 : ℚ) ≤ (tMinus : ℚ) := Nat.cast_nonneg _

      -- From ℓ-large and `T.card ≤ l`, we get `n * |T| ≤ |S| * k`.
      have hNat : inst.voters.card * T.card ≤ S.card * k := by
        have h1 : inst.voters.card * T.card ≤ inst.voters.card * l :=
          Nat.mul_le_mul_left inst.voters.card hT_card
        have h2 : inst.voters.card * l ≤ S.card * k := by
          -- unfold `is_l_large`: `l * n ≤ |S| * k`
          simpa [ABCInstance.is_l_large, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h_large
        exact h1.trans h2
      have hRat : (inst.voters.card : ℚ) * (T.card : ℚ) ≤ (S.card : ℚ) * (k : ℚ) := by
        exact_mod_cast hNat
      have hTposQ : (0 : ℚ) < (T.card : ℚ) := by
        exact_mod_cast (card_pos.mpr hT_nonempty)
      have hTne : (T.card : ℚ) ≠ 0 := ne_of_gt hTposQ

      -- Turn `n * |T| ≤ |S| * k` into `n ≤ |S| * k / |T|`.
      have hn_le : (inst.voters.card : ℚ) ≤ (S.card : ℚ) * (k : ℚ) / T.card := by
        have hinv_nonneg : (0 : ℚ) ≤ (T.card : ℚ)⁻¹ := inv_nonneg.2 hTposQ.le
        have hRat' := mul_le_mul_of_nonneg_right hRat hinv_nonneg
        -- simplify `(n * t) * t⁻¹` and `(|S|*k) * t⁻¹`
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hTne] using hRat'

      have hcoef_nonneg : (0 : ℚ) ≤ (S.card : ℚ) * (k : ℚ) / T.card - inst.voters.card := by
        linarith

      -- Express the constant lower bound as `tMinus * ((|S|*k/|T|) - n)`.
      have hSsub' : S.card ≤ inst.voters.card := hS_card_le
      have hcard_sdiff : ((inst.voters \ S).card : ℚ) = (inst.voters.card : ℚ) - S.card := by
        have : (inst.voters \ S).card = inst.voters.card - S.card :=
          card_sdiff_of_subset hS_sub
        simpa [this, Nat.cast_sub hSsub'] using congrArg (fun n : ℕ => (n : ℚ)) this

      -- Now finish by arithmetic.
      subst rhs
      have :
          (S.card : ℚ) * core_rhs k T.card tMinus +
              ((inst.voters \ S).card : ℚ) * (-(tMinus : ℚ))
            =
          (tMinus : ℚ) * ((S.card : ℚ) * (k : ℚ) / T.card - inst.voters.card) := by
        simp [core_rhs, hcard_sdiff, div_eq_mul_inv, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
        ring
      -- `tMinus ≥ 0` and the coefficient is ≥ 0.
      rw [hS_const, hComp_const, this]
      exact mul_nonneg htminus_nonneg hcoef_nonneg
    -- conclude positivity of the total delta sum
    have hRHS : (∑ i ∈ S, delta_voter inst W T i) + (∑ i ∈ inst.voters \ S, delta_voter inst W T i) =
        ∑ i ∈ inst.voters, delta_voter inst W T i := by
      simpa [hSplit] using (Eq.symm hSplit)
    have : (0 : ℚ) < (∑ i ∈ S, delta_voter inst W T i) + (∑ i ∈ inst.voters \ S, delta_voter inst W T i) :=
      lt_of_le_of_lt hLeft hAdd
    simpa [hRHS] using this

  linarith

/--
**Corollary**: Global PAV winners are in the core when k ≤ 7.
-/
theorem pav_winner_in_core (inst : ABCInstance V C k) (W : Finset C)
    (hW : inst.is_pav_winner W) (hk : k ≤ 7) :
    inst.is_in_core W :=
  local_pav_in_core inst W (global_pav_is_local inst W hW) hk

end ABCInstance
