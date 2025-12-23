/-
# Counterexamples for PAV

This file contains counterexamples showing that PAV (Proportional Approval Voting)
does not satisfy certain properties in general.

## Main Results
- `pav_not_in_core_k8`: PAV may fail the core property when k = 8

## References
- The counterexample is from: "The Core of Approval-Based Committee Elections with
  Few Candidates" by Dominik Peters.
-/

import ABCVoting.Rules.PAV.Defs
import ABCVoting.Axioms.Core
import ABCVoting.Axioms.Priceability

open Finset BigOperators

-- ============================================================================
-- COUNTEREXAMPLE: PAV FAILS CORE FOR k = 8
-- ============================================================================

/-!
## The Counterexample Instance

Consider an instance with:
- 4 voters: v₁, v₂, v₃, v₄
- 10 candidates: c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉, c₁₀
- k = 8

Approval profile:
- v₁ approves {c₁, c₂, c₃}
- v₂ approves {c₁, c₂, c₄}
- v₃ approves {c₅, c₆, c₇, c₈, c₉, c₁₀}
- v₄ approves {c₅, c₆, c₇, c₈, c₉, c₁₀}

The committee W = {c₁, c₂, c₅, c₆, c₇, c₈, c₉, c₁₀} is a PAV winner (size 8).

However, W is not in the core: Consider T = {c₁, c₂, c₃, c₄} with the supporting
coalition S = {v₁, v₂}. We have:
- |S|/n = 2/4 = 1/2
- |T|/k = 4/8 = 1/2
- So S is 4-large (since 4 × 4 ≤ 2 × 8)
- For v₁: utility(W) = 2 < utility(T) = 3
- For v₂: utility(W) = 2 < utility(T) = 3
- Both voters in S strictly prefer T to W, so W is not in the core.
-/

namespace PAVCounterexamples

-- ============================================================================
-- SETUP: CONCRETE TYPES
-- ============================================================================

/-- Voters are indexed 0, 1, 2, 3 (representing v₁, v₂, v₃, v₄). -/
abbrev Voter := Fin 4

/-- Candidates are indexed 0-9 (representing c₁, c₂, ..., c₁₀). -/
abbrev Candidate := Fin 10

/-- The committee size for this counterexample. -/
def k : ℕ := 8

-- ============================================================================
-- THE APPROVAL PROFILE
-- ============================================================================

/--
The approval function for the counterexample.
- v₀ (v₁) approves {c₀, c₁, c₂} (i.e., c₁, c₂, c₃)
- v₁ (v₂) approves {c₀, c₁, c₃} (i.e., c₁, c₂, c₄)
- v₂ (v₃) approves {c₄, c₅, c₆, c₇, c₈, c₉} (i.e., c₅, c₆, c₇, c₈, c₉, c₁₀)
- v₃ (v₄) approves {c₄, c₅, c₆, c₇, c₈, c₉} (same as v₃)
-/
def approves : Voter → Finset Candidate
  | ⟨0, _⟩ => {0, 1, 2}       -- v₁ approves c₁, c₂, c₃
  | ⟨1, _⟩ => {0, 1, 3}       -- v₂ approves c₁, c₂, c₄
  | ⟨2, _⟩ => {4, 5, 6, 7, 8, 9}  -- v₃ approves c₅, c₆, c₇, c₈, c₉, c₁₀
  | ⟨3, _⟩ => {4, 5, 6, 7, 8, 9}  -- v₄ approves c₅, c₆, c₇, c₈, c₉, c₁₀

/-- All voters. -/
def voters : Finset Voter := Finset.univ

/-- All candidates. -/
def candidates : Finset Candidate := Finset.univ

-- ============================================================================
-- THE ABC INSTANCE
-- ============================================================================

lemma approves_subset (v : Voter) (_ : v ∈ voters) : approves v ⊆ candidates := by
  intro c _
  exact Finset.mem_univ c

lemma voters_nonempty : voters.Nonempty := by
  use 0
  exact Finset.mem_univ 0

lemma k_pos : 0 < k := by norm_num [k]

lemma k_le_m : k ≤ candidates.card := by
  simp only [k, candidates, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- The ABC instance for the counterexample. -/
def inst : ABCInstance Voter Candidate k where
  voters := voters
  candidates := candidates
  approves := approves
  approves_subset := approves_subset
  voters_nonempty := voters_nonempty
  k_pos := k_pos
  k_le_m := k_le_m

-- ============================================================================
-- THE COMMITTEE W (CLAIMED PAV WINNER)
-- ============================================================================

/-- The committee W = {c₁, c₂, c₅, c₆, c₇, c₈, c₉, c₁₀} (indices 0, 1, 4, 5, 6, 7, 8, 9). -/
def W : Finset Candidate := {0, 1, 4, 5, 6, 7, 8, 9}

lemma W_subset_candidates : W ⊆ candidates := by
  intro c _
  exact Finset.mem_univ c

lemma W_card : W.card = k := by decide

-- ============================================================================
-- THE BLOCKING COALITION
-- ============================================================================

/-- The blocking coalition T = {c₁, c₂, c₃, c₄} (indices 0, 1, 2, 3). -/
def T : Finset Candidate := {0, 1, 2, 3}

/-- The supporting voter set S = {v₁, v₂} (indices 0, 1). -/
def S : Finset Voter := {0, 1}

lemma T_subset_candidates : T ⊆ candidates := by
  intro c _
  exact Finset.mem_univ c

lemma S_subset_voters : S ⊆ voters := by
  intro v _
  exact Finset.mem_univ v

lemma T_card : T.card = 4 := by decide

lemma S_card : S.card = 2 := by decide

-- ============================================================================
-- UTILITIES COMPUTATION
-- ============================================================================

/-- v₁'s utility from W is 2 (approves c₁, c₂). -/
lemma utility_W_v0 : inst.utility W 0 = 2 := by decide

/-- v₁'s utility from T is 3 (approves c₁, c₂, c₃). -/
lemma utility_T_v0 : inst.utility T 0 = 3 := by decide

/-- v₂'s utility from W is 2 (approves c₁, c₂). -/
lemma utility_W_v1 : inst.utility W 1 = 2 := by decide

/-- v₂'s utility from T is 3 (approves c₁, c₂, c₄). -/
lemma utility_T_v1 : inst.utility T 1 = 3 := by decide

-- ============================================================================
-- S IS 4-LARGE
-- ============================================================================

/-- S is 4-large: 4 × 4 ≤ 2 × 8. -/
lemma S_is_4_large : inst.is_l_large S 4 := by
  unfold ABCInstance.is_l_large
  simp only [inst, voters, S_card]
  simp only [Finset.card_univ, Fintype.card_fin, k]
  norm_num

-- ============================================================================
-- CORE VIOLATION
-- ============================================================================

/-- All voters in S strictly prefer T to W. -/
lemma all_S_prefer_T : ∀ v ∈ S, inst.utility T v > inst.utility W v := by
  intro v hv
  -- S = {0, 1}, so v is either 0 or 1
  simp only [S, mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl
  · -- v = 0
    simp only [utility_T_v0, utility_W_v0]
    norm_num
  · -- v = 1
    simp only [utility_T_v1, utility_W_v1]
    norm_num

/--
W is not in the core.

Proof: The coalition S = {v₁, v₂} is 4-large, T = {c₁, c₂, c₃, c₄} has size 4,
and all voters in S strictly prefer T to W (utility 3 vs 2).
-/
theorem W_not_in_core : ¬inst.is_in_core W := by
  intro h_core
  -- Apply the core definition with S, T, l = 4
  have h := h_core S T 4 S_subset_voters T_subset_candidates (by norm_num)
    ⟨S_is_4_large, by simp only [T_card]; norm_num⟩
  -- This gives us some voter in S who weakly prefers W to T
  obtain ⟨v, hv_in_S, hv_util⟩ := h
  -- But all voters in S strictly prefer T to W
  have hv_prefer := all_S_prefer_T v hv_in_S
  -- The core condition says (W ∩ approves v).card ≥ (T ∩ approves v).card
  -- But utility is defined as (W ∩ approves v).card
  -- So hv_util says: inst.utility W v ≥ inst.utility T v
  -- And hv_prefer says: inst.utility T v > inst.utility W v
  -- This is a contradiction
  unfold ABCInstance.utility at hv_prefer
  simp only [inst] at hv_util hv_prefer
  omega

-- PAV SCORE COMPUTATION (for verification)
-- ============================================================================

/-- Helper: compute harmonic number as a rational. -/
noncomputable def H (n : ℕ) : ℚ := ABCInstance.harmonic n

/-- H(2) = 3/2. -/
lemma H_2 : H 2 = 3/2 := by
  simp only [H, ABCInstance.harmonic]
  norm_num [Finset.sum_range_succ]

/-- H(6) = 49/20. -/
lemma H_6 : H 6 = 49/20 := by
  simp only [H, ABCInstance.harmonic]
  norm_num [Finset.sum_range_succ]

/-- PAV score of W. -/
lemma pav_score_W : inst.pav_score W = 79/10 := by
  simp only [ABCInstance.pav_score, inst, voters]
  rw [Fin.sum_univ_four]
  -- Compute each intersection cardinality
  have h0 : (W ∩ approves 0).card = 2 := by decide
  have h1 : (W ∩ approves 1).card = 2 := by decide
  have h2 : (W ∩ approves 2).card = 6 := by decide
  have h3 : (W ∩ approves 3).card = 6 := by decide
  simp only [h0, h1, h2, h3]
  -- Use harmonic values: H(2) = 3/2, H(6) = 49/20
  have hH2 : ABCInstance.harmonic 2 = 3/2 := by
    simp only [ABCInstance.harmonic]
    norm_num [Finset.sum_range_succ]
  have hH6 : ABCInstance.harmonic 6 = 49/20 := by
    simp only [ABCInstance.harmonic]
    norm_num [Finset.sum_range_succ]
  simp only [hH2, hH6]
  -- 3/2 + 3/2 + 49/20 + 49/20 = 3 + 49/10 = 79/10
  norm_num

-- ============================================================================
-- W IS A PAV WINNER
-- ============================================================================

/--
The set D of candidates approved by voters v₃ and v₄.
D = {c₅, c₆, c₇, c₈, c₉, c₁₀} = {4, 5, 6, 7, 8, 9}
-/
def D : Finset Candidate := {4, 5, 6, 7, 8, 9}

lemma D_card : D.card = 6 := by decide

/--
The complement of D within candidates.
Dᶜ = {c₁, c₂, c₃, c₄} = {0, 1, 2, 3}
-/
def Dc : Finset Candidate := {0, 1, 2, 3}

lemma Dc_card : Dc.card = 4 := by decide

lemma D_union_Dc : D ∪ Dc = candidates := by
  ext x
  simp only [mem_union, candidates, mem_univ, iff_true]
  fin_cases x <;> simp [D, Dc]

lemma D_inter_Dc : D ∩ Dc = ∅ := by decide

/--
For any size-8 committee W', the intersection with D has cardinality in {4, 5, 6}.
-/
lemma W'_inter_D_card_range (W' : Finset Candidate) (hW'_sub : W' ⊆ candidates)
    (hW'_card : W'.card = 8) : (W' ∩ D).card ∈ ({4, 5, 6} : Finset ℕ) := by
  have hDc_bound : (W' ∩ Dc).card ≤ 4 := by
    calc (W' ∩ Dc).card ≤ Dc.card := card_le_card inter_subset_right
      _ = 4 := Dc_card
  have hD_bound : (W' ∩ D).card ≤ 6 := by
    calc (W' ∩ D).card ≤ D.card := card_le_card inter_subset_right
      _ = 6 := D_card
  -- W' = (W' ∩ D) ∪ (W' ∩ Dc) since W' ⊆ D ∪ Dc = candidates
  have hW'_split : W' = (W' ∩ D) ∪ (W' ∩ Dc) := by
    ext x
    simp only [mem_union, mem_inter]
    constructor
    · intro hx
      have hx_cand : x ∈ candidates := hW'_sub hx
      rw [← D_union_Dc] at hx_cand
      simp only [mem_union] at hx_cand
      rcases hx_cand with hD | hDc
      · left; exact ⟨hx, hD⟩
      · right; exact ⟨hx, hDc⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hDisj : Disjoint (W' ∩ D) (W' ∩ Dc) := by
    rw [disjoint_iff_inter_eq_empty]
    have h : (W' ∩ D) ∩ (W' ∩ Dc) ⊆ D ∩ Dc := by
      intro x hx
      simp only [mem_inter] at hx ⊢
      exact ⟨hx.1.2, hx.2.2⟩
    rw [D_inter_Dc] at h
    exact Finset.subset_empty.mp h
  have hCard : (W' ∩ D).card + (W' ∩ Dc).card = 8 := by
    have heq : W' ∩ D ∪ W' ∩ Dc = W' := by
      rw [← hW'_split]
    rw [← card_union_of_disjoint hDisj, heq, hW'_card]
  -- From hCard and hDc_bound: (W' ∩ D).card ≥ 4
  have hD_lower : 4 ≤ (W' ∩ D).card := by omega
  -- Combined with hD_bound: (W' ∩ D).card ∈ {4, 5, 6}
  simp only [mem_insert, mem_singleton]
  omega

-- ============================================================================
-- PRICEABILITY VIOLATION
-- ============================================================================

lemma D_subset_W : D ⊆ W := by decide

lemma supporters_c2 : inst.supporters 2 = {0} := by decide

lemma supporters_c3 : inst.supporters 3 = {1} := by decide

theorem W_not_priceable : ¬inst.is_priceable W := by
  intro h_priceable
  rcases h_priceable with ⟨b, p, hb, hprice⟩
  rcases hprice with ⟨hvalid, hexhaust⟩
  rcases hvalid with ⟨hnonneg, happr, hbudget, helect, hnonelect⟩
  -- Sum of payments for candidates c₅..c₁₀ equals 6.
  have hDsum : (∑ c ∈ D, p.total_payment inst c) = 6 := by
    have hDpay : ∀ c ∈ D, p.total_payment inst c = 1 := by
      intro c hc
      exact helect c (D_subset_W hc)
    calc
      ∑ c ∈ D, p.total_payment inst c = ∑ c ∈ D, (1 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro c hc
        exact hDpay c hc
      _ = (D.card : ℝ) := by simp
      _ = 6 := by simp [D_card]
  -- For c ∈ D, only voters 2 and 3 can pay (C1).
  have hD_total (c : Candidate) (hc : c ∈ D) :
      p.total_payment inst c = p 2 c + p 3 c := by
    have hdisj0 : Disjoint D (approves 0) := by decide
    have hdisj1 : Disjoint D (approves 1) := by decide
    have h0 : p 0 c = 0 := by
      apply ABCInstance.PriceSystem.payment_zero_of_not_approved p inst 0 c
      · simp [inst, voters]
      · exact (Finset.disjoint_left.mp hdisj0) hc
      · exact happr
    have h1 : p 1 c = 0 := by
      apply ABCInstance.PriceSystem.payment_zero_of_not_approved p inst 1 c
      · simp [inst, voters]
      · exact (Finset.disjoint_left.mp hdisj1) hc
      · exact happr
    -- Expand the total payment over all voters.
    simp [ABCInstance.PriceSystem.total_payment, inst, voters, h0, h1, Fin.sum_univ_four]
  -- Use within-budget bounds for voters 2 and 3 to get b ≥ 3.
  have hsum_le :
      (∑ c ∈ D, p.total_payment inst c) ≤ 2 * b := by
    have hsumD :
        ∑ c ∈ D, p.total_payment inst c = ∑ c ∈ D, (p 2 c + p 3 c) := by
      refine Finset.sum_congr rfl ?_
      intro c hc
      exact hD_total c hc
    have hD_sub_candidates : D ⊆ inst.candidates := by
      intro c _
      exact Finset.mem_univ c
    have hsum2_le : ∑ c ∈ D, p 2 c ≤ p.spending inst 2 := by
      have h_disj : Disjoint D (inst.candidates \ D) := by
        exact disjoint_sdiff
      have h_union : D ∪ (inst.candidates \ D) = inst.candidates := by
        simpa [Finset.union_sdiff_of_subset hD_sub_candidates]
      have hsum :
          ∑ c ∈ inst.candidates, p 2 c =
            ∑ c ∈ D, p 2 c + ∑ c ∈ inst.candidates \ D, p 2 c := by
        have hsum_union := (Finset.sum_union (s₁ := D) (s₂ := inst.candidates \ D)
          (f := fun c => p 2 c) h_disj)
        simpa [h_union] using hsum_union
      have h_nonneg : 0 ≤ ∑ c ∈ inst.candidates \ D, p 2 c := by
        apply Finset.sum_nonneg
        intro c hc
        exact hnonneg 2 (by simp [inst, voters]) c
      unfold ABCInstance.PriceSystem.spending
      linarith [hsum, h_nonneg]
    have hsum3_le : ∑ c ∈ D, p 3 c ≤ p.spending inst 3 := by
      have h_disj : Disjoint D (inst.candidates \ D) := by
        exact disjoint_sdiff
      have h_union : D ∪ (inst.candidates \ D) = inst.candidates := by
        simpa [Finset.union_sdiff_of_subset hD_sub_candidates]
      have hsum :
          ∑ c ∈ inst.candidates, p 3 c =
            ∑ c ∈ D, p 3 c + ∑ c ∈ inst.candidates \ D, p 3 c := by
        have hsum_union := (Finset.sum_union (s₁ := D) (s₂ := inst.candidates \ D)
          (f := fun c => p 3 c) h_disj)
        simpa [h_union] using hsum_union
      have h_nonneg : 0 ≤ ∑ c ∈ inst.candidates \ D, p 3 c := by
        apply Finset.sum_nonneg
        intro c hc
        exact hnonneg 3 (by simp [inst, voters]) c
      unfold ABCInstance.PriceSystem.spending
      linarith [hsum, h_nonneg]
    have hbudget2 : p.spending inst 2 ≤ b := hbudget 2 (by simp [inst, voters])
    have hbudget3 : p.spending inst 3 ≤ b := hbudget 3 (by simp [inst, voters])
    have hsum2_le_b : ∑ c ∈ D, p 2 c ≤ b := le_trans hsum2_le hbudget2
    have hsum3_le_b : ∑ c ∈ D, p 3 c ≤ b := le_trans hsum3_le hbudget3
    calc
      ∑ c ∈ D, p.total_payment inst c
          = ∑ c ∈ D, (p 2 c + p 3 c) := hsumD
      _ = (∑ c ∈ D, p 2 c) + (∑ c ∈ D, p 3 c) := by
        simp [Finset.sum_add_distrib]
      _ ≤ b + b := by linarith
      _ = 2 * b := by ring
  have hb_ge : (3 : ℝ) ≤ b := by
    linarith [hDsum, hsum_le]
  -- C5 for c₃ (index 2) and c₄ (index 3) gives spending bounds for voters 0 and 1.
  have h_unspent0_le : p.unspent inst b 0 ≤ 1 := by
    have hmem : (2 : Candidate) ∈ inst.candidates \ W := by
      simp [inst, candidates, W]
    have h := hexhaust 2 hmem
    simpa [supporters_c2] using h
  have h_unspent1_le : p.unspent inst b 1 ≤ 1 := by
    have hmem : (3 : Candidate) ∈ inst.candidates \ W := by
      simp [inst, candidates, W]
    have h := hexhaust 3 hmem
    simpa [supporters_c3] using h
  have h_spend0_ge : b - 1 ≤ p.spending inst 0 := by
    unfold ABCInstance.PriceSystem.unspent at h_unspent0_le
    linarith
  have h_spend1_ge : b - 1 ≤ p.spending inst 1 := by
    unfold ABCInstance.PriceSystem.unspent at h_unspent1_le
    linarith
  -- Voters 0 and 1 can only pay for candidates 0 and 1, so their total spending is 2.
  have hsum01 : p.spending inst 0 + p.spending inst 1 = 2 := by
    have h2_not0 : (0 : Candidate) ∉ approves 2 := by decide
    have h2_not1 : (1 : Candidate) ∉ approves 2 := by decide
    have h3_not0 : (0 : Candidate) ∉ approves 3 := by decide
    have h3_not1 : (1 : Candidate) ∉ approves 3 := by decide
    have hp0_2 : p 0 2 = 0 := by
      have hmem : (2 : Candidate) ∈ inst.candidates \ W := by
        simp [inst, candidates, W]
      have htot := hnonelect 2 hmem
      have h1 : p 1 2 = 0 := by
        apply ABCInstance.PriceSystem.payment_zero_of_not_approved p inst 1 2
        · simp [inst, voters]
        · decide
        · exact happr
      have h2 : p 2 2 = 0 := by
        apply ABCInstance.PriceSystem.payment_zero_of_not_approved p inst 2 2
        · simp [inst, voters]
        · decide
        · exact happr
      have h3 : p 3 2 = 0 := by
        apply ABCInstance.PriceSystem.payment_zero_of_not_approved p inst 3 2
        · simp [inst, voters]
        · decide
        · exact happr
      -- total payment is zero, so all individual payments are zero
      have htot' : p 0 2 + p 1 2 + p 2 2 + p 3 2 = 0 := by
        simpa [ABCInstance.PriceSystem.total_payment, inst, voters, Fin.sum_univ_four,
          h1, h2, h3] using htot
      linarith
    have hp1_3 : p 1 3 = 0 := by
      have hmem : (3 : Candidate) ∈ inst.candidates \ W := by
        simp [inst, candidates, W]
      have htot := hnonelect 3 hmem
      have h0 : p 0 3 = 0 := by
        apply ABCInstance.PriceSystem.payment_zero_of_not_approved p inst 0 3
        · simp [inst, voters]
        · decide
        · exact happr
      have h2 : p 2 3 = 0 := by
        apply ABCInstance.PriceSystem.payment_zero_of_not_approved p inst 2 3
        · simp [inst, voters]
        · decide
        · exact happr
      have h3 : p 3 3 = 0 := by
        apply ABCInstance.PriceSystem.payment_zero_of_not_approved p inst 3 3
        · simp [inst, voters]
        · decide
        · exact happr
      have htot' : p 0 3 + p 1 3 + p 2 3 + p 3 3 = 0 := by
        simpa [ABCInstance.PriceSystem.total_payment, inst, voters, Fin.sum_univ_four,
          h0, h2, h3] using htot
      linarith
    have htot0 : p.total_payment inst 0 = 1 := by
      exact helect 0 (by decide)
    have htot1 : p.total_payment inst 1 = 1 := by
      exact helect 1 (by decide)
    have hpay2_0 : p 2 0 = 0 := by
      apply ABCInstance.PriceSystem.payment_zero_of_not_approved p inst 2 0
      · simp [inst, voters]
      · exact h2_not0
      · exact happr
    have hpay3_0 : p 3 0 = 0 := by
      apply ABCInstance.PriceSystem.payment_zero_of_not_approved p inst 3 0
      · simp [inst, voters]
      · exact h3_not0
      · exact happr
    have hpay2_1 : p 2 1 = 0 := by
      apply ABCInstance.PriceSystem.payment_zero_of_not_approved p inst 2 1
      · simp [inst, voters]
      · exact h2_not1
      · exact happr
    have hpay3_1 : p 3 1 = 0 := by
      apply ABCInstance.PriceSystem.payment_zero_of_not_approved p inst 3 1
      · simp [inst, voters]
      · exact h3_not1
      · exact happr
    have htot0' : p 0 0 + p 1 0 = 1 := by
      have h := htot0
      simpa [ABCInstance.PriceSystem.total_payment, inst, voters, Fin.sum_univ_four,
        hpay2_0, hpay3_0] using h
    have htot1' : p 0 1 + p 1 1 = 1 := by
      have h := htot1
      simpa [ABCInstance.PriceSystem.total_payment, inst, voters, Fin.sum_univ_four,
        hpay2_1, hpay3_1] using h
    have hspend0 :
        p.spending inst 0 = p 0 0 + p 0 1 := by
      unfold ABCInstance.PriceSystem.spending
      have hsub : approves 0 ⊆ inst.candidates :=
        inst.approves_subset 0 (by simp [inst, voters])
      have hsum := (Finset.sum_subset (f := fun c => p 0 c) hsub ?_).symm
      · calc
          ∑ c ∈ inst.candidates, p 0 c
              = ∑ c ∈ approves 0, p 0 c := hsum
          _ = p 0 0 + p 0 1 + p 0 2 := by simp [approves, add_assoc]
          _ = p 0 0 + p 0 1 := by simp [hp0_2]
      · intro c hc hnot
        exact happr 0 (by simp [inst, voters]) c hnot
    have hspend1 :
        p.spending inst 1 = p 1 0 + p 1 1 := by
      unfold ABCInstance.PriceSystem.spending
      have hsub : approves 1 ⊆ inst.candidates :=
        inst.approves_subset 1 (by simp [inst, voters])
      have hsum := (Finset.sum_subset (f := fun c => p 1 c) hsub ?_).symm
      · calc
          ∑ c ∈ inst.candidates, p 1 c
              = ∑ c ∈ approves 1, p 1 c := hsum
          _ = p 1 0 + p 1 1 + p 1 3 := by simp [approves, add_assoc]
          _ = p 1 0 + p 1 1 := by simp [hp1_3]
      · intro c hc hnot
        exact happr 1 (by simp [inst, voters]) c hnot
    calc
      p.spending inst 0 + p.spending inst 1
          = (p 0 0 + p 0 1) + (p 1 0 + p 1 1) := by
            simp [hspend0, hspend1]
      _ = (p 0 0 + p 1 0) + (p 0 1 + p 1 1) := by ring
      _ = 1 + 1 := by simp [htot0', htot1']
      _ = 2 := by ring
  -- Combine bounds to get the contradiction b ≥ 3 and b ≤ 2.
  have hb_le : b ≤ 2 := by
    linarith [h_spend0_ge, h_spend1_ge, hsum01]
  linarith

/--
Harmonic H(5) = 137/60.
-/
lemma harmonic_5 : ABCInstance.harmonic 5 = 137/60 := by
  simp only [ABCInstance.harmonic]
  norm_num [Finset.sum_range_succ]

/--
Harmonic H(4) = 25/12.
-/
lemma harmonic_4 : ABCInstance.harmonic 4 = 25/12 := by
  simp only [ABCInstance.harmonic]
  norm_num [Finset.sum_range_succ]

/--
Harmonic H(3) = 11/6.
-/
lemma harmonic_3 : ABCInstance.harmonic 3 = 11/6 := by
  simp only [ABCInstance.harmonic]
  norm_num [Finset.sum_range_succ]

/--
Harmonic H(1) = 1.
-/
lemma harmonic_1 : ABCInstance.harmonic 1 = 1 := by
  simp only [ABCInstance.harmonic]
  norm_num [Finset.sum_range_succ]

/--
Harmonic H(0) = 0.
-/
lemma harmonic_0 : ABCInstance.harmonic 0 = 0 := by
  simp only [ABCInstance.harmonic, Finset.sum_range_zero]

/--
The harmonic function is monotone.
-/
lemma harmonic_mono' {a b : ℕ} (h : a ≤ b) : ABCInstance.harmonic a ≤ ABCInstance.harmonic b :=
  ABCInstance.harmonic_mono h

/--
Key bound: For voters v₂ and v₃, utility from W' equals |W' ∩ D|.
-/
lemma utility_v2_eq_D_inter (W' : Finset Candidate) :
    (W' ∩ approves 2).card = (W' ∩ D).card := by
  congr 1  -- Sets are definitionally equal

lemma utility_v3_eq_D_inter (W' : Finset Candidate) :
    (W' ∩ approves 3).card = (W' ∩ D).card := by
  congr 1  -- Sets are definitionally equal

/--
Upper bound on utility for v₀: at most 3.
-/
lemma utility_v0_le_3 (W' : Finset Candidate) : (W' ∩ approves 0).card ≤ 3 := by
  calc (W' ∩ approves 0).card ≤ (approves 0).card := card_le_card inter_subset_right
    _ = 3 := by decide

/--
Upper bound on utility for v₁: at most 3.
-/
lemma utility_v1_le_3 (W' : Finset Candidate) : (W' ∩ approves 1).card ≤ 3 := by
  calc (W' ∩ approves 1).card ≤ (approves 1).card := card_le_card inter_subset_right
    _ = 3 := by decide

/--
Harmonic H(6) = 49/20 = 147/60.
-/
lemma harmonic_6_alt : ABCInstance.harmonic 6 = 147/60 := by
  simp only [ABCInstance.harmonic]
  norm_num [Finset.sum_range_succ]

/--
Harmonic H(2) = 3/2 = 90/60.
-/
lemma harmonic_2_alt : ABCInstance.harmonic 2 = 90/60 := by
  simp only [ABCInstance.harmonic]
  norm_num [Finset.sum_range_succ]

/--
W is a PAV winner: it has maximal PAV score among all size-k committees.

Proof strategy: For any committee W' with |W'| = 8, let d = |W' ∩ D| where
D = {4,5,6,7,8,9}. We have d ∈ {4, 5, 6}.

The PAV score is: H(u₀) + H(u₁) + 2·H(d) where u₀, u₁ ≤ 3.

- If d = 6: score ≤ 2·H(3) + 2·H(6) = 22/6 + 294/60 = 514/60.
  But W achieves 2·H(2) + 2·H(6) = 79/10 = 474/60 when u₀ = u₁ = 2.
  Actually the max with d=6 needs u₀ + u₁ + d ≤ 8 constraint...

The key observation is that H is concave (diminishing returns), so spreading
approval across more candidates is suboptimal compared to concentrating it.
-/
theorem W_is_pav_winner : inst.is_pav_winner W := by
  unfold ABCInstance.is_pav_winner
  refine ⟨W_subset_candidates, W_card, ?_⟩
  intro W' hW'_sub hW'_card
  -- Expand PAV scores
  simp only [ABCInstance.pav_score, inst, voters]
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  -- Use the D-intersection characterization for v₂ and v₃
  rw [utility_v2_eq_D_inter, utility_v3_eq_D_inter]
  -- Get the range of d = |W' ∩ D|
  have hd_range := W'_inter_D_card_range W' hW'_sub hW'_card
  set d := (W' ∩ D).card with hd_def
  -- Also set up utilities for v₀ and v₁
  set u0 := (W' ∩ approves 0).card with hu0_def
  set u1 := (W' ∩ approves 1).card with hu1_def
  -- Upper bounds on u₀ and u₁
  have hu0_le : u0 ≤ 3 := utility_v0_le_3 W'
  have hu1_le : u1 ≤ 3 := utility_v1_le_3 W'
  -- The score of W
  have hW_inter_0 : (W ∩ approves 0).card = 2 := by decide
  have hW_inter_1 : (W ∩ approves 1).card = 2 := by decide
  have hW_inter_2 : (W ∩ approves 2).card = 6 := by decide
  have hW_inter_3 : (W ∩ approves 3).card = 6 := by decide
  simp only [hW_inter_0, hW_inter_1, hW_inter_2, hW_inter_3]
  -- We need to show: H(u0) + H(u1) + 2*H(d) ≤ 2*H(2) + 2*H(6)
  -- Case analysis on d ∈ {4, 5, 6}
  simp only [mem_insert, mem_singleton] at hd_range
  -- Upper bound on H(d) using monotonicity
  have hu0_bound : ABCInstance.harmonic u0 ≤ ABCInstance.harmonic 3 :=
    harmonic_mono' hu0_le
  have hu1_bound : ABCInstance.harmonic u1 ≤ ABCInstance.harmonic 3 :=
    harmonic_mono' hu1_le
  have hd_bound : ABCInstance.harmonic d ≤ ABCInstance.harmonic 6 := by
    apply harmonic_mono'
    rcases hd_range with hd4 | hd5 | hd6 <;> omega
  -- The bound: H(u0) + H(u1) + 2*H(d) ≤ 2*H(3) + 2*H(6)
  have hH3 : ABCInstance.harmonic 3 = 11/6 := harmonic_3
  have hH6 : ABCInstance.harmonic 6 = 49/20 := by
    simp only [ABCInstance.harmonic]
    norm_num [Finset.sum_range_succ]
  have hH2 : ABCInstance.harmonic 2 = 3/2 := by
    simp only [ABCInstance.harmonic]
    norm_num [Finset.sum_range_succ]
  -- The RHS = 2*H(2) + 2*H(6) = 79/10
  -- The upper bound = 2*H(3) + 2*H(6) = 22/6 + 49/10 = 110/30 + 147/30 = 257/30
  -- But 257/30 > 79/10 = 237/30, so we need a tighter bound!
  -- Actually the issue is that when d = 6, we must have u0 + u1 ≤ 2 (not 6)
  -- Let me use interval_cases to handle each case properly
  rcases hd_range with hd4 | hd5 | hd6
  · -- Case d = 4
    simp only [hd4]
    calc ABCInstance.harmonic u0 + ABCInstance.harmonic u1 +
            ABCInstance.harmonic 4 + ABCInstance.harmonic 4
        ≤ ABCInstance.harmonic 3 + ABCInstance.harmonic 3 +
            ABCInstance.harmonic 4 + ABCInstance.harmonic 4 := by linarith
      _ = 11/6 + 11/6 + 25/12 + 25/12 := by rw [harmonic_3, harmonic_4]
      _ = 47/6 := by norm_num
      _ ≤ 79/10 := by norm_num
      _ = 3/2 + 3/2 + 49/20 + 49/20 := by norm_num
      _ = _ := by rw [hH2, hH6]
  · -- Case d = 5: |W' ∩ Dc| = 3
    simp only [hd5]
    -- When d = 5, W' has exactly 3 from {0,1,2,3}
    -- Best case: {0,1,2} or {0,1,3} gives H(3) + H(2) + 2*H(5) = 79/10
    have hDc_card : (W' ∩ Dc).card = 3 := by
      have hCard : (W' ∩ D).card + (W' ∩ Dc).card = 8 := by
        have hDisj : Disjoint (W' ∩ D) (W' ∩ Dc) := by
          rw [disjoint_iff_inter_eq_empty]
          have h : (W' ∩ D) ∩ (W' ∩ Dc) ⊆ D ∩ Dc := by
            intro x hx
            simp only [mem_inter] at hx ⊢
            exact ⟨hx.1.2, hx.2.2⟩
          rw [D_inter_Dc] at h
          exact Finset.subset_empty.mp h
        have hW'_split : W' = (W' ∩ D) ∪ (W' ∩ Dc) := by
          ext x
          simp only [mem_union, mem_inter]
          constructor
          · intro hx
            have hx_cand : x ∈ candidates := hW'_sub hx
            rw [← D_union_Dc] at hx_cand
            simp only [mem_union] at hx_cand
            rcases hx_cand with hD | hDc
            · left; exact ⟨hx, hD⟩
            · right; exact ⟨hx, hDc⟩
          · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
        have heq : W' ∩ D ∪ W' ∩ Dc = W' := by rw [← hW'_split]
        rw [← card_union_of_disjoint hDisj, heq, hW'_card]
        rfl
      omega
    -- u0 ≤ 3 and u1 ≤ 3, and u0 + u1 ≤ |W' ∩ Dc| + |W' ∩ {0,1}| = 3 + |W' ∩ {0,1}|
    -- Actually: approves 0 ∩ approves 1 = {0, 1}
    -- Better bound: H(u0) + H(u1) ≤ H(3) + H(2) when |W' ∩ Dc| = 3
    -- Since at most one of u0, u1 can be 3 (the third element from Dc is 2 or 3, not both)
    -- If 2 ∈ W', then u0 gets +1, u1 doesn't. If 3 ∈ W', then u1 gets +1, u0 doesn't.
    -- So max(u0, u1) = 3 implies min(u0, u1) ≤ 2
    have hu_sum_bound : ABCInstance.harmonic u0 + ABCInstance.harmonic u1 ≤
        ABCInstance.harmonic 3 + ABCInstance.harmonic 2 := by
      -- The intersection of approves 0 and approves 1 is {0, 1}
      -- approves 0 \ approves 1 = {2}, approves 1 \ approves 0 = {3}
      -- So u0 = |W' ∩ {0,1}| + (1 if 2 ∈ W' else 0)
      -- And u1 = |W' ∩ {0,1}| + (1 if 3 ∈ W' else 0)
      -- With |W' ∩ Dc| = 3, the elements from Dc are some subset of size 3 from {0,1,2,3}
      -- Cases: {0,1,2}, {0,1,3}, {0,2,3}, {1,2,3}
      -- - {0,1,2}: u0 = 3, u1 = 2
      -- - {0,1,3}: u0 = 2, u1 = 3
      -- - {0,2,3}: u0 = 2, u1 = 2
      -- - {1,2,3}: u0 = 2, u1 = 2
      -- In all cases H(u0) + H(u1) ≤ H(3) + H(2)
      have hmax : max u0 u1 ≤ 3 := max_le hu0_le hu1_le
      by_cases h01 : (0 : Candidate) ∈ W' ∧ (1 : Candidate) ∈ W'
      · -- Both 0 and 1 in W'
        -- Then at most one of 2, 3 is in W' (since |W' ∩ Dc| = 3)
        have h_either : ¬((2 : Candidate) ∈ W' ∧ (3 : Candidate) ∈ W') := by
          intro ⟨h2, h3⟩
          have hfour : ({0, 1, 2, 3} : Finset Candidate) ⊆ W' ∩ Dc := by
            intro x hx
            simp only [mem_inter, Dc, mem_insert, mem_singleton] at hx ⊢
            rcases hx with rfl | rfl | rfl | rfl
            · exact ⟨h01.1, Or.inl rfl⟩
            · exact ⟨h01.2, Or.inr (Or.inl rfl)⟩
            · exact ⟨h2, Or.inr (Or.inr (Or.inl rfl))⟩
            · exact ⟨h3, Or.inr (Or.inr (Or.inr rfl))⟩
          have hcard4 : 4 ≤ (W' ∩ Dc).card := by
            calc 4 = ({0, 1, 2, 3} : Finset Candidate).card := by decide
              _ ≤ (W' ∩ Dc).card := card_le_card hfour
          omega
        rcases not_and_or.mp h_either with h2_not | h3_not
        · -- 2 ∉ W': u0 = 2, u1 ≤ 3
          have hu0_eq : u0 = 2 := by
            have h_sub : W' ∩ approves 0 ⊆ {0, 1} := by
              intro x hx
              simp only [mem_inter, approves, mem_insert, mem_singleton] at hx ⊢
              rcases hx.2 with rfl | rfl | rfl
              · left; rfl
              · right; rfl
              · exact absurd hx.1 h2_not
            have h_sup : {0, 1} ⊆ W' ∩ approves 0 := by
              intro x hx
              simp only [mem_insert, mem_singleton] at hx
              simp only [mem_inter, approves, mem_insert, mem_singleton]
              rcases hx with rfl | rfl
              · exact ⟨h01.1, Or.inl rfl⟩
              · exact ⟨h01.2, Or.inr (Or.inl rfl)⟩
            have heq : W' ∩ approves 0 = {0, 1} := Finset.Subset.antisymm h_sub h_sup
            simp only [hu0_def, heq]
            decide
          calc ABCInstance.harmonic u0 + ABCInstance.harmonic u1
              = ABCInstance.harmonic 2 + ABCInstance.harmonic u1 := by rw [hu0_eq]
            _ ≤ ABCInstance.harmonic 2 + ABCInstance.harmonic 3 := by
                apply add_le_add_left (harmonic_mono' hu1_le)
            _ = ABCInstance.harmonic 3 + ABCInstance.harmonic 2 := by ring
        · -- 3 ∉ W': u0 ≤ 3, u1 = 2
          have hu1_eq : u1 = 2 := by
            have h_sub : W' ∩ approves 1 ⊆ {0, 1} := by
              intro x hx
              simp only [mem_inter, approves, mem_insert, mem_singleton] at hx ⊢
              rcases hx.2 with rfl | rfl | rfl
              · left; rfl
              · right; rfl
              · exact absurd hx.1 h3_not
            have h_sup : {0, 1} ⊆ W' ∩ approves 1 := by
              intro x hx
              simp only [mem_insert, mem_singleton] at hx
              simp only [mem_inter, approves, mem_insert, mem_singleton]
              rcases hx with rfl | rfl
              · exact ⟨h01.1, Or.inl rfl⟩
              · exact ⟨h01.2, Or.inr (Or.inl rfl)⟩
            have heq : W' ∩ approves 1 = {0, 1} := Finset.Subset.antisymm h_sub h_sup
            simp only [hu1_def, heq]
            decide
          calc ABCInstance.harmonic u0 + ABCInstance.harmonic u1
              = ABCInstance.harmonic u0 + ABCInstance.harmonic 2 := by rw [hu1_eq]
            _ ≤ ABCInstance.harmonic 3 + ABCInstance.harmonic 2 := by
                apply add_le_add_right (harmonic_mono' hu0_le)
      · -- Not both 0 and 1 in W'
        -- Then u0 ≤ 2 and u1 ≤ 2
        push_neg at h01
        have hu0_le2 : u0 ≤ 2 := by
          by_cases h0 : (0 : Candidate) ∈ W'
          · -- 0 ∈ W' but 1 ∉ W'
            have h1_not := h01 h0
            calc u0 = (W' ∩ approves 0).card := rfl
              _ ≤ ({0, 2} : Finset Candidate).card := by
                apply card_le_card
                intro x hx
                simp only [mem_inter, approves, mem_insert, mem_singleton] at hx ⊢
                rcases hx.2 with rfl | rfl | rfl
                · left; rfl
                · exact absurd hx.1 h1_not
                · right; rfl
              _ = 2 := by decide
          · -- 0 ∉ W'
            calc u0 = (W' ∩ approves 0).card := rfl
              _ ≤ ({1, 2} : Finset Candidate).card := by
                apply card_le_card
                intro x hx
                simp only [mem_inter, approves, mem_insert, mem_singleton] at hx ⊢
                rcases hx.2 with rfl | rfl | rfl
                · exact absurd hx.1 h0
                · left; rfl
                · right; rfl
              _ = 2 := by decide
        have hu1_le2 : u1 ≤ 2 := by
          by_cases h1 : (1 : Candidate) ∈ W'
          · -- 1 ∈ W' but 0 ∉ W'
            have h0_not : (0 : Candidate) ∉ W' := fun h0 => h01 h0 h1
            calc u1 = (W' ∩ approves 1).card := rfl
              _ ≤ ({1, 3} : Finset Candidate).card := by
                apply card_le_card
                intro x hx
                simp only [mem_inter, approves, mem_insert, mem_singleton] at hx ⊢
                rcases hx.2 with rfl | rfl | rfl
                · exact absurd hx.1 h0_not
                · left; rfl
                · right; rfl
              _ = 2 := by decide
          · -- 1 ∉ W'
            calc u1 = (W' ∩ approves 1).card := rfl
              _ ≤ ({0, 3} : Finset Candidate).card := by
                apply card_le_card
                intro x hx
                simp only [mem_inter, approves, mem_insert, mem_singleton] at hx ⊢
                rcases hx.2 with rfl | rfl | rfl
                · left; rfl
                · exact absurd hx.1 h1
                · right; rfl
              _ = 2 := by decide
        calc ABCInstance.harmonic u0 + ABCInstance.harmonic u1
            ≤ ABCInstance.harmonic 2 + ABCInstance.harmonic 2 := by
              apply add_le_add (harmonic_mono' hu0_le2) (harmonic_mono' hu1_le2)
          _ ≤ ABCInstance.harmonic 3 + ABCInstance.harmonic 2 := by
              apply add_le_add_right
              exact harmonic_mono' (by norm_num : (2 : ℕ) ≤ 3)
    calc ABCInstance.harmonic u0 + ABCInstance.harmonic u1 +
            ABCInstance.harmonic 5 + ABCInstance.harmonic 5
        ≤ ABCInstance.harmonic 3 + ABCInstance.harmonic 2 +
            ABCInstance.harmonic 5 + ABCInstance.harmonic 5 := by linarith [hu_sum_bound]
      _ = 11/6 + 3/2 + 137/60 + 137/60 := by rw [harmonic_3, hH2, harmonic_5]
      _ = 79/10 := by norm_num
      _ = 3/2 + 3/2 + 49/20 + 49/20 := by norm_num
      _ = _ := by rw [hH2, hH6]
  · -- Case d = 6: Here u0 + u1 ≤ 2 since |W' ∩ Dc| = 8 - 6 = 2
    simp only [hd6]
    -- When d = 6, we have |W' ∩ Dc| = 2, so W' contains exactly 2 from {0,1,2,3}
    -- The best case is {0,1} giving u0 = u1 = 2, which equals W
    -- We need: H(u0) + H(u1) ≤ H(2) + H(2)
    -- Using the constraint that W' ∩ Dc has exactly 2 elements
    have hDc_card : (W' ∩ Dc).card = 2 := by
      have hCard : (W' ∩ D).card + (W' ∩ Dc).card = 8 := by
        have hDisj : Disjoint (W' ∩ D) (W' ∩ Dc) := by
          rw [disjoint_iff_inter_eq_empty]
          have h : (W' ∩ D) ∩ (W' ∩ Dc) ⊆ D ∩ Dc := by
            intro x hx
            simp only [mem_inter] at hx ⊢
            exact ⟨hx.1.2, hx.2.2⟩
          rw [D_inter_Dc] at h
          exact Finset.subset_empty.mp h
        have hW'_split : W' = (W' ∩ D) ∪ (W' ∩ Dc) := by
          ext x
          simp only [mem_union, mem_inter]
          constructor
          · intro hx
            have hx_cand : x ∈ candidates := hW'_sub hx
            rw [← D_union_Dc] at hx_cand
            simp only [mem_union] at hx_cand
            rcases hx_cand with hD | hDc
            · left; exact ⟨hx, hD⟩
            · right; exact ⟨hx, hDc⟩
          · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
        have heq : W' ∩ D ∪ W' ∩ Dc = W' := by rw [← hW'_split]
        rw [← card_union_of_disjoint hDisj, heq, hW'_card]
        rfl
      omega
    -- u0 ≤ |{0,1,2} ∩ W' ∩ Dc| + |{0,1,2} ∩ W' ∩ D|
    -- But W' ∩ D ⊆ D = {4,5,6,7,8,9}, so {0,1,2} ∩ W' ∩ D = ∅
    -- Hence u0 ≤ |{0,1,2} ∩ W' ∩ Dc| ≤ |W' ∩ Dc| = 2
    have hu0_le2 : u0 ≤ 2 := by
      calc u0 = (W' ∩ approves 0).card := rfl
        _ ≤ (W' ∩ Dc).card := by
          apply card_le_card
          intro x hx
          simp only [mem_inter, approves, Dc] at hx ⊢
          refine ⟨hx.1, ?_⟩
          simp only [mem_insert, mem_singleton] at hx ⊢
          rcases hx.2 with rfl | rfl | rfl
          · left; rfl
          · right; left; rfl
          · right; right; left; rfl
        _ = 2 := hDc_card
    have hu1_le2 : u1 ≤ 2 := by
      calc u1 = (W' ∩ approves 1).card := rfl
        _ ≤ (W' ∩ Dc).card := by
          apply card_le_card
          intro x hx
          simp only [mem_inter, approves, Dc] at hx ⊢
          refine ⟨hx.1, ?_⟩
          simp only [mem_insert, mem_singleton] at hx ⊢
          rcases hx.2 with rfl | rfl | rfl
          · left; rfl
          · right; left; rfl
          · right; right; right; rfl
        _ = 2 := hDc_card
    have hu0_bound' : ABCInstance.harmonic u0 ≤ ABCInstance.harmonic 2 :=
      harmonic_mono' hu0_le2
    have hu1_bound' : ABCInstance.harmonic u1 ≤ ABCInstance.harmonic 2 :=
      harmonic_mono' hu1_le2
    linarith

-- ============================================================================
-- MAIN THEOREMS
-- ============================================================================

/--
**Main Result**: PAV may fail the core property when k = 8.

There exists an ABC instance with k = 8 where a PAV winning committee
is not in the core.
-/
theorem pav_not_in_core_k8 :
    ∃ (inst : ABCInstance Voter Candidate k),
      ∃ W : Finset Candidate, inst.is_pav_winner W ∧ ¬inst.is_in_core W :=
  ⟨inst, W, W_is_pav_winner, W_not_in_core⟩

/--
**Main Result**: PAV may fail priceability when k = 8.

There exists an ABC instance with k = 8 where a PAV winning committee
is not priceable.
-/
theorem pav_not_priceable_k8 :
    ∃ (inst : ABCInstance Voter Candidate k),
      ∃ W : Finset Candidate, inst.is_pav_winner W ∧ ¬inst.is_priceable W :=
  ⟨inst, W, W_is_pav_winner, W_not_priceable⟩

end PAVCounterexamples
