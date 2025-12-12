/-
Peters Impossibility Base Case: k=3, n=3, m=4

This file proves the first step of the base case: assuming f(P₁) = acd,
we show f(P₁_₅) = acd.
-/

import ABCVoting.ABCRule
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.Peters.SingletonApprovers

open Finset ABCInstance

namespace Peters.BaseCase

-- ============================================================================
-- TYPE SETUP
-- ============================================================================

abbrev V := Fin 3
abbrev C := Fin 4
abbrev k : ℕ := 3

abbrev v₁ : V := 0
abbrev v₂ : V := 1
abbrev v₃ : V := 2

def allCandidates : Finset C := univ
def allVoters : Finset V := univ

abbrev Profile := V → Finset C

def mkInstance (P : Profile) (h_proper : ∀ v : V, P v ⊂ allCandidates) : ABCInstance V C k where
  voters := allVoters
  candidates := allCandidates
  approves := P
  approves_subset := fun v _ => (h_proper v).subset
  voters_nonempty := by simp [allVoters]
  k_pos := by decide
  k_le_m := by simp [allCandidates]; decide

noncomputable def W (f : ABCRule V C k) (hres : f.IsResolute) (P : Profile)
    (h_proper : ∀ v : V, P v ⊂ allCandidates) : Finset C :=
  f.resolute_committee (mkInstance P h_proper) hres

-- ============================================================================
-- BALLOTS AND COMMITTEES
-- ============================================================================

def ballot_ab : Finset C := {0, 1}
def ballot_ac : Finset C := {0, 2}
def ballot_c : Finset C := {2}
def ballot_d : Finset C := {3}

def comm_acd : Finset C := {0, 2, 3}
def comm_bcd : Finset C := {1, 2, 3}
def comm_abd : Finset C := {0, 1, 3}

def P₁ : Profile := ![ballot_ab, ballot_c, ballot_d]
def P₁_₅ : Profile := ![ballot_ab, ballot_ac, ballot_d]

-- ============================================================================
-- VALIDITY
-- ============================================================================

lemma P₁_proper (v : V) : P₁ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₁_₅_proper (v : V) : P₁_₅ v ⊂ allCandidates := by
  fin_cases v <;> decide

-- ============================================================================
-- SINGLETON APPROVERS FOR d IN P₁_₅
-- ============================================================================

lemma d_exclusive_singleton_P₁_₅ :
    SingletonApprovers.is_exclusive_singleton (mkInstance P₁_₅ P₁_₅_proper) (3 : C) := by
  constructor
  · use (2 : V)
    simp only [ABCInstance.singleton_party, mem_filter, mkInstance, allVoters, mem_univ, true_and]
    rfl
  · ext v
    simp only [ABCInstance.supporters, ABCInstance.singleton_party, mem_filter,
               mkInstance, allVoters, mem_univ, true_and]
    constructor
    · intro hd_in
      fin_cases v <;> simp_all [P₁_₅, ballot_ab, ballot_ac, ballot_d]
    · intro heq
      rw [heq]
      decide

lemma singleton_party_size_d_P₁_₅ :
    (mkInstance P₁_₅ P₁_₅_proper).singleton_party_size (3 : C) = 1 := rfl

lemma d_meets_threshold_P₁_₅ :
    (mkInstance P₁_₅ P₁_₅_proper).singleton_party_size (3 : C) * k ≥
    (mkInstance P₁_₅ P₁_₅_proper).voters.card := by
  rw [singleton_party_size_d_P₁_₅]
  rfl

lemma d_in_candidates : (3 : C) ∈ (mkInstance P₁_₅ P₁_₅_proper).candidates := by decide

lemma candidates_card : (mkInstance P₁_₅ P₁_₅_proper).candidates.card = k + 1 := by decide

lemma d_in_W_P₁_₅ (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness) :
    (3 : C) ∈ W f hres P₁_₅ P₁_₅_proper :=
  SingletonApprovers.singleton_approvers_elected
    (mkInstance P₁_₅ P₁_₅_proper) 3 d_in_candidates candidates_card
    d_meets_threshold_P₁_₅ d_exclusive_singleton_P₁_₅ f hwf hres hprop hsp

-- ============================================================================
-- VARIANT LEMMAS
-- ============================================================================

lemma P₁_₅_is_variant_P₁ :
    (mkInstance P₁_₅ P₁_₅_proper).is_i_variant (mkInstance P₁ P₁_proper) v₂ := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v
  · rfl
  · exact absurd rfl hne
  · rfl

lemma P₁_ballot_strict_subset_P₁_₅ :
    (mkInstance P₁ P₁_proper).approves v₂ ⊂ (mkInstance P₁_₅ P₁_₅_proper).approves v₂ := by
  decide

lemma v₂_in_voters : v₂ ∈ (mkInstance P₁_₅ P₁_₅_proper).voters := by decide

lemma v₂_approves_ac : (mkInstance P₁_₅ P₁_₅_proper).approves v₂ = ballot_ac := rfl

-- ============================================================================
-- MAIN STEP
-- ============================================================================

/-- Key: if f(P₁) = acd, then f(P₁_₅) = acd -/
lemma step1_f_P₁_₅_eq_acd (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness)
    (h_P₁ : W f hres P₁ P₁_proper = comm_acd) :
    W f hres P₁_₅ P₁_₅_proper = comm_acd := by
  have hd : (3 : C) ∈ W f hres P₁_₅ P₁_₅_proper := d_in_W_P₁_₅ f hwf hres hprop hsp

  set W₁_₅ := W f hres P₁_₅ P₁_₅_proper
  set inst₁_₅ := mkInstance P₁_₅ P₁_₅_proper
  set inst₁ := mkInstance P₁ P₁_proper

  have hW_mem := f.resolute_committee_mem inst₁_₅ hres
  have hW_sub : W₁_₅ ⊆ inst₁_₅.candidates := (hwf inst₁_₅).2 W₁_₅ hW_mem |>.2
  have hW_card : W₁_₅.card = k := (hwf inst₁_₅).2 W₁_₅ hW_mem |>.1

  -- inst₁_₅.candidates = univ (all 4 candidates)
  have h_cands : inst₁_₅.candidates = univ := rfl

  -- Use committee_contains_or_complement
  have h_card_eq : W₁_₅.card = inst₁_₅.candidates.card - 1 := by
    simp only [hW_card, k, h_cands, card_univ, Fintype.card_fin]

  -- Since d ∈ W₁_₅, W₁_₅ ≠ C \ {d}
  have h_ne_compl : W₁_₅ ≠ inst₁_₅.candidates \ {3} := by
    intro heq
    have : (3 : C) ∈ inst₁_₅.candidates \ {3} := by rw [← heq]; exact hd
    simp at this

  -- So W₁_₅ must contain 3 (which we know) and be one of abd, acd, bcd
  -- We determine which by checking if it equals comm_acd, and if not, derive contradiction

  by_contra h_ne_acd

  -- W₁_₅ contains 3, has size 3, is a subset of {0,1,2,3}, and ≠ acd
  -- So W₁_₅ = abd or W₁_₅ = bcd

  -- Check if 0 ∈ W₁_₅
  by_cases h0 : (0 : C) ∈ W₁_₅
  · -- 0, 3 ∈ W₁_₅
    -- Check if 1 ∈ W₁_₅
    by_cases h1 : (1 : C) ∈ W₁_₅
    · -- 0, 1, 3 ∈ W₁_₅, so W₁_₅ = abd (since |W₁_₅| = 3)
      have hW_eq : W₁_₅ = comm_abd := by
        have h_sub : comm_abd ⊆ W₁_₅ := by
          intro x hx
          simp only [comm_abd, mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        exact (eq_of_subset_of_card_le h_sub (by simp [comm_abd, hW_card, k])).symm
      -- Strategyproofness violation
      have h_viol : W f hres P₁ P₁_proper ∩ ballot_ac ⊃ W₁_₅ ∩ ballot_ac := by
        simp only [h_P₁, hW_eq, comm_acd, comm_abd, ballot_ac]
        decide
      have := hsp inst₁_₅ inst₁ v₂ v₂_in_voters P₁_₅_is_variant_P₁ P₁_ballot_strict_subset_P₁_₅ hres
      exact this h_viol

    · -- 0, 3 ∈ W₁_₅; 1 ∉ W₁_₅
      -- Since |W₁_₅| = 3, we need 2 ∈ W₁_₅, so W₁_₅ = acd
      have h2 : (2 : C) ∈ W₁_₅ := by
        by_contra h2_out
        -- W₁_₅ ⊆ {0, 3}, but |W₁_₅| = 3, contradiction
        have hsub : W₁_₅ ⊆ ({0, 3} : Finset C) := by
          intro x hx
          have hx_in := hW_sub hx
          simp only [h_cands, mem_univ] at hx_in
          fin_cases x <;> simp_all
        have hcard : W₁_₅.card ≤ 2 := by
          calc W₁_₅.card ≤ ({0, 3} : Finset C).card := card_le_card hsub
            _ = 2 := by decide
        simp only [hW_card, k] at hcard
        omega
      -- W₁_₅ = acd
      have hW_eq : W₁_₅ = comm_acd := by
        have h_sub : comm_acd ⊆ W₁_₅ := by
          intro x hx
          simp only [comm_acd, mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        exact (eq_of_subset_of_card_le h_sub (by simp [comm_acd, hW_card, k])).symm
      exact h_ne_acd hW_eq

  · -- 0 ∉ W₁_₅, 3 ∈ W₁_₅
    -- Since |W₁_₅| = 3 and W₁_₅ ⊆ {0,1,2,3}, we need 1, 2 ∈ W₁_₅
    have h1 : (1 : C) ∈ W₁_₅ := by
      by_contra h1_out
      -- W₁_₅ ⊆ {2, 3}, but |W₁_₅| = 3
      have hsub : W₁_₅ ⊆ ({2, 3} : Finset C) := by
        intro x hx
        have hx_in := hW_sub hx
        simp only [h_cands, mem_univ] at hx_in
        fin_cases x <;> simp_all
      have hcard : W₁_₅.card ≤ 2 := by
        calc W₁_₅.card ≤ ({2, 3} : Finset C).card := card_le_card hsub
          _ = 2 := by decide
      simp only [hW_card, k] at hcard
      omega
    have h2 : (2 : C) ∈ W₁_₅ := by
      by_contra h2_out
      -- W₁_₅ ⊆ {1, 3}, but |W₁_₅| = 3
      have hsub : W₁_₅ ⊆ ({1, 3} : Finset C) := by
        intro x hx
        have hx_in := hW_sub hx
        simp only [h_cands, mem_univ] at hx_in
        fin_cases x <;> simp_all
      have hcard : W₁_₅.card ≤ 2 := by
        calc W₁_₅.card ≤ ({1, 3} : Finset C).card := card_le_card hsub
          _ = 2 := by decide
      simp only [hW_card, k] at hcard
      omega
    -- So 1, 2, 3 ∈ W₁_₅, meaning W₁_₅ = bcd
    have hW_eq : W₁_₅ = comm_bcd := by
      have h_sub : comm_bcd ⊆ W₁_₅ := by
        intro x hx
        simp only [comm_bcd, mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      exact (eq_of_subset_of_card_le h_sub (by simp [comm_bcd, hW_card, k])).symm
    -- Strategyproofness violation
    have h_viol : W f hres P₁ P₁_proper ∩ ballot_ac ⊃ W₁_₅ ∩ ballot_ac := by
      simp only [h_P₁, hW_eq, comm_acd, comm_bcd, ballot_ac]
      decide
    have := hsp inst₁_₅ inst₁ v₂ v₂_in_voters P₁_₅_is_variant_P₁ P₁_ballot_strict_subset_P₁_₅ hres
    exact this h_viol

end Peters.BaseCase
