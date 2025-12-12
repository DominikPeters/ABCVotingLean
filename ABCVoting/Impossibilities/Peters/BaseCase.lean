/-
Peters Impossibility Base Case: k=3, n=3, m=4

This file proves the first step of the base case: assuming f(P₁) = acd,
we show f(P₁_₅) = acd, and then f(P₂) = bcd.
-/

import ABCVoting.ABCRule
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.Peters.SingletonApprovers
import ABCVoting.Fin4Card3

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
def ballot_b : Finset C := {1}
def ballot_ac : Finset C := {0, 2}
def ballot_c : Finset C := {2}
def ballot_d : Finset C := {3}

def comm_acd : Finset C := {0, 2, 3}
def comm_bcd : Finset C := {1, 2, 3}
def comm_abd : Finset C := {0, 1, 3}

def P₁ : Profile := ![ballot_ab, ballot_c, ballot_d]
def P₁_₅ : Profile := ![ballot_ab, ballot_ac, ballot_d]
def P₂ : Profile := ![ballot_b, ballot_ac, ballot_d]

-- ============================================================================
-- VALIDITY
-- ============================================================================

lemma P₁_proper (v : V) : P₁ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₁_₅_proper (v : V) : P₁_₅ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₂_proper (v : V) : P₂ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₂_is_party_list : (mkInstance P₂ P₂_proper).is_party_list := by
  intro v₁ _ v₂ _
  fin_cases v₁ <;> fin_cases v₂ <;> decide

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
-- P₂: PROPORTIONALITY FOR b AND d
-- ============================================================================

lemma singleton_party_size_b_P₂ :
    (mkInstance P₂ P₂_proper).singleton_party_size (1 : C) = 1 := rfl

lemma singleton_party_size_d_P₂ :
    (mkInstance P₂ P₂_proper).singleton_party_size (3 : C) = 1 := rfl

lemma b_meets_threshold_P₂ :
    (mkInstance P₂ P₂_proper).singleton_party_size (1 : C) * k ≥
    (mkInstance P₂ P₂_proper).voters.card := by
  rw [singleton_party_size_b_P₂]
  rfl

lemma d_meets_threshold_P₂ :
    (mkInstance P₂ P₂_proper).singleton_party_size (3 : C) * k ≥
    (mkInstance P₂ P₂_proper).voters.card := by
  rw [singleton_party_size_d_P₂]
  rfl

lemma b_in_candidates_P₂ : (1 : C) ∈ (mkInstance P₂ P₂_proper).candidates := by decide

lemma d_in_candidates_P₂ : (3 : C) ∈ (mkInstance P₂ P₂_proper).candidates := by decide

lemma b_in_W_P₂ (f : ABCRule V C k) (hres : f.IsResolute) (hprop : f.SatisfiesProportionality) :
    (1 : C) ∈ W f hres P₂ P₂_proper := by
  simpa [W] using
    (ABCRule.resolute_proportionality (f := f) (hres := hres) (hprop := hprop)
      (inst := mkInstance P₂ P₂_proper) (c := (1 : C))
      (hpl := P₂_is_party_list) (hc_cand := b_in_candidates_P₂) (h_size := b_meets_threshold_P₂))

lemma d_in_W_P₂ (f : ABCRule V C k) (hres : f.IsResolute) (hprop : f.SatisfiesProportionality) :
    (3 : C) ∈ W f hres P₂ P₂_proper := by
  simpa [W] using
    (ABCRule.resolute_proportionality (f := f) (hres := hres) (hprop := hprop)
      (inst := mkInstance P₂ P₂_proper) (c := (3 : C))
      (hpl := P₂_is_party_list) (hc_cand := d_in_candidates_P₂) (h_size := d_meets_threshold_P₂))

-- ============================================================================
-- VARIANT LEMMAS FOR P₁_₅ → P₂ (VOTER 1 REPORTS b ⊂ ab)
-- ============================================================================

lemma P₁_₅_is_variant_P₂ :
    (mkInstance P₁_₅ P₁_₅_proper).is_i_variant (mkInstance P₂ P₂_proper) v₁ := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v
  · exact absurd rfl hne
  · rfl
  · rfl

lemma P₂_ballot_strict_subset_P₁_₅ :
    (mkInstance P₂ P₂_proper).approves v₁ ⊂ (mkInstance P₁_₅ P₁_₅_proper).approves v₁ := by
  decide

lemma v₁_in_voters : v₁ ∈ (mkInstance P₁_₅ P₁_₅_proper).voters := by decide

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
  have hW_card : W₁_₅.card = k := (hwf inst₁_₅).2 W₁_₅ hW_mem |>.1

  have hW_cases : W₁_₅ = comm_abd ∨ W₁_₅ = comm_acd ∨ W₁_₅ = comm_bcd := by
    have hcard3 : W₁_₅.card = 3 := by
      simpa [k] using hW_card
    simpa [comm_abd, comm_acd, comm_bcd] using
      (ABCVoting.fin4_card3_mem_three (s := W₁_₅) (hs := hcard3) (h3 := hd))

  rcases hW_cases with hW_eq_abd | hW_cases'
  · have h_viol : W f hres P₁ P₁_proper ∩ ballot_ac ⊃ W₁_₅ ∩ ballot_ac := by
      simp [h_P₁, hW_eq_abd, comm_acd, comm_abd, ballot_ac]
      decide
    have hno :=
      hsp inst₁_₅ inst₁ v₂ v₂_in_voters P₁_₅_is_variant_P₁ P₁_ballot_strict_subset_P₁_₅ hres
    exact False.elim (hno h_viol)

  rcases hW_cases' with hW_eq_acd | hW_eq_bcd
  · exact hW_eq_acd
  · have h_viol : W f hres P₁ P₁_proper ∩ ballot_ac ⊃ W₁_₅ ∩ ballot_ac := by
      simp [h_P₁, hW_eq_bcd, comm_acd, comm_bcd, ballot_ac]
      decide
    have hno :=
      hsp inst₁_₅ inst₁ v₂ v₂_in_voters P₁_₅_is_variant_P₁ P₁_ballot_strict_subset_P₁_₅ hres
    exact False.elim (hno h_viol)

/-- Next: if f(P₁) = acd, then f(P₂) = bcd -/
lemma step2_f_P₂_eq_bcd (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness)
    (h_P₁ : W f hres P₁ P₁_proper = comm_acd) :
    W f hres P₂ P₂_proper = comm_bcd := by
  have h_P₁_₅ : W f hres P₁_₅ P₁_₅_proper = comm_acd :=
    step1_f_P₁_₅_eq_acd f hwf hres hprop hsp h_P₁

  have hb : (1 : C) ∈ W f hres P₂ P₂_proper := b_in_W_P₂ f hres hprop
  have hd : (3 : C) ∈ W f hres P₂ P₂_proper := d_in_W_P₂ f hres hprop

  set W₂ := W f hres P₂ P₂_proper with hW₂
  set inst₂ := mkInstance P₂ P₂_proper with hinst₂

  have hW_mem := f.resolute_committee_mem inst₂ hres
  have hW_card : W₂.card = k := (hwf inst₂).2 W₂ hW_mem |>.1

  have hW_cases : W₂ = comm_abd ∨ W₂ = comm_bcd := by
    have hcard3 : W₂.card = 3 := by
      simpa [k] using hW_card
    have hcases3 :
        W₂ = ({0, 1, 3} : Finset (Fin 4)) ∨
        W₂ = ({0, 2, 3} : Finset (Fin 4)) ∨
        W₂ = ({1, 2, 3} : Finset (Fin 4)) := by
      simpa [W₂] using (ABCVoting.fin4_card3_mem_three (s := W₂) (hs := hcard3) (h3 := hd))
    rcases hcases3 with hW_eq_abd' | hW_cases'
    · left
      simpa [comm_abd] using hW_eq_abd'
    rcases hW_cases' with hW_eq_acd' | hW_eq_bcd'
    · -- impossible since b must be elected by proportionality
      have : (1 : C) ∈ ({0, 2, 3} : Finset (Fin 4)) := by
        simpa [hW_eq_acd'] using hb
      cases (by decide : ¬(1 : C) ∈ ({0, 2, 3} : Finset (Fin 4))) this
    · right
      simpa [comm_bcd] using hW_eq_bcd'

  rcases hW_cases with hW_eq_abd | hW_eq_bcd
  · have h_viol' : W₂ ∩ ballot_ab ⊃ comm_acd ∩ ballot_ab := by
      simp [hW_eq_abd, comm_abd, comm_acd, ballot_ab]
      decide
    have hno :=
      hsp (mkInstance P₁_₅ P₁_₅_proper) inst₂ v₁ v₁_in_voters P₁_₅_is_variant_P₂
        P₂_ballot_strict_subset_P₁_₅ hres
    have h_eq : f.resolute_committee (mkInstance P₁_₅ P₁_₅_proper) hres = comm_acd := by
      simpa [W] using h_P₁_₅
    have h_viol_comm :
        f.resolute_committee inst₂ hres ∩ ballot_ab ⊃ comm_acd ∩ ballot_ab := by
      simpa [W, hW₂, hinst₂] using h_viol'
    have h_viol :
        f.resolute_committee inst₂ hres ∩ (mkInstance P₁_₅ P₁_₅_proper).approves v₁ ⊃
          f.resolute_committee (mkInstance P₁_₅ P₁_₅_proper) hres ∩
            (mkInstance P₁_₅ P₁_₅_proper).approves v₁ := by
      convert h_viol_comm
    exact False.elim (hno h_viol)
  · exact hW_eq_bcd

end Peters.BaseCase
