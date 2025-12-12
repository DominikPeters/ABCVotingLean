/-
Peters Impossibility Base Case: k=3, n=3, m=4

This file proves the first step of the base case: assuming f(P₁) = acd,
we show f(P₁_₅) = acd, and then f(P₂) = bcd.
-/

import ABCVoting.Fin4Card3
import ABCVoting.Impossibilities.Peters.BaseCaseCommon

open Finset ABCInstance

namespace Peters.BaseCaseACD

open Peters.BaseCaseCommon

-- ============================================================================
-- BALLOTS AND COMMITTEES
-- ============================================================================

def ballot_ab : Finset C := {0, 1}
def ballot_a : Finset C := {0}
def ballot_b : Finset C := {1}
def ballot_ac : Finset C := {0, 2}
def ballot_ad : Finset C := {0, 3}
def ballot_c : Finset C := {2}
def ballot_d : Finset C := {3}
def ballot_cd : Finset C := {2, 3}

def comm_acd : Finset C := {0, 2, 3}
def comm_bcd : Finset C := {1, 2, 3}
def comm_abd : Finset C := {0, 1, 3}
def comm_abc : Finset C := {0, 1, 2}

@[simp] lemma insert_d_ballot_ac : insert (3 : C) ballot_ac = comm_acd := by decide
@[simp] lemma insert_b_ballot_cd : insert (1 : C) ballot_cd = comm_bcd := by decide
@[simp] lemma insert_b_ballot_ad : insert (1 : C) ballot_ad = comm_abd := by decide
@[simp] lemma insert_c_ballot_ab : insert (2 : C) ballot_ab = comm_abc := by decide
@[simp] lemma insert_b_ballot_ac : insert (1 : C) ballot_ac = comm_abc := by decide

def P₁ : Profile := ![ballot_ab, ballot_c, ballot_d]
def P₁_₅ : Profile := ![ballot_ab, ballot_ac, ballot_d]
def P₂ : Profile := ![ballot_b, ballot_ac, ballot_d]
def P₂_₅ : Profile := ![ballot_b, ballot_ac, ballot_cd]
def P₃ : Profile := ![ballot_b, ballot_a, ballot_cd]
def P₃_₅ : Profile := ![ballot_b, ballot_ad, ballot_cd]
def P₄ : Profile := ![ballot_b, ballot_ad, ballot_c]
def P₄_₅ : Profile := ![ballot_b, ballot_ad, ballot_ac]
def P₅ : Profile := ![ballot_b, ballot_d, ballot_ac]
def P₅_₅ : Profile := ![ballot_b, ballot_cd, ballot_ac]
def P₆ : Profile := ![ballot_b, ballot_cd, ballot_a]
def P₆_₅ : Profile := ![ballot_b, ballot_cd, ballot_ad]
def P₇ : Profile := ![ballot_b, ballot_c, ballot_ad]
def P₇_₅ : Profile := ![ballot_ab, ballot_c, ballot_ad]

-- ============================================================================
-- VALIDITY
-- ============================================================================

lemma P₁_proper (v : V) : P₁ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₁_₅_proper (v : V) : P₁_₅ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₂_proper (v : V) : P₂ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₂_₅_proper (v : V) : P₂_₅ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₃_proper (v : V) : P₃ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₃_₅_proper (v : V) : P₃_₅ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₄_proper (v : V) : P₄ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₄_₅_proper (v : V) : P₄_₅ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₅_proper (v : V) : P₅ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₅_₅_proper (v : V) : P₅_₅ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₆_proper (v : V) : P₆ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₆_₅_proper (v : V) : P₆_₅ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₇_proper (v : V) : P₇ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₇_₅_proper (v : V) : P₇_₅ v ⊂ allCandidates := by
  fin_cases v <;> decide

lemma P₂_is_party_list : (mkInstance P₂ P₂_proper).is_party_list := by
  intro v₁ _ v₂ _
  fin_cases v₁ <;> fin_cases v₂ <;> decide

lemma P₃_is_party_list : (mkInstance P₃ P₃_proper).is_party_list := by
  intro v₁ _ v₂ _
  fin_cases v₁ <;> fin_cases v₂ <;> decide

lemma P₄_is_party_list : (mkInstance P₄ P₄_proper).is_party_list := by
  intro v₁ _ v₂ _
  fin_cases v₁ <;> fin_cases v₂ <;> decide

lemma P₅_is_party_list : (mkInstance P₅ P₅_proper).is_party_list := by
  intro v₁ _ v₂ _
  fin_cases v₁ <;> fin_cases v₂ <;> decide

lemma P₆_is_party_list : (mkInstance P₆ P₆_proper).is_party_list := by
  intro v₁ _ v₂ _
  fin_cases v₁ <;> fin_cases v₂ <;> decide

lemma P₇_is_party_list : (mkInstance P₇ P₇_proper).is_party_list := by
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
-- GENERIC STEPS (LEMMA H / LEMMA I)
-- (available in `Peters.BaseCaseCommon`)

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

  have h :
      W f hres P₁_₅ P₁_₅_proper = insert (3 : C) ballot_ac := by
    refine stepH f hwf hres hsp P₁ P₁_₅ P₁_proper P₁_₅_proper v₂ v₂_in_voters
      P₁_₅_is_variant_P₁ P₁_ballot_strict_subset_P₁_₅ ballot_ac ?_ (3 : C) hd ?_ ?_ ?_
    · exact v₂_approves_ac
    · decide
    · decide
    · simpa [h_P₁]
  simpa [comm_acd] using h

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

-- ============================================================================
-- COMMITTEE CASE SPLITS FROM REQUIRED MEMBERS
-- ============================================================================

lemma card3_mem_bd_cases (W : Finset C) (hcard : W.card = 3)
    (hb : (1 : C) ∈ W) (hd : (3 : C) ∈ W) :
    W = comm_abd ∨ W = comm_bcd := by
  have hcases :
      W = ({0, 1, 3} : Finset (Fin 4)) ∨
      W = ({0, 2, 3} : Finset (Fin 4)) ∨
      W = ({1, 2, 3} : Finset (Fin 4)) :=
    ABCVoting.fin4_card3_mem_three (s := W) (hs := hcard) (h3 := hd)
  rcases hcases with hW_eq_abd | hW_cases'
  · left; simpa [comm_abd] using hW_eq_abd
  rcases hW_cases' with hW_eq_acd | hW_eq_bcd
  · -- impossible since b ∈ W
    have : (1 : C) ∈ ({0, 2, 3} : Finset (Fin 4)) := by
      simpa [hW_eq_acd] using hb
    cases (by decide : ¬(1 : C) ∈ ({0, 2, 3} : Finset (Fin 4))) this
  · right; simpa [comm_bcd] using hW_eq_bcd

lemma card3_mem_ab_cases (W : Finset C) (hcard : W.card = 3)
    (ha : (0 : C) ∈ W) (hb : (1 : C) ∈ W) :
    W = comm_abc ∨ W = comm_abd := by
  have hcases :
      W = ({0, 1, 2} : Finset (Fin 4)) ∨
      W = ({0, 1, 3} : Finset (Fin 4)) ∨
      W = ({1, 2, 3} : Finset (Fin 4)) :=
    ABCVoting.fin4_card3_mem_one (s := W) (hs := hcard) (h1 := hb)
  rcases hcases with hW_eq_abc | hW_cases'
  · left; simpa [comm_abc] using hW_eq_abc
  rcases hW_cases' with hW_eq_abd | hW_eq_bcd
  · right; simpa [comm_abd] using hW_eq_abd
  · -- impossible since a ∈ W
    have : (0 : C) ∈ ({1, 2, 3} : Finset (Fin 4)) := by
      simpa [hW_eq_bcd] using ha
    cases (by decide : ¬(0 : C) ∈ ({1, 2, 3} : Finset (Fin 4))) this

lemma card3_mem_bc_cases (W : Finset C) (hcard : W.card = 3)
    (hb : (1 : C) ∈ W) (hc : (2 : C) ∈ W) :
    W = comm_abc ∨ W = comm_bcd := by
  have hcases :
      W = ({0, 1, 2} : Finset (Fin 4)) ∨
      W = ({0, 2, 3} : Finset (Fin 4)) ∨
      W = ({1, 2, 3} : Finset (Fin 4)) :=
    ABCVoting.fin4_card3_mem_two (s := W) (hs := hcard) (h2 := hc)
  rcases hcases with hW_eq_abc | hW_cases'
  · left; simpa [comm_abc] using hW_eq_abc
  rcases hW_cases' with hW_eq_acd | hW_eq_bcd
  · -- impossible since b ∈ W
    have : (1 : C) ∈ ({0, 2, 3} : Finset (Fin 4)) := by
      simpa [hW_eq_acd] using hb
    cases (by decide : ¬(1 : C) ∈ ({0, 2, 3} : Finset (Fin 4))) this
  · right; simpa [comm_bcd] using hW_eq_bcd

-- ============================================================================
-- HELPERS
-- (available in `Peters.BaseCaseCommon`)

-- ============================================================================
-- REMAINING CHAIN (FROM f(P₁)=acd)
-- ============================================================================

-- P₂ → P₂_₅ (v₃ expands d ⊂ cd), singleton b in P₂_₅

lemma P₂_to_P₂_₅_is_variant :
    (mkInstance P₂_₅ P₂_₅_proper).is_i_variant (mkInstance P₂ P₂_proper) v₃ := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v
  · rfl
  · rfl
  · exact False.elim (hne rfl)

lemma P₂_ballot_strict_subset_P₂_₅ :
    (mkInstance P₂ P₂_proper).approves v₃ ⊂ (mkInstance P₂_₅ P₂_₅_proper).approves v₃ := by
  decide

lemma b_exclusive_singleton_P₂_₅ :
    Peters.SingletonApprovers.is_exclusive_singleton (mkInstance P₂_₅ P₂_₅_proper) (1 : C) := by
  refine exclusive_singleton_of_unique_supporter (inst := mkInstance P₂_₅ P₂_₅_proper)
    (c := (1 : C)) (v₀ := v₁) ?_ ?_ ?_
  · decide
  · rfl
  · intro v hv hne
    fin_cases v <;> simp [mkInstance, P₂_₅, ballot_b, ballot_ac, ballot_cd] at hv hne ⊢

lemma singleton_party_size_b_P₂_₅ :
    (mkInstance P₂_₅ P₂_₅_proper).singleton_party_size (1 : C) = 1 := by
  decide

lemma b_in_W_P₂_₅ (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness) :
    (1 : C) ∈ W f hres P₂_₅ P₂_₅_proper :=
  singleton_approver_in_W f hwf hres hprop hsp P₂_₅ P₂_₅_proper (1 : C)
    singleton_party_size_b_P₂_₅ b_exclusive_singleton_P₂_₅

lemma step3_f_P₂_₅_eq_bcd (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness)
    (h_P₁ : W f hres P₁ P₁_proper = comm_acd) :
    W f hres P₂_₅ P₂_₅_proper = comm_bcd := by
  have h_P₂ : W f hres P₂ P₂_proper = comm_bcd :=
    step2_f_P₂_eq_bcd f hwf hres hprop hsp h_P₁
  have hb : (1 : C) ∈ W f hres P₂_₅ P₂_₅_proper := b_in_W_P₂_₅ f hwf hres hprop hsp
  have h :
      W f hres P₂_₅ P₂_₅_proper = insert (1 : C) ballot_cd := by
    refine stepH f hwf hres hsp P₂ P₂_₅ P₂_proper P₂_₅_proper v₃ (by decide)
      P₂_to_P₂_₅_is_variant P₂_ballot_strict_subset_P₂_₅ ballot_cd rfl (1 : C) hb ?_ ?_ ?_
    · decide
    · decide
    · simpa [h_P₂]
  simpa [comm_bcd] using h

-- P₂_₅ → P₃ (v₂ shrinks a ⊂ ac), P₃ is party-list with singleton a and b

lemma P₂_₅_is_variant_P₃ :
    (mkInstance P₂_₅ P₂_₅_proper).is_i_variant (mkInstance P₃ P₃_proper) v₂ := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v
  · rfl
  · exact False.elim (hne rfl)
  · rfl

lemma P₃_ballot_strict_subset_P₂_₅ :
    (mkInstance P₃ P₃_proper).approves v₂ ⊂ (mkInstance P₂_₅ P₂_₅_proper).approves v₂ := by
  decide

lemma a_in_W_P₃ (f : ABCRule V C k) (hres : f.IsResolute) (hprop : f.SatisfiesProportionality) :
    (0 : C) ∈ W f hres P₃ P₃_proper :=
  mem_W_of_prop_singleton_one f hres hprop P₃ P₃_proper P₃_is_party_list (0 : C) (by decide)

lemma b_in_W_P₃ (f : ABCRule V C k) (hres : f.IsResolute) (hprop : f.SatisfiesProportionality) :
    (1 : C) ∈ W f hres P₃ P₃_proper :=
  mem_W_of_prop_singleton_one f hres hprop P₃ P₃_proper P₃_is_party_list (1 : C) (by decide)

lemma step4_f_P₃_eq_abd (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness)
    (h_P₁ : W f hres P₁ P₁_proper = comm_acd) :
    W f hres P₃ P₃_proper = comm_abd := by
  have h_P₂_₅ : W f hres P₂_₅ P₂_₅_proper = comm_bcd :=
    step3_f_P₂_₅_eq_bcd f hwf hres hprop hsp h_P₁

  have ha : (0 : C) ∈ W f hres P₃ P₃_proper := a_in_W_P₃ f hres hprop
  have hb : (1 : C) ∈ W f hres P₃ P₃_proper := b_in_W_P₃ f hres hprop
  have hcard3 : (W f hres P₃ P₃_proper).card = 3 := by
    simpa [k] using (W_card f hwf hres P₃ P₃_proper)
  have hW_cases : W f hres P₃ P₃_proper = comm_abc ∨ W f hres P₃ P₃_proper = comm_abd :=
    card3_mem_ab_cases _ hcard3 ha hb

  have h_gain_if_abc :
      comm_abc ∩ ballot_ac ⊃ comm_bcd ∩ ballot_ac := by
    simp [comm_abc, comm_bcd, ballot_ac]
    decide

  refine stepI f hres hsp P₂_₅ P₃ P₂_₅_proper P₃_proper v₂ (by decide)
    P₂_₅_is_variant_P₃ P₃_ballot_strict_subset_P₂_₅ comm_bcd comm_abc comm_abd ?_ hW_cases ?_
  · exact h_P₂_₅
  · simpa [ballot_ac] using h_gain_if_abc

-- P₃ → P₃_₅ (v₂ expands a ⊂ ad), singleton b in P₃_₅

lemma P₃_to_P₃_₅_is_variant :
    (mkInstance P₃_₅ P₃_₅_proper).is_i_variant (mkInstance P₃ P₃_proper) v₂ := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v
  · rfl
  · exact False.elim (hne rfl)
  · rfl

lemma P₃_ballot_strict_subset_P₃_₅ :
    (mkInstance P₃ P₃_proper).approves v₂ ⊂ (mkInstance P₃_₅ P₃_₅_proper).approves v₂ := by
  decide

lemma b_exclusive_singleton_P₃_₅ :
    Peters.SingletonApprovers.is_exclusive_singleton (mkInstance P₃_₅ P₃_₅_proper) (1 : C) := by
  refine exclusive_singleton_of_unique_supporter (inst := mkInstance P₃_₅ P₃_₅_proper)
    (c := (1 : C)) (v₀ := v₁) ?_ ?_ ?_
  · decide
  · rfl
  · intro v hv hne
    fin_cases v <;> simp [mkInstance, P₃_₅, ballot_b, ballot_ad, ballot_cd] at hv hne ⊢

lemma singleton_party_size_b_P₃_₅ :
    (mkInstance P₃_₅ P₃_₅_proper).singleton_party_size (1 : C) = 1 := by
  decide

lemma b_in_W_P₃_₅ (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness) :
    (1 : C) ∈ W f hres P₃_₅ P₃_₅_proper :=
  singleton_approver_in_W f hwf hres hprop hsp P₃_₅ P₃_₅_proper (1 : C)
    singleton_party_size_b_P₃_₅ b_exclusive_singleton_P₃_₅

lemma step5_f_P₃_₅_eq_abd (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness)
    (h_P₁ : W f hres P₁ P₁_proper = comm_acd) :
    W f hres P₃_₅ P₃_₅_proper = comm_abd := by
  have h_P₃ : W f hres P₃ P₃_proper = comm_abd :=
    step4_f_P₃_eq_abd f hwf hres hprop hsp h_P₁
  have hb : (1 : C) ∈ W f hres P₃_₅ P₃_₅_proper := b_in_W_P₃_₅ f hwf hres hprop hsp
  have h :
      W f hres P₃_₅ P₃_₅_proper = insert (1 : C) ballot_ad := by
    refine stepH f hwf hres hsp P₃ P₃_₅ P₃_proper P₃_₅_proper v₂ (by decide)
      P₃_to_P₃_₅_is_variant P₃_ballot_strict_subset_P₃_₅ ballot_ad rfl (1 : C) hb ?_ ?_ ?_
    · decide
    · decide
    · simpa [h_P₃]
  simpa [comm_abd] using h

-- P₃_₅ → P₄ (v₃ shrinks c ⊂ cd), P₄ is party-list with singleton b and c

lemma P₃_₅_is_variant_P₄ :
    (mkInstance P₃_₅ P₃_₅_proper).is_i_variant (mkInstance P₄ P₄_proper) v₃ := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v
  · rfl
  · rfl
  · exact False.elim (hne rfl)

lemma P₄_ballot_strict_subset_P₃_₅ :
    (mkInstance P₄ P₄_proper).approves v₃ ⊂ (mkInstance P₃_₅ P₃_₅_proper).approves v₃ := by
  decide

lemma b_in_W_P₄ (f : ABCRule V C k) (hres : f.IsResolute) (hprop : f.SatisfiesProportionality) :
    (1 : C) ∈ W f hres P₄ P₄_proper :=
  mem_W_of_prop_singleton_one f hres hprop P₄ P₄_proper P₄_is_party_list (1 : C) (by decide)

lemma c_in_W_P₄ (f : ABCRule V C k) (hres : f.IsResolute) (hprop : f.SatisfiesProportionality) :
    (2 : C) ∈ W f hres P₄ P₄_proper :=
  mem_W_of_prop_singleton_one f hres hprop P₄ P₄_proper P₄_is_party_list (2 : C) (by decide)

lemma step6_f_P₄_eq_abc (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness)
    (h_P₁ : W f hres P₁ P₁_proper = comm_acd) :
    W f hres P₄ P₄_proper = comm_abc := by
  have h_P₃_₅ : W f hres P₃_₅ P₃_₅_proper = comm_abd :=
    step5_f_P₃_₅_eq_abd f hwf hres hprop hsp h_P₁

  have hb : (1 : C) ∈ W f hres P₄ P₄_proper := b_in_W_P₄ f hres hprop
  have hc : (2 : C) ∈ W f hres P₄ P₄_proper := c_in_W_P₄ f hres hprop
  have hcard3 : (W f hres P₄ P₄_proper).card = 3 := by
    simpa [k] using (W_card f hwf hres P₄ P₄_proper)
  have hW_cases : W f hres P₄ P₄_proper = comm_abc ∨ W f hres P₄ P₄_proper = comm_bcd :=
    card3_mem_bc_cases _ hcard3 hb hc

  have h_gain_if_bcd :
      comm_bcd ∩ ballot_cd ⊃ comm_abd ∩ ballot_cd := by
    simp [comm_bcd, comm_abd, ballot_cd]
    decide

  -- Manipulator: v₃, true ballot cd at P₃_₅, reports c at P₄
  have hW_cases' : W f hres P₄ P₄_proper = comm_bcd ∨ W f hres P₄ P₄_proper = comm_abc := by
    rcases hW_cases with hEq | hEq
    · exact Or.inr hEq
    · exact Or.inl hEq
  refine stepI f hres hsp P₃_₅ P₄ P₃_₅_proper P₄_proper v₃ (by decide)
    P₃_₅_is_variant_P₄ P₄_ballot_strict_subset_P₃_₅ comm_abd comm_bcd comm_abc ?_ hW_cases' ?_
  · exact h_P₃_₅
  · simpa [ballot_cd] using h_gain_if_bcd

-- P₄ → P₄_₅ (v₃ expands c ⊂ ac), singleton b in P₄_₅

lemma P₄_to_P₄_₅_is_variant :
    (mkInstance P₄_₅ P₄_₅_proper).is_i_variant (mkInstance P₄ P₄_proper) v₃ := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v
  · rfl
  · rfl
  · exact False.elim (hne rfl)

lemma P₄_ballot_strict_subset_P₄_₅ :
    (mkInstance P₄ P₄_proper).approves v₃ ⊂ (mkInstance P₄_₅ P₄_₅_proper).approves v₃ := by
  decide

lemma b_exclusive_singleton_P₄_₅ :
    Peters.SingletonApprovers.is_exclusive_singleton (mkInstance P₄_₅ P₄_₅_proper) (1 : C) := by
  refine exclusive_singleton_of_unique_supporter (inst := mkInstance P₄_₅ P₄_₅_proper)
    (c := (1 : C)) (v₀ := v₁) ?_ ?_ ?_
  · decide
  · rfl
  · intro v hv hne
    fin_cases v <;> simp [mkInstance, P₄_₅, ballot_b, ballot_ad, ballot_ac] at hv hne ⊢

lemma singleton_party_size_b_P₄_₅ :
    (mkInstance P₄_₅ P₄_₅_proper).singleton_party_size (1 : C) = 1 := by
  decide

lemma b_in_W_P₄_₅ (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness) :
    (1 : C) ∈ W f hres P₄_₅ P₄_₅_proper :=
  singleton_approver_in_W f hwf hres hprop hsp P₄_₅ P₄_₅_proper (1 : C)
    singleton_party_size_b_P₄_₅ b_exclusive_singleton_P₄_₅

lemma step7_f_P₄_₅_eq_abc (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness)
    (h_P₁ : W f hres P₁ P₁_proper = comm_acd) :
    W f hres P₄_₅ P₄_₅_proper = comm_abc := by
  have h_P₄ : W f hres P₄ P₄_proper = comm_abc :=
    step6_f_P₄_eq_abc f hwf hres hprop hsp h_P₁
  have hb : (1 : C) ∈ W f hres P₄_₅ P₄_₅_proper := b_in_W_P₄_₅ f hwf hres hprop hsp
  have h :
      W f hres P₄_₅ P₄_₅_proper = insert (1 : C) ballot_ac := by
    refine stepH f hwf hres hsp P₄ P₄_₅ P₄_proper P₄_₅_proper v₃ (by decide)
      P₄_to_P₄_₅_is_variant P₄_ballot_strict_subset_P₄_₅ ballot_ac rfl (1 : C) hb ?_ ?_ ?_
    · decide
    · decide
    · simpa [h_P₄]
  simpa [comm_abc] using h

-- P₄_₅ → P₅ (v₂ shrinks d ⊂ ad), P₅ is party-list with singleton b and d

lemma P₄_₅_is_variant_P₅ :
    (mkInstance P₄_₅ P₄_₅_proper).is_i_variant (mkInstance P₅ P₅_proper) v₂ := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v
  · rfl
  · exact False.elim (hne rfl)
  · rfl

lemma P₅_ballot_strict_subset_P₄_₅ :
    (mkInstance P₅ P₅_proper).approves v₂ ⊂ (mkInstance P₄_₅ P₄_₅_proper).approves v₂ := by
  decide

lemma b_in_W_P₅ (f : ABCRule V C k) (hres : f.IsResolute) (hprop : f.SatisfiesProportionality) :
    (1 : C) ∈ W f hres P₅ P₅_proper :=
  mem_W_of_prop_singleton_one f hres hprop P₅ P₅_proper P₅_is_party_list (1 : C) (by decide)

lemma d_in_W_P₅ (f : ABCRule V C k) (hres : f.IsResolute) (hprop : f.SatisfiesProportionality) :
    (3 : C) ∈ W f hres P₅ P₅_proper :=
  mem_W_of_prop_singleton_one f hres hprop P₅ P₅_proper P₅_is_party_list (3 : C) (by decide)

lemma step8_f_P₅_eq_bcd (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness)
    (h_P₁ : W f hres P₁ P₁_proper = comm_acd) :
    W f hres P₅ P₅_proper = comm_bcd := by
  have h_P₄_₅ : W f hres P₄_₅ P₄_₅_proper = comm_abc :=
    step7_f_P₄_₅_eq_abc f hwf hres hprop hsp h_P₁

  have hb : (1 : C) ∈ W f hres P₅ P₅_proper := b_in_W_P₅ f hres hprop
  have hd : (3 : C) ∈ W f hres P₅ P₅_proper := d_in_W_P₅ f hres hprop
  have hcard3 : (W f hres P₅ P₅_proper).card = 3 := by
    simpa [k] using (W_card f hwf hres P₅ P₅_proper)
  have hW_cases : W f hres P₅ P₅_proper = comm_abd ∨ W f hres P₅ P₅_proper = comm_bcd :=
    card3_mem_bd_cases _ hcard3 hb hd

  have h_gain_if_abd :
      comm_abd ∩ ballot_ad ⊃ comm_abc ∩ ballot_ad := by
    simp [comm_abd, comm_abc, ballot_ad]
    decide

  refine stepI f hres hsp P₄_₅ P₅ P₄_₅_proper P₅_proper v₂ (by decide)
    P₄_₅_is_variant_P₅ P₅_ballot_strict_subset_P₄_₅ comm_abc comm_abd comm_bcd ?_ hW_cases ?_
  · exact h_P₄_₅
  · simpa [ballot_ad] using h_gain_if_abd

-- P₅ → P₅_₅ (v₂ expands d ⊂ cd), singleton b in P₅_₅

lemma P₅_to_P₅_₅_is_variant :
    (mkInstance P₅_₅ P₅_₅_proper).is_i_variant (mkInstance P₅ P₅_proper) v₂ := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v
  · rfl
  · exact False.elim (hne rfl)
  · rfl

lemma P₅_ballot_strict_subset_P₅_₅ :
    (mkInstance P₅ P₅_proper).approves v₂ ⊂ (mkInstance P₅_₅ P₅_₅_proper).approves v₂ := by
  decide

lemma b_exclusive_singleton_P₅_₅ :
    Peters.SingletonApprovers.is_exclusive_singleton (mkInstance P₅_₅ P₅_₅_proper) (1 : C) := by
  refine exclusive_singleton_of_unique_supporter (inst := mkInstance P₅_₅ P₅_₅_proper)
    (c := (1 : C)) (v₀ := v₁) ?_ ?_ ?_
  · decide
  · rfl
  · intro v hv hne
    fin_cases v <;> simp [mkInstance, P₅_₅, ballot_b, ballot_cd, ballot_ac] at hv hne ⊢

lemma singleton_party_size_b_P₅_₅ :
    (mkInstance P₅_₅ P₅_₅_proper).singleton_party_size (1 : C) = 1 := by
  decide

lemma b_in_W_P₅_₅ (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness) :
    (1 : C) ∈ W f hres P₅_₅ P₅_₅_proper :=
  singleton_approver_in_W f hwf hres hprop hsp P₅_₅ P₅_₅_proper (1 : C)
    singleton_party_size_b_P₅_₅ b_exclusive_singleton_P₅_₅

lemma step9_f_P₅_₅_eq_bcd (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness)
    (h_P₁ : W f hres P₁ P₁_proper = comm_acd) :
    W f hres P₅_₅ P₅_₅_proper = comm_bcd := by
  have h_P₅ : W f hres P₅ P₅_proper = comm_bcd :=
    step8_f_P₅_eq_bcd f hwf hres hprop hsp h_P₁
  have hb : (1 : C) ∈ W f hres P₅_₅ P₅_₅_proper := b_in_W_P₅_₅ f hwf hres hprop hsp
  have h :
      W f hres P₅_₅ P₅_₅_proper = insert (1 : C) ballot_cd := by
    refine stepH f hwf hres hsp P₅ P₅_₅ P₅_proper P₅_₅_proper v₂ (by decide)
      P₅_to_P₅_₅_is_variant P₅_ballot_strict_subset_P₅_₅ ballot_cd rfl (1 : C) hb ?_ ?_ ?_
    · decide
    · decide
    · simpa [h_P₅]
  simpa [comm_bcd] using h

-- P₅_₅ → P₆ (v₃ shrinks a ⊂ ac), P₆ is party-list with singleton a and b

lemma P₅_₅_is_variant_P₆ :
    (mkInstance P₅_₅ P₅_₅_proper).is_i_variant (mkInstance P₆ P₆_proper) v₃ := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v
  · rfl
  · rfl
  · exact False.elim (hne rfl)

lemma P₆_ballot_strict_subset_P₅_₅ :
    (mkInstance P₆ P₆_proper).approves v₃ ⊂ (mkInstance P₅_₅ P₅_₅_proper).approves v₃ := by
  decide

lemma a_in_W_P₆ (f : ABCRule V C k) (hres : f.IsResolute) (hprop : f.SatisfiesProportionality) :
    (0 : C) ∈ W f hres P₆ P₆_proper :=
  mem_W_of_prop_singleton_one f hres hprop P₆ P₆_proper P₆_is_party_list (0 : C) (by decide)

lemma b_in_W_P₆ (f : ABCRule V C k) (hres : f.IsResolute) (hprop : f.SatisfiesProportionality) :
    (1 : C) ∈ W f hres P₆ P₆_proper :=
  mem_W_of_prop_singleton_one f hres hprop P₆ P₆_proper P₆_is_party_list (1 : C) (by decide)

lemma step10_f_P₆_eq_abd (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness)
    (h_P₁ : W f hres P₁ P₁_proper = comm_acd) :
    W f hres P₆ P₆_proper = comm_abd := by
  have h_P₅_₅ : W f hres P₅_₅ P₅_₅_proper = comm_bcd :=
    step9_f_P₅_₅_eq_bcd f hwf hres hprop hsp h_P₁

  have ha : (0 : C) ∈ W f hres P₆ P₆_proper := a_in_W_P₆ f hres hprop
  have hb : (1 : C) ∈ W f hres P₆ P₆_proper := b_in_W_P₆ f hres hprop
  have hcard3 : (W f hres P₆ P₆_proper).card = 3 := by
    simpa [k] using (W_card f hwf hres P₆ P₆_proper)
  have hW_cases : W f hres P₆ P₆_proper = comm_abc ∨ W f hres P₆ P₆_proper = comm_abd :=
    card3_mem_ab_cases _ hcard3 ha hb

  have h_gain_if_abc :
      comm_abc ∩ ballot_ac ⊃ comm_bcd ∩ ballot_ac := by
    simp [comm_abc, comm_bcd, ballot_ac]
    decide

  -- Manipulator: v₃, true ballot ac at P₅_₅, reports a at P₆
  refine stepI f hres hsp P₅_₅ P₆ P₅_₅_proper P₆_proper v₃ (by decide)
    P₅_₅_is_variant_P₆ P₆_ballot_strict_subset_P₅_₅ comm_bcd comm_abc comm_abd ?_ hW_cases ?_
  · exact h_P₅_₅
  · simpa [ballot_ac] using h_gain_if_abc

-- P₆ → P₆_₅ (v₃ expands a ⊂ ad), singleton b in P₆_₅

lemma P₆_to_P₆_₅_is_variant :
    (mkInstance P₆_₅ P₆_₅_proper).is_i_variant (mkInstance P₆ P₆_proper) v₃ := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v
  · rfl
  · rfl
  · exact False.elim (hne rfl)

lemma P₆_ballot_strict_subset_P₆_₅ :
    (mkInstance P₆ P₆_proper).approves v₃ ⊂ (mkInstance P₆_₅ P₆_₅_proper).approves v₃ := by
  decide

lemma b_exclusive_singleton_P₆_₅ :
    Peters.SingletonApprovers.is_exclusive_singleton (mkInstance P₆_₅ P₆_₅_proper) (1 : C) := by
  refine exclusive_singleton_of_unique_supporter (inst := mkInstance P₆_₅ P₆_₅_proper)
    (c := (1 : C)) (v₀ := v₁) ?_ ?_ ?_
  · decide
  · rfl
  · intro v hv hne
    fin_cases v <;> simp [mkInstance, P₆_₅, ballot_b, ballot_cd, ballot_ad] at hv hne ⊢

lemma singleton_party_size_b_P₆_₅ :
    (mkInstance P₆_₅ P₆_₅_proper).singleton_party_size (1 : C) = 1 := by
  decide

lemma b_in_W_P₆_₅ (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness) :
    (1 : C) ∈ W f hres P₆_₅ P₆_₅_proper :=
  singleton_approver_in_W f hwf hres hprop hsp P₆_₅ P₆_₅_proper (1 : C)
    singleton_party_size_b_P₆_₅ b_exclusive_singleton_P₆_₅

lemma step11_f_P₆_₅_eq_abd (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness)
    (h_P₁ : W f hres P₁ P₁_proper = comm_acd) :
    W f hres P₆_₅ P₆_₅_proper = comm_abd := by
  have h_P₆ : W f hres P₆ P₆_proper = comm_abd :=
    step10_f_P₆_eq_abd f hwf hres hprop hsp h_P₁
  have hb : (1 : C) ∈ W f hres P₆_₅ P₆_₅_proper := b_in_W_P₆_₅ f hwf hres hprop hsp
  have h :
      W f hres P₆_₅ P₆_₅_proper = insert (1 : C) ballot_ad := by
    refine stepH f hwf hres hsp P₆ P₆_₅ P₆_proper P₆_₅_proper v₃ (by decide)
      P₆_to_P₆_₅_is_variant P₆_ballot_strict_subset_P₆_₅ ballot_ad rfl (1 : C) hb ?_ ?_ ?_
    · decide
    · decide
    · simpa [h_P₆]
  simpa [comm_abd] using h

-- P₆_₅ → P₇ (v₂ shrinks c ⊂ cd), P₇ is party-list with singleton b and c

lemma P₆_₅_is_variant_P₇ :
    (mkInstance P₆_₅ P₆_₅_proper).is_i_variant (mkInstance P₇ P₇_proper) v₂ := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v
  · rfl
  · exact False.elim (hne rfl)
  · rfl

lemma P₇_ballot_strict_subset_P₆_₅ :
    (mkInstance P₇ P₇_proper).approves v₂ ⊂ (mkInstance P₆_₅ P₆_₅_proper).approves v₂ := by
  decide

lemma b_in_W_P₇ (f : ABCRule V C k) (hres : f.IsResolute) (hprop : f.SatisfiesProportionality) :
    (1 : C) ∈ W f hres P₇ P₇_proper :=
  mem_W_of_prop_singleton_one f hres hprop P₇ P₇_proper P₇_is_party_list (1 : C) (by decide)

lemma c_in_W_P₇ (f : ABCRule V C k) (hres : f.IsResolute) (hprop : f.SatisfiesProportionality) :
    (2 : C) ∈ W f hres P₇ P₇_proper :=
  mem_W_of_prop_singleton_one f hres hprop P₇ P₇_proper P₇_is_party_list (2 : C) (by decide)

lemma step12_f_P₇_eq_abc (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness)
    (h_P₁ : W f hres P₁ P₁_proper = comm_acd) :
    W f hres P₇ P₇_proper = comm_abc := by
  have h_P₆_₅ : W f hres P₆_₅ P₆_₅_proper = comm_abd :=
    step11_f_P₆_₅_eq_abd f hwf hres hprop hsp h_P₁

  have hb : (1 : C) ∈ W f hres P₇ P₇_proper := b_in_W_P₇ f hres hprop
  have hc : (2 : C) ∈ W f hres P₇ P₇_proper := c_in_W_P₇ f hres hprop
  have hcard3 : (W f hres P₇ P₇_proper).card = 3 := by
    simpa [k] using (W_card f hwf hres P₇ P₇_proper)
  have hW_cases : W f hres P₇ P₇_proper = comm_abc ∨ W f hres P₇ P₇_proper = comm_bcd :=
    card3_mem_bc_cases _ hcard3 hb hc
  have hW_cases' : W f hres P₇ P₇_proper = comm_bcd ∨ W f hres P₇ P₇_proper = comm_abc := by
    rcases hW_cases with hEq | hEq
    · exact Or.inr hEq
    · exact Or.inl hEq

  have h_gain_if_bcd :
      comm_bcd ∩ ballot_cd ⊃ comm_abd ∩ ballot_cd := by
    simp [comm_bcd, comm_abd, ballot_cd]
    decide

  -- Manipulator: v₂, true ballot cd at P₆_₅, reports c at P₇
  refine stepI f hres hsp P₆_₅ P₇ P₆_₅_proper P₇_proper v₂ (by decide)
    P₆_₅_is_variant_P₇ P₇_ballot_strict_subset_P₆_₅ comm_abd comm_bcd comm_abc ?_ hW_cases' ?_
  · exact h_P₆_₅
  · simpa [ballot_cd] using h_gain_if_bcd

-- P₇ → P₇_₅ (v₁ expands b ⊂ ab), singleton c in P₇_₅

lemma P₇_to_P₇_₅_is_variant :
    (mkInstance P₇_₅ P₇_₅_proper).is_i_variant (mkInstance P₇ P₇_proper) v₁ := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v
  · exact False.elim (hne rfl)
  · rfl
  · rfl

lemma P₇_ballot_strict_subset_P₇_₅ :
    (mkInstance P₇ P₇_proper).approves v₁ ⊂ (mkInstance P₇_₅ P₇_₅_proper).approves v₁ := by
  decide

lemma c_exclusive_singleton_P₇_₅ :
    Peters.SingletonApprovers.is_exclusive_singleton (mkInstance P₇_₅ P₇_₅_proper) (2 : C) := by
  refine exclusive_singleton_of_unique_supporter (inst := mkInstance P₇_₅ P₇_₅_proper)
    (c := (2 : C)) (v₀ := v₂) ?_ ?_ ?_
  · decide
  · rfl
  · intro v hv hne
    fin_cases v <;> simp [mkInstance, P₇_₅, ballot_ab, ballot_c, ballot_ad] at hv hne ⊢

lemma singleton_party_size_c_P₇_₅ :
    (mkInstance P₇_₅ P₇_₅_proper).singleton_party_size (2 : C) = 1 := by
  decide

lemma c_in_W_P₇_₅ (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness) :
    (2 : C) ∈ W f hres P₇_₅ P₇_₅_proper :=
  singleton_approver_in_W f hwf hres hprop hsp P₇_₅ P₇_₅_proper (2 : C)
    singleton_party_size_c_P₇_₅ c_exclusive_singleton_P₇_₅

lemma step13_f_P₇_₅_eq_abc (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness)
    (h_P₁ : W f hres P₁ P₁_proper = comm_acd) :
    W f hres P₇_₅ P₇_₅_proper = comm_abc := by
  have h_P₇ : W f hres P₇ P₇_proper = comm_abc :=
    step12_f_P₇_eq_abc f hwf hres hprop hsp h_P₁
  have hc : (2 : C) ∈ W f hres P₇_₅ P₇_₅_proper := c_in_W_P₇_₅ f hwf hres hprop hsp
  have h :
      W f hres P₇_₅ P₇_₅_proper = insert (2 : C) ballot_ab := by
    refine stepH f hwf hres hsp P₇ P₇_₅ P₇_proper P₇_₅_proper v₁ (by decide)
      P₇_to_P₇_₅_is_variant P₇_ballot_strict_subset_P₇_₅ ballot_ab rfl (2 : C) hc ?_ ?_ ?_
    · decide
    · decide
    · simpa [h_P₇]
  simpa [comm_abc] using h

-- Final contradiction: from P₇_₅ back to P₁ via voter 3 shrinking ad → d

lemma P₇_₅_is_variant_P₁ :
    (mkInstance P₇_₅ P₇_₅_proper).is_i_variant (mkInstance P₁ P₁_proper) v₃ := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v
  · rfl
  · rfl
  · exact False.elim (hne rfl)

lemma P₁_ballot_strict_subset_P₇_₅ :
    (mkInstance P₁ P₁_proper).approves v₃ ⊂ (mkInstance P₇_₅ P₇_₅_proper).approves v₃ := by
  decide

theorem contradiction_from_P₁_eq_acd (f : ABCRule V C k) (hwf : f.IsWellFormed) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : f.SatisfiesResoluteStrategyproofness)
    (h_P₁ : W f hres P₁ P₁_proper = comm_acd) :
    False := by
  have h_P₇_₅ : W f hres P₇_₅ P₇_₅_proper = comm_abc :=
    step13_f_P₇_₅_eq_abc f hwf hres hprop hsp h_P₁

  have h_viol :
      W f hres P₁ P₁_proper ∩ ballot_ad ⊃ W f hres P₇_₅ P₇_₅_proper ∩ ballot_ad := by
    simp [h_P₁, h_P₇_₅, comm_acd, comm_abc, ballot_ad]
    decide

  have hno :=
    hsp (mkInstance P₇_₅ P₇_₅_proper) (mkInstance P₁ P₁_proper) v₃ (by decide)
      P₇_₅_is_variant_P₁ P₁_ballot_strict_subset_P₇_₅ hres
  -- SP forbids a strict improvement by reporting a strict subset
  exact hno (by simpa [W] using h_viol)

end Peters.BaseCaseACD
