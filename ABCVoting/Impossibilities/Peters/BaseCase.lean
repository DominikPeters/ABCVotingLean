import ABCVoting.ABCRule
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Fin4Card3
import ABCVoting.Impossibilities.Peters.BaseCaseACD
import ABCVoting.Impossibilities.Peters.BaseCaseBCD
import ABCVoting.Impossibilities.Peters.BaseCaseCommon

open Finset ABCInstance

namespace Peters.BaseCase

open Peters.BaseCaseCommon

abbrev V := Peters.BaseCaseCommon.V
abbrev C := Peters.BaseCaseCommon.C
abbrev k : ℕ := Peters.BaseCaseCommon.k

open Peters.BaseCaseACD

lemma P₁_is_party_list : (mkInstance P₁ P₁_proper).is_party_list := by
  intro v₁ _ v₂ _
  fin_cases v₁ <;> fin_cases v₂ <;> decide

lemma singleton_party_size_c_P₁ :
    (mkInstance P₁ P₁_proper).singleton_party_size (2 : C) = 1 := by
  decide

lemma singleton_party_size_d_P₁ :
    (mkInstance P₁ P₁_proper).singleton_party_size (3 : C) = 1 := by
  decide

lemma c_in_W_P₁ (f : ABCRule V C k) (hres : f.IsResolute) (hprop : f.SatisfiesProportionality) :
    (2 : C) ∈ W f hres P₁ P₁_proper :=
  mem_W_of_prop_singleton_one f hres hprop P₁ P₁_proper P₁_is_party_list (2 : C)
    singleton_party_size_c_P₁

lemma d_in_W_P₁ (f : ABCRule V C k) (hres : f.IsResolute) (hprop : f.SatisfiesProportionality) :
    (3 : C) ∈ W f hres P₁ P₁_proper :=
  mem_W_of_prop_singleton_one f hres hprop P₁ P₁_proper P₁_is_party_list (3 : C)
    singleton_party_size_d_P₁

lemma W_P₁_eq_W_P₁' (f : ABCRule V C k) (hres : f.IsResolute) :
    W f hres Peters.BaseCaseACD.P₁ Peters.BaseCaseACD.P₁_proper =
      W f hres Peters.BaseCaseBCD.P₁ Peters.BaseCaseBCD.P₁_proper := by
  classical
  -- The two instances have identical voters/candidates/approvals; only proof fields differ.
  have :
      f.resolute_committee
          (mkInstance Peters.BaseCaseACD.P₁ Peters.BaseCaseACD.P₁_proper) hres =
        f.resolute_committee
          (mkInstance Peters.BaseCaseBCD.P₁ Peters.BaseCaseBCD.P₁_proper) hres := by
    refine f.resolute_ballot_ext (hres := hres) (inst := _ ) (inst' := _) ?_ ?_ ?_
    · rfl
    · rfl
    · intro v _
      fin_cases v <;> rfl
  simpa [W] using this

theorem base_case_impossible
    (f : ABCRule V C k) (hwf : IsWellFormedOnPlentiful f) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f) :
    False := by
  have hc : (2 : C) ∈ W f hres P₁ P₁_proper := c_in_W_P₁ f hres hprop
  have hd : (3 : C) ∈ W f hres P₁ P₁_proper := d_in_W_P₁ f hres hprop

  have hcard3 : (W f hres P₁ P₁_proper).card = 3 := by
    simpa [k] using (W_card f hwf hres P₁ P₁_proper P₁_plentiful)

  set W₁ := W f hres P₁ P₁_proper

  have hcases :
      W₁ = Peters.BaseCaseACD.comm_abd ∨
      W₁ = Peters.BaseCaseACD.comm_acd ∨
      W₁ = Peters.BaseCaseACD.comm_bcd := by
    have : W₁ = ({0, 1, 3} : Finset (Fin 4)) ∨
        W₁ = ({0, 2, 3} : Finset (Fin 4)) ∨
        W₁ = ({1, 2, 3} : Finset (Fin 4)) := by
      simpa [W₁] using
        (ABCVoting.fin4_card3_mem_three (s := W₁) (hs := by simpa [W₁] using hcard3) (h3 := by simpa [W₁] using hd))
    rcases this with hW_eq_abd | hW_cases'
    · left
      simpa [Peters.BaseCaseACD.comm_abd] using hW_eq_abd
    rcases hW_cases' with hW_eq_acd | hW_eq_bcd
    · right; left
      simpa [Peters.BaseCaseACD.comm_acd] using hW_eq_acd
    · right; right
      simpa [Peters.BaseCaseACD.comm_bcd] using hW_eq_bcd

  rcases hcases with hW_eq_abd | hW_cases'
  · -- impossible since c ∈ W₁
    have : (2 : C) ∈ ({0, 1, 3} : Finset (Fin 4)) := by
      simpa [W₁, Peters.BaseCaseACD.comm_abd, hW_eq_abd] using hc
    cases (by decide : ¬(2 : C) ∈ ({0, 1, 3} : Finset (Fin 4))) this
  rcases hW_cases' with hW_eq_acd | hW_eq_bcd
  ·
    refine Peters.BaseCaseACD.contradiction_from_P₁_eq_acd f hwf hres hprop hsp ?_
    simpa [W₁] using hW_eq_acd
  · -- transfer the equality to the `BaseCaseBCD` version of `P₁`
    have hW_eq_bcd_ACD :
        W f hres Peters.BaseCaseACD.P₁ Peters.BaseCaseACD.P₁_proper =
          Peters.BaseCaseACD.comm_bcd := by
      simpa [W₁] using hW_eq_bcd
    have hcomm_bcd : Peters.BaseCaseACD.comm_bcd = Peters.BaseCaseBCD.comm_bcd := by
      ext x
      simp [Peters.BaseCaseACD.comm_bcd, Peters.BaseCaseBCD.comm_bcd]
    have hW_eq_bcd' :
        W f hres Peters.BaseCaseBCD.P₁ Peters.BaseCaseBCD.P₁_proper =
          Peters.BaseCaseBCD.comm_bcd := by
      calc
        W f hres Peters.BaseCaseBCD.P₁ Peters.BaseCaseBCD.P₁_proper
            = W f hres Peters.BaseCaseACD.P₁ Peters.BaseCaseACD.P₁_proper := by
          simpa using (W_P₁_eq_W_P₁' (f := f) (hres := hres)).symm
        _ = Peters.BaseCaseACD.comm_bcd := hW_eq_bcd_ACD
        _ = Peters.BaseCaseBCD.comm_bcd := by simpa [hcomm_bcd]
    exact Peters.BaseCaseBCD.contradiction_from_P₁_eq_bcd f hwf hres hprop hsp hW_eq_bcd'

end Peters.BaseCase
