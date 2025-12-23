import Mathlib.Data.Finset.Card

import ABCVoting.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.Peters.Fin4Card3
import ABCVoting.Impossibilities.KluivingDeVriesVrijbergenBoixelEndriss.InductionN
import ABCVoting.Impossibilities.KluivingDeVriesVrijbergenBoixelEndriss.SingletonApprovers

open Finset ABCInstance
open ABCVoting
open KluivingDeVriesVrijbergenBoixelEndriss.SingletonApprovers

namespace KluivingDeVriesVrijbergenBoixelEndriss.BaseCase

-- ============================================================================
-- TYPE SETUP
-- ============================================================================

abbrev V := Fin 3
abbrev C := Fin 4
abbrev k : ℕ := 3

abbrev v₁ : V := 0
abbrev v₂ : V := 1
abbrev v₃ : V := 2

abbrev a : C := 0
abbrev b : C := 1
abbrev c : C := 2
abbrev d : C := 3

def allCandidates : Finset C := univ
def allVoters : Finset V := univ

abbrev Profile := V → Finset C

def mkInstance (P : Profile) (h_proper : ∀ v : V, P v ⊂ allCandidates) :
    ABCInstance V C k where
  voters := allVoters
  candidates := allCandidates
  approves := P
  approves_subset := fun v _ => (h_proper v).subset
  voters_nonempty := by simp [allVoters]
  k_pos := by decide
  k_le_m := by simp [allCandidates]; decide

-- ============================================================================
-- PROFILES
-- ============================================================================

def P_A : Profile := fun v =>
  if v = v₁ then {c, d} else if v = v₂ then {a, c, d} else {b, c, d}

def P_A' : Profile := fun v =>
  if v = v₁ then {c, d} else if v = v₂ then {a} else {b, c, d}

def P_A'' : Profile := fun v =>
  if v = v₁ then {c, d} else if v = v₂ then {a, c, d} else {b}

lemma P_A_proper : ∀ v : V, P_A v ⊂ allCandidates := by
  intro v
  fin_cases v <;> decide

lemma P_A'_proper : ∀ v : V, P_A' v ⊂ allCandidates := by
  intro v
  fin_cases v <;> decide

lemma P_A''_proper : ∀ v : V, P_A'' v ⊂ allCandidates := by
  intro v
  fin_cases v <;> decide

abbrev instA : ABCInstance V C k := mkInstance P_A P_A_proper
abbrev instA' : ABCInstance V C k := mkInstance P_A' P_A'_proper
abbrev instA'' : ABCInstance V C k := mkInstance P_A'' P_A''_proper

def comm_acd : Finset C := {a, c, d}
def comm_bcd : Finset C := {b, c, d}

-- ============================================================================
-- DOMINANCE FACTS
-- ============================================================================

lemma dominates_c_a_A : instA.dominates c a := by
  refine ⟨?_, ?_⟩
  · intro v _ ha
    fin_cases v <;> simp [instA, mkInstance, P_A, v₁, v₂] at ha ⊢
  · refine ⟨v₁, by simp [instA, mkInstance, allVoters], ?_, ?_⟩
    · simp [instA, mkInstance, P_A, a, c, d]
    · simp [instA, mkInstance, P_A, a, c, d]

lemma dominates_c_b_A : instA.dominates c b := by
  refine ⟨?_, ?_⟩
  · intro v _ hb
    fin_cases v <;> simp [instA, mkInstance, P_A, v₁, v₂] at hb ⊢
  · refine ⟨v₁, by simp [instA, mkInstance, allVoters], ?_, ?_⟩
    · simp [instA, mkInstance, P_A, b, c, d]
    · simp [instA, mkInstance, P_A, b, c, d]

lemma dominates_d_a_A : instA.dominates d a := by
  refine ⟨?_, ?_⟩
  · intro v _ ha
    fin_cases v <;> simp [instA, mkInstance, P_A, v₁, v₂] at ha ⊢
  · refine ⟨v₁, by simp [instA, mkInstance, allVoters], ?_, ?_⟩
    · simp [instA, mkInstance, P_A, a, c, d]
    · simp [instA, mkInstance, P_A, a, c, d]

lemma dominates_d_b_A : instA.dominates d b := by
  refine ⟨?_, ?_⟩
  · intro v _ hb
    fin_cases v <;> simp [instA, mkInstance, P_A, v₁, v₂] at hb ⊢
  · refine ⟨v₁, by simp [instA, mkInstance, allVoters], ?_, ?_⟩
    · simp [instA, mkInstance, P_A, b, c, d]
    · simp [instA, mkInstance, P_A, b, c, d]

lemma dominates_c_b_A' : instA'.dominates c b := by
  refine ⟨?_, ?_⟩
  · intro v _ hb
    fin_cases v <;> simp [instA', mkInstance, P_A', v₁, v₂] at hb ⊢
  · refine ⟨v₁, by simp [instA', mkInstance, allVoters], ?_, ?_⟩
    · simp [instA', mkInstance, P_A', b, c, d]
    · simp [instA', mkInstance, P_A', b, c, d]

lemma dominates_d_b_A' : instA'.dominates d b := by
  refine ⟨?_, ?_⟩
  · intro v _ hb
    fin_cases v <;> simp [instA', mkInstance, P_A', v₁, v₂] at hb ⊢
  · refine ⟨v₁, by simp [instA', mkInstance, allVoters], ?_, ?_⟩
    · simp [instA', mkInstance, P_A', b, c, d]
    · simp [instA', mkInstance, P_A', b, c, d]

lemma dominates_c_a_A'' : instA''.dominates c a := by
  refine ⟨?_, ?_⟩
  · intro v _ ha
    fin_cases v <;> simp [instA'', mkInstance, P_A'', v₁, v₂] at ha ⊢
  · refine ⟨v₁, by simp [instA'', mkInstance, allVoters], ?_, ?_⟩
    · simp [instA'', mkInstance, P_A'', a, c, d]
    · simp [instA'', mkInstance, P_A'', a, c, d]

lemma dominates_d_a_A'' : instA''.dominates d a := by
  refine ⟨?_, ?_⟩
  · intro v _ ha
    fin_cases v <;> simp [instA'', mkInstance, P_A'', v₁, v₂] at ha ⊢
  · refine ⟨v₁, by simp [instA'', mkInstance, allVoters], ?_, ?_⟩
    · simp [instA'', mkInstance, P_A'', a, c, d]
    · simp [instA'', mkInstance, P_A'', a, c, d]

-- ============================================================================
-- C AND D MUST BE ELECTED
-- ============================================================================

lemma c_in_all_A (f : ABCRule V C k) (hwf : f.IsWellFormed)
    (heff : f.SatisfiesDominatingCandidateEfficiency) :
    ∀ W ∈ f instA, c ∈ W := by
  classical
  intro W hW
  by_contra hc
  have hW_card : W.card = k := (hwf instA).2 _ hW |>.1
  obtain ⟨x, hWx⟩ :=
    KluivingDeVriesVrijbergenBoixelEndriss.InductionN.committee_eq_erase_of_card (k := k) (W := W)
      (by simpa [k] using hW_card)
  have hc' : c ∉ (Finset.univ.erase x) := by simpa [hWx] using hc
  have hx : x = c := by
    by_contra hxc
    have hxc' : c ≠ x := by simpa [eq_comm] using hxc
    have : c ∈ (Finset.univ.erase x) := by simp [hxc']
    exact hc' this
  have haW : a ∈ W := by
    have : a ∈ (Finset.univ.erase c) := by simp [a, c]
    simpa [hWx, hx] using this
  have hcand : c ∈ instA.candidates := by simp [instA, mkInstance, allCandidates]
  have ha : a ∈ instA.candidates := by simp [instA, mkInstance, allCandidates]
  have hdom : instA.dominates c a := dominates_c_a_A
  have hcW := heff instA c a hcand ha hdom W hW haW
  exact hc hcW

lemma d_in_all_A (f : ABCRule V C k) (hwf : f.IsWellFormed)
    (heff : f.SatisfiesDominatingCandidateEfficiency) :
    ∀ W ∈ f instA, d ∈ W := by
  classical
  intro W hW
  by_contra hd
  have hW_card : W.card = k := (hwf instA).2 _ hW |>.1
  obtain ⟨x, hWx⟩ :=
    KluivingDeVriesVrijbergenBoixelEndriss.InductionN.committee_eq_erase_of_card (k := k) (W := W)
      (by simpa [k] using hW_card)
  have hd' : d ∉ (Finset.univ.erase x) := by simpa [hWx] using hd
  have hx : x = d := by
    by_contra hxd
    have hxd' : d ≠ x := by simpa [eq_comm] using hxd
    have : d ∈ (Finset.univ.erase x) := by simp [hxd']
    exact hd' this
  have haW : a ∈ W := by
    have : a ∈ (Finset.univ.erase d) := by simp [a, d]
    simpa [hWx, hx] using this
  have hcand : d ∈ instA.candidates := by simp [instA, mkInstance, allCandidates]
  have ha : a ∈ instA.candidates := by simp [instA, mkInstance, allCandidates]
  have hdom : instA.dominates d a := dominates_d_a_A
  have hdW := heff instA d a hcand ha hdom W hW haW
  exact hd hdW

lemma c_in_all_A' (f : ABCRule V C k) (hwf : f.IsWellFormed)
    (heff : f.SatisfiesDominatingCandidateEfficiency) :
    ∀ W ∈ f instA', c ∈ W := by
  classical
  intro W hW
  by_contra hc
  have hW_card : W.card = k := (hwf instA').2 _ hW |>.1
  obtain ⟨x, hWx⟩ :=
    KluivingDeVriesVrijbergenBoixelEndriss.InductionN.committee_eq_erase_of_card (k := k) (W := W)
      (by simpa [k] using hW_card)
  have hc' : c ∉ (Finset.univ.erase x) := by simpa [hWx] using hc
  have hx : x = c := by
    by_contra hxc
    have hxc' : c ≠ x := by simpa [eq_comm] using hxc
    have : c ∈ (Finset.univ.erase x) := by simp [hxc']
    exact hc' this
  have hbW : b ∈ W := by
    have : b ∈ (Finset.univ.erase c) := by simp [b, c]
    simpa [hWx, hx] using this
  have hcand : c ∈ instA'.candidates := by simp [instA', mkInstance, allCandidates]
  have hb : b ∈ instA'.candidates := by simp [instA', mkInstance, allCandidates]
  have hdom : instA'.dominates c b := dominates_c_b_A'
  have hcW := heff instA' c b hcand hb hdom W hW hbW
  exact hc hcW

lemma d_in_all_A' (f : ABCRule V C k) (hwf : f.IsWellFormed)
    (heff : f.SatisfiesDominatingCandidateEfficiency) :
    ∀ W ∈ f instA', d ∈ W := by
  classical
  intro W hW
  by_contra hd
  have hW_card : W.card = k := (hwf instA').2 _ hW |>.1
  obtain ⟨x, hWx⟩ :=
    KluivingDeVriesVrijbergenBoixelEndriss.InductionN.committee_eq_erase_of_card (k := k) (W := W)
      (by simpa [k] using hW_card)
  have hd' : d ∉ (Finset.univ.erase x) := by simpa [hWx] using hd
  have hx : x = d := by
    by_contra hxd
    have hxd' : d ≠ x := by simpa [eq_comm] using hxd
    have : d ∈ (Finset.univ.erase x) := by simp [hxd']
    exact hd' this
  have hbW : b ∈ W := by
    have : b ∈ (Finset.univ.erase d) := by simp [b, d]
    simpa [hWx, hx] using this
  have hcand : d ∈ instA'.candidates := by simp [instA', mkInstance, allCandidates]
  have hb : b ∈ instA'.candidates := by simp [instA', mkInstance, allCandidates]
  have hdom : instA'.dominates d b := dominates_d_b_A'
  have hdW := heff instA' d b hcand hb hdom W hW hbW
  exact hd hdW

lemma c_in_all_A'' (f : ABCRule V C k) (hwf : f.IsWellFormed)
    (heff : f.SatisfiesDominatingCandidateEfficiency) :
    ∀ W ∈ f instA'', c ∈ W := by
  classical
  intro W hW
  by_contra hc
  have hW_card : W.card = k := (hwf instA'').2 _ hW |>.1
  obtain ⟨x, hWx⟩ :=
    KluivingDeVriesVrijbergenBoixelEndriss.InductionN.committee_eq_erase_of_card (k := k) (W := W)
      (by simpa [k] using hW_card)
  have hc' : c ∉ (Finset.univ.erase x) := by simpa [hWx] using hc
  have hx : x = c := by
    by_contra hxc
    have hxc' : c ≠ x := by simpa [eq_comm] using hxc
    have : c ∈ (Finset.univ.erase x) := by simp [hxc']
    exact hc' this
  have haW : a ∈ W := by
    have : a ∈ (Finset.univ.erase c) := by simp [a, c]
    simpa [hWx, hx] using this
  have hcand : c ∈ instA''.candidates := by simp [instA'', mkInstance, allCandidates]
  have ha : a ∈ instA''.candidates := by simp [instA'', mkInstance, allCandidates]
  have hdom : instA''.dominates c a := dominates_c_a_A''
  have hcW := heff instA'' c a hcand ha hdom W hW haW
  exact hc hcW

lemma d_in_all_A'' (f : ABCRule V C k) (hwf : f.IsWellFormed)
    (heff : f.SatisfiesDominatingCandidateEfficiency) :
    ∀ W ∈ f instA'', d ∈ W := by
  classical
  intro W hW
  by_contra hd
  have hW_card : W.card = k := (hwf instA'').2 _ hW |>.1
  obtain ⟨x, hWx⟩ :=
    KluivingDeVriesVrijbergenBoixelEndriss.InductionN.committee_eq_erase_of_card (k := k) (W := W)
      (by simpa [k] using hW_card)
  have hd' : d ∉ (Finset.univ.erase x) := by simpa [hWx] using hd
  have hx : x = d := by
    by_contra hxd
    have hxd' : d ≠ x := by simpa [eq_comm] using hxd
    have : d ∈ (Finset.univ.erase x) := by simp [hxd']
    exact hd' this
  have haW : a ∈ W := by
    have : a ∈ (Finset.univ.erase d) := by simp [a, d]
    simpa [hWx, hx] using this
  have hcand : d ∈ instA''.candidates := by simp [instA'', mkInstance, allCandidates]
  have ha : a ∈ instA''.candidates := by simp [instA'', mkInstance, allCandidates]
  have hdom : instA''.dominates d a := dominates_d_a_A''
  have hdW := heff instA'' d a hcand ha hdom W hW haW
  exact hd hdW

-- ============================================================================
-- EXCLUSIVE SINGLETONS
-- ============================================================================

lemma a_exclusive_A' : is_exclusive_singleton instA' a := by
  classical
  refine ⟨?_, ?_⟩
  · refine ⟨v₂, ?_⟩
    apply (mem_singleton_party_iff instA' a v₂).2
    refine ⟨?_, ?_⟩
    · simp [instA', mkInstance, allVoters]
    · simp [instA', mkInstance, P_A', v₁, v₂, a]
  · ext v
    fin_cases v <;>
      (simp [instA', mkInstance, P_A', ABCInstance.singleton_party,
        ABCInstance.supporters, allVoters, v₁, v₂, a, b, c, d] <;> decide)

lemma b_exclusive_A'' : is_exclusive_singleton instA'' b := by
  classical
  refine ⟨?_, ?_⟩
  · refine ⟨v₃, ?_⟩
    apply (mem_singleton_party_iff instA'' b v₃).2
    refine ⟨?_, ?_⟩
    · simp [instA'', mkInstance, allVoters]
    · simp [instA'', mkInstance, P_A'', v₁, v₂, v₃, b]
  · ext v
    fin_cases v <;>
      (simp [instA'', mkInstance, P_A'', ABCInstance.singleton_party,
        ABCInstance.supporters, allVoters, v₁, v₂, a, b, c, d] <;> decide)

lemma singleton_party_a_A' : instA'.singleton_party a = {v₂} := by
  classical
  ext v
  fin_cases v <;>
    (simp [instA', mkInstance, P_A', ABCInstance.singleton_party,
      allVoters, v₁, v₂, a, b, c, d] <;> decide)

lemma singleton_party_b_A'' : instA''.singleton_party b = {v₃} := by
  classical
  ext v
  fin_cases v <;>
    (simp [instA'', mkInstance, P_A'', ABCInstance.singleton_party,
      allVoters, v₁, v₂, a, b, c, d] <;> decide)

lemma singleton_party_size_a_A' : instA'.singleton_party_size a = 1 := by
  calc
    instA'.singleton_party_size a = (instA'.singleton_party a).card := rfl
    _ = ({v₂} : Finset V).card := by simpa [singleton_party_a_A']
    _ = 1 := by simp

lemma singleton_party_size_b_A'' : instA''.singleton_party_size b = 1 := by
  calc
    instA''.singleton_party_size b = (instA''.singleton_party b).card := rfl
    _ = ({v₃} : Finset V).card := by simpa [singleton_party_b_A'']
    _ = 1 := by simp

-- ============================================================================
-- A' AND A'' OUTCOMES
-- ============================================================================

lemma A'_only_acd (f : ABCRule V C k)
    (hwf : f.IsWellFormed) (hprop : f.SatisfiesMinimalProportionality)
    (hsp : f.SatisfiesCautiousStrategyproofness)
    (heff : f.SatisfiesDominatingCandidateEfficiency) :
    ∀ W ∈ f instA', W = comm_acd := by
  intro W hW
  have haW : a ∈ W := by
    have hcand : a ∈ instA'.candidates := by simp [instA', mkInstance, allCandidates]
    have hsize :
        instA'.singleton_party_size a * k ≥ instA'.voters.card := by
      have hsize1 : instA'.singleton_party_size a = 1 := singleton_party_size_a_A'
      have hvoters : instA'.voters.card = 3 := by
        simp [instA', mkInstance, allVoters]
      simp [hsize1, hvoters, k]
    have ha := singleton_approvers_elected (inst := instA') (c := a)
      hcand hsize a_exclusive_A' f hwf hprop hsp W hW
    exact ha
  have hcW : c ∈ W := c_in_all_A' f hwf heff W hW
  have hdW : d ∈ W := d_in_all_A' f hwf heff W hW
  have hcardW : W.card = k := (hwf instA').2 _ hW |>.1
  have hsubset : comm_acd ⊆ W := by
    intro x hx
    have hx' : x = a ∨ x = c ∨ x = d := by
      simpa [comm_acd, a, c, d] using hx
    rcases hx' with rfl | hx'
    · exact haW
    rcases hx' with rfl | rfl
    · exact hcW
    exact hdW
  have hle : W.card ≤ comm_acd.card := by
    simpa [comm_acd, hcardW, k, a, c, d] using (Nat.le_refl k)
  exact (Finset.eq_of_subset_of_card_le hsubset hle).symm

lemma A''_only_bcd (f : ABCRule V C k)
    (hwf : f.IsWellFormed) (hprop : f.SatisfiesMinimalProportionality)
    (hsp : f.SatisfiesCautiousStrategyproofness)
    (heff : f.SatisfiesDominatingCandidateEfficiency) :
    ∀ W ∈ f instA'', W = comm_bcd := by
  intro W hW
  have hbW : b ∈ W := by
    have hcand : b ∈ instA''.candidates := by simp [instA'', mkInstance, allCandidates]
    have hsize :
        instA''.singleton_party_size b * k ≥ instA''.voters.card := by
      have hsize1 : instA''.singleton_party_size b = 1 := singleton_party_size_b_A''
      have hvoters : instA''.voters.card = 3 := by
        simp [instA'', mkInstance, allVoters]
      simp [hsize1, hvoters, k]
    have hb := singleton_approvers_elected (inst := instA'') (c := b)
      hcand hsize b_exclusive_A'' f hwf hprop hsp W hW
    exact hb
  have hcW : c ∈ W := c_in_all_A'' f hwf heff W hW
  have hdW : d ∈ W := d_in_all_A'' f hwf heff W hW
  have hcardW : W.card = k := (hwf instA'').2 _ hW |>.1
  have hsubset : comm_bcd ⊆ W := by
    intro x hx
    have hx' : x = b ∨ x = c ∨ x = d := by
      simpa [comm_bcd, b, c, d] using hx
    rcases hx' with rfl | hx'
    · exact hbW
    rcases hx' with rfl | rfl
    · exact hcW
    exact hdW
  have hle : W.card ≤ comm_bcd.card := by
    simpa [comm_bcd, hcardW, k, b, c, d] using (Nat.le_refl k)
  exact (Finset.eq_of_subset_of_card_le hsubset hle).symm

-- ============================================================================
-- BASE CASE IMPOSSIBILITY
-- ============================================================================

theorem base_case_impossible
    (f : ABCRule V C k)
    (hwf : f.IsWellFormed)
    (heff : f.SatisfiesDominatingCandidateEfficiency)
    (hprop : f.SatisfiesMinimalProportionality)
    (hsp : f.SatisfiesCautiousStrategyproofness) :
    False := by
  classical
  -- outcomes for A' and A''
  have hA'nonempty : (f instA').Nonempty := (hwf instA').1
  have hA''nonempty : (f instA'').Nonempty := (hwf instA'').1
  rcases hA'nonempty with ⟨W', hW'⟩
  have hW'_eq : W' = comm_acd :=
    A'_only_acd f hwf hprop hsp heff W' hW'
  have hA'_mem : comm_acd ∈ f instA' := by simpa [hW'_eq] using hW'
  rcases hA''nonempty with ⟨W'', hW''⟩
  have hW''_eq : W'' = comm_bcd :=
    A''_only_bcd f hwf hprop hsp heff W'' hW''
  have hA''_mem : comm_bcd ∈ f instA'' := by simpa [hW''_eq] using hW''

  -- committees in A must include c and d
  have hcdA : ∀ W ∈ f instA, c ∈ W ∧ d ∈ W := by
    intro W hW
    exact ⟨c_in_all_A f hwf heff W hW, d_in_all_A f hwf heff W hW⟩

  -- if bcd is in A, voter 2 can manipulate to A'
  have hA_no_bcd : comm_bcd ∉ f instA := by
    intro hbcd
    have hvar : instA.is_i_variant instA' v₂ := by
      refine ⟨rfl, rfl, ?_⟩
      intro v _ hne
      fin_cases v <;>
        simp [instA, instA', mkInstance, P_A, P_A', v₁, v₂] at hne ⊢
    have hv2 : v₂ ∈ instA.voters := by simp [instA, mkInstance, allVoters]
    have h_prefeq :
        cautious_prefeq (instA.approves v₂) (f instA') (f instA) := by
      intro W hW W' hW'
      have hW_eq : W = comm_acd := A'_only_acd f hwf hprop hsp heff W hW
      have hW'cases :
          W' = comm_acd ∨ W' = comm_bcd := by
        have hcardW' : W'.card = k := (hwf instA).2 _ hW' |>.1
        have hcW' : c ∈ W' := (hcdA W' hW').1
        have hdW' : d ∈ W' := (hcdA W' hW').2
        have hcases :
            W' = ({a, c, d} : Finset C) ∨
            W' = ({b, c, d} : Finset C) := by
          have h3 :
              W' = ({0, 2, 3} : Finset (Fin 4)) ∨
              W' = ({1, 2, 3} : Finset (Fin 4)) := by
            have hcases' :=
              ABCVoting.fin4_card3_mem_two (s := W')
                (hs := by simpa [k] using hcardW') (h2 := by simpa using hcW')
            rcases hcases' with h0 | hcases''
            · -- eliminate {0,1,2} using d ∈ W'
              exfalso
              have : (3 : Fin 4) ∈ ({0, 1, 2} : Finset (Fin 4)) := by
                simpa [h0, d] using hdW'
              simpa using this
            · rcases hcases'' with h1 | h2
              · left; exact h1
              · right; exact h2
          simpa [comm_acd, comm_bcd] using h3
        rcases hcases with hW' | hW'
        · left; exact hW'
        · right; exact hW'
      rcases hW'cases with hW'acd | hW'bcd
      · subst hW_eq; subst hW'acd
        simp [committee_prefeq, instA, mkInstance, P_A]
      · subst hW_eq; subst hW'bcd
        have hA2 : instA.approves v₂ = {a, c, d} := by
          simp [instA, mkInstance, P_A, v₁, v₂, a, c, d]
        have h_inter :
            ({b, c, d} : Finset C) ∩ ({a, c, d} : Finset C) = ({c, d} : Finset C) := by
          decide
        simp [committee_prefeq, hA2, comm_acd, comm_bcd, h_inter, a, b, c, d]
    have h_not_prefeq :
        ¬cautious_prefeq (instA.approves v₂) (f instA) (f instA') := by
      intro h
      have : committee_prefeq (instA.approves v₂) comm_bcd comm_acd := by
        have := h comm_bcd hbcd comm_acd hA'_mem
        simpa using this
      have hcontra : ¬committee_prefeq (instA.approves v₂) comm_bcd comm_acd := by
        have hA2 : instA.approves v₂ = {a, c, d} := by
          simp [instA, mkInstance, P_A, v₁, v₂, a, c, d]
        have h_inter :
            ({b, c, d} : Finset C) ∩ ({a, c, d} : Finset C) = ({c, d} : Finset C) := by
          decide
        simp [committee_prefeq, hA2, comm_acd, comm_bcd, h_inter, a, b, c, d]
      exact hcontra (by simpa using this)
    have hpref : cautious_pref (instA.approves v₂) (f instA') (f instA) :=
      ⟨h_prefeq, h_not_prefeq⟩
    exact hsp instA instA' v₂ hv2 hvar hpref

  -- if acd is in A, voter 3 can manipulate to A''
  have hA_no_acd : comm_acd ∉ f instA := by
    intro hacd
    have hvar : instA.is_i_variant instA'' v₃ := by
      refine ⟨rfl, rfl, ?_⟩
      intro v _ hne
      fin_cases v <;>
        simp [instA, instA'', mkInstance, P_A, P_A'', v₁, v₂, v₃] at hne ⊢
    have hv3 : v₃ ∈ instA.voters := by simp [instA, mkInstance, allVoters]
    have h_prefeq :
        cautious_prefeq (instA.approves v₃) (f instA'') (f instA) := by
      intro W hW W' hW'
      have hW_eq : W = comm_bcd := A''_only_bcd f hwf hprop hsp heff W hW
      have hW'cases :
          W' = comm_acd ∨ W' = comm_bcd := by
        have hcardW' : W'.card = k := (hwf instA).2 _ hW' |>.1
        have hcW' : c ∈ W' := (hcdA W' hW').1
        have hdW' : d ∈ W' := (hcdA W' hW').2
        have hcases :
            W' = ({a, c, d} : Finset C) ∨
            W' = ({b, c, d} : Finset C) := by
          have h3 :
              W' = ({0, 2, 3} : Finset (Fin 4)) ∨
              W' = ({1, 2, 3} : Finset (Fin 4)) := by
            have hcases' :=
              ABCVoting.fin4_card3_mem_two (s := W')
                (hs := by simpa [k] using hcardW') (h2 := by simpa using hcW')
            rcases hcases' with h0 | hcases''
            · exfalso
              have : (3 : Fin 4) ∈ ({0, 1, 2} : Finset (Fin 4)) := by
                simpa [h0, d] using hdW'
              simpa using this
            · rcases hcases'' with h1 | h2
              · left; exact h1
              · right; exact h2
          simpa [comm_acd, comm_bcd] using h3
        rcases hcases with hW' | hW'
        · left; exact hW'
        · right; exact hW'
      rcases hW'cases with hW'acd | hW'bcd
      · subst hW_eq; subst hW'acd
        have hA3 : instA.approves v₃ = {b, c, d} := by
          simp [instA, mkInstance, P_A, v₁, v₂, v₃, b, c, d]
        have h_inter :
            ({a, c, d} : Finset C) ∩ ({b, c, d} : Finset C) = ({c, d} : Finset C) := by
          decide
        simp [committee_prefeq, hA3, comm_acd, comm_bcd, h_inter, a, b, c, d]
      · subst hW_eq; subst hW'bcd
        simp [committee_prefeq, instA, mkInstance, P_A]
    have h_not_prefeq :
        ¬cautious_prefeq (instA.approves v₃) (f instA) (f instA'') := by
      intro h
      have : committee_prefeq (instA.approves v₃) comm_acd comm_bcd := by
        have := h comm_acd hacd comm_bcd hA''_mem
        simpa using this
      have hcontra : ¬committee_prefeq (instA.approves v₃) comm_acd comm_bcd := by
        have hA3 : instA.approves v₃ = {b, c, d} := by
          simp [instA, mkInstance, P_A, v₁, v₂, v₃, b, c, d]
        have h_inter :
            ({a, c, d} : Finset C) ∩ ({b, c, d} : Finset C) = ({c, d} : Finset C) := by
          decide
        simp [committee_prefeq, hA3, comm_acd, comm_bcd, h_inter, a, b, c, d]
      exact hcontra (by simpa using this)
    have hpref : cautious_pref (instA.approves v₃) (f instA'') (f instA) :=
      ⟨h_prefeq, h_not_prefeq⟩
    exact hsp instA instA'' v₃ hv3 hvar hpref

  have hA_nonempty : (f instA).Nonempty := (hwf instA).1
  rcases hA_nonempty with ⟨W, hW⟩
  have hW_cases :
      W = comm_acd ∨ W = comm_bcd := by
    have hcardW : W.card = k := (hwf instA).2 _ hW |>.1
    have hcW : c ∈ W := (hcdA W hW).1
    have hdW : d ∈ W := (hcdA W hW).2
    have h3 :
        W = ({0, 2, 3} : Finset (Fin 4)) ∨
        W = ({1, 2, 3} : Finset (Fin 4)) := by
      have hcases :=
        ABCVoting.fin4_card3_mem_two (s := W) (hs := by simpa [k] using hcardW) (h2 := by simpa using hcW)
      rcases hcases with h0 | hcases'
      · exfalso
        have : (3 : Fin 4) ∈ ({0, 1, 2} : Finset (Fin 4)) := by
          simpa [h0, d] using hdW
        simpa using this
      · rcases hcases' with h1 | h2
        · left; exact h1
        · right; exact h2
    simpa [comm_acd, comm_bcd] using h3
  rcases hW_cases with hW_eq | hW_eq
  · exact hA_no_acd (by simpa [hW_eq] using hW)
  · exact hA_no_bcd (by simpa [hW_eq] using hW)

end KluivingDeVriesVrijbergenBoixelEndriss.BaseCase
