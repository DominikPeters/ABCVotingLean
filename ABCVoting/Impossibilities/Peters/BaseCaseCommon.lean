import ABCVoting.ABCRule
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.Peters.SingletonApprovers
import ABCVoting.Impossibilities.Peters.RestrictToPlentiful

open Finset ABCInstance

namespace Peters.BaseCaseCommon

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

lemma W_card (f : ABCRule V C k) (hwf : IsWellFormedOnPlentiful f) (hres : f.IsResolute)
    (P : Profile) (h_proper : ∀ v : V, P v ⊂ allCandidates)
    (hpl : (mkInstance P h_proper).plentiful) :
    (W f hres P h_proper).card = k := by
  have hmem := f.resolute_committee_mem (mkInstance P h_proper) hres
  exact (hwf (mkInstance P h_proper) hpl).2 _ hmem |>.1

-- ============================================================================
-- GENERIC STEPS (LEMMA H / LEMMA I)
-- ============================================================================

lemma stepH
    (f : ABCRule V C k) (hwf : IsWellFormedOnPlentiful f) (hres : f.IsResolute)
    (hsp : Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f)
    (P_from P_to : Profile)
    (h_from : ∀ v : V, P_from v ⊂ allCandidates)
    (h_to : ∀ v : V, P_to v ⊂ allCandidates)
    (i : V) (hi : i ∈ (mkInstance P_to h_to).voters)
    (hvar : (mkInstance P_to h_to).is_i_variant (mkInstance P_from h_from) i)
    (hsub : (mkInstance P_from h_from).approves i ⊂ (mkInstance P_to h_to).approves i)
    (hpl_from : (mkInstance P_from h_from).plentiful)
    (hpl_to : (mkInstance P_to h_to).plentiful)
    (A : Finset C) (hA : (mkInstance P_to h_to).approves i = A)
    (z : C) (hz : z ∈ W f hres P_to h_to)
    (hzA : z ∉ A)
    (hA_card : A.card = 2)
    (h_prev : W f hres P_from h_from = insert z A) :
    W f hres P_to h_to = insert z A := by
  classical
  set inst_to := mkInstance P_to h_to
  set inst_from := mkInstance P_from h_from
  set W_to := W f hres P_to h_to
  set W_from := W f hres P_from h_from

  have hW_to_card3 : W_to.card = 3 := by
    simpa [W_to, k] using (W_card f hwf hres P_to h_to hpl_to)

  have hW_from_inter : W_from ∩ A = A := by
    have h : insert z A ∩ A = A := by
      simpa using (Finset.inter_eq_right.mpr (Finset.subset_insert z A))
    simpa [W_from, h_prev] using h

  have hA_sub_W_to : A ⊆ W_to := by
    by_contra hnot
    rcases not_subset.mp hnot with ⟨x, hxA, hxnot⟩
    have h_inter_ss : W_to ∩ A ⊂ A := by
      refine (Finset.ssubset_iff_subset_ne).2 ?_
      refine ⟨Finset.inter_subset_right, ?_⟩
      intro hEq
      have hx_in : x ∈ W_to ∩ A := by simpa [hEq] using hxA
      exact hxnot (Finset.mem_inter.mp hx_in).1
    have h_viol : W_from ∩ A ⊃ W_to ∩ A := by
      simpa [hW_from_inter] using h_inter_ss
    have hno :=
      hsp inst_to inst_from i hpl_to hpl_from hi hvar (by simpa [inst_from, inst_to] using hsub) hres
    have h_viol' :
        f.resolute_committee inst_from hres ∩ inst_to.approves i ⊃
          f.resolute_committee inst_to hres ∩ inst_to.approves i := by
      simpa [W, W_from, W_to, hA] using h_viol
    exact (hno h_viol')

  have h_target_sub : insert z A ⊆ W_to := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxA'
    · exact hz
    · exact hA_sub_W_to hxA'

  have h_target_card3 : (insert z A).card = 3 := by
    simp [Finset.card_insert_of_notMem, hzA, hA_card]

  have hle : W_to.card ≤ (insert z A).card := by
    simpa [hW_to_card3, h_target_card3]

  have hEq : insert z A = W_to :=
    Finset.eq_of_subset_of_card_le h_target_sub hle
  exact hEq.symm

lemma stepI
    (f : ABCRule V C k) (hres : f.IsResolute) (hsp : Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f)
    (P_true P_party : Profile)
    (h_true : ∀ v : V, P_true v ⊂ allCandidates)
    (h_party : ∀ v : V, P_party v ⊂ allCandidates)
    (i : V) (hi : i ∈ (mkInstance P_true h_true).voters)
    (hvar : (mkInstance P_true h_true).is_i_variant (mkInstance P_party h_party) i)
    (hsub : (mkInstance P_party h_party).approves i ⊂ (mkInstance P_true h_true).approves i)
    (hpl_true : (mkInstance P_true h_true).plentiful)
    (hpl_party : (mkInstance P_party h_party).plentiful)
    (W_true W_bad W_good : Finset C)
    (hW_true : W f hres P_true h_true = W_true)
    (hW_cases : W f hres P_party h_party = W_bad ∨ W f hres P_party h_party = W_good)
    (h_gain_if_bad :
      W_bad ∩ (mkInstance P_true h_true).approves i ⊃ W_true ∩ (mkInstance P_true h_true).approves i) :
    W f hres P_party h_party = W_good := by
  classical
  have hno :=
    hsp (mkInstance P_true h_true) (mkInstance P_party h_party) i hpl_true hpl_party hi hvar hsub hres

  have hW_ne_bad : W f hres P_party h_party ≠ W_bad := by
    intro hEq
    have h_viol :
        f.resolute_committee (mkInstance P_party h_party) hres ∩ (mkInstance P_true h_true).approves i ⊃
          f.resolute_committee (mkInstance P_true h_true) hres ∩ (mkInstance P_true h_true).approves i := by
      have h_gain :
          W f hres P_party h_party ∩ (mkInstance P_true h_true).approves i ⊃
            W f hres P_true h_true ∩ (mkInstance P_true h_true).approves i := by
        simpa [hEq.symm, hW_true] using h_gain_if_bad
      simpa [W] using h_gain
    exact (hno h_viol)

  rcases hW_cases with hEqBad | hEqGood
  · exact False.elim (hW_ne_bad hEqBad)
  · exact hEqGood

-- ============================================================================
-- HELPER LEMMAS USED THROUGHOUT THE CHAIN
-- ============================================================================

lemma mem_W_of_prop_singleton_one (f : ABCRule V C k) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality)
    (P : Profile) (hP : ∀ v : V, P v ⊂ allCandidates)
    (hpl : (mkInstance P hP).is_party_list)
    (c : C) (hsize : (mkInstance P hP).singleton_party_size c = 1) :
    c ∈ W f hres P hP := by
  have hc : c ∈ (mkInstance P hP).candidates := by
    simpa [mkInstance, allCandidates] using (Finset.mem_univ c)
  have hthr : (mkInstance P hP).singleton_party_size c * k ≥ (mkInstance P hP).voters.card := by
    rw [hsize]
    simp [mkInstance, allVoters, k]
  simpa [W] using
    (ABCRule.resolute_proportionality (f := f) (hres := hres) (hprop := hprop)
      (inst := mkInstance P hP) (c := c) (hpl := hpl) (hc_cand := hc) (h_size := hthr))

lemma exclusive_singleton_of_unique_supporter (inst : ABCInstance V C k) (c : C) (v₀ : V)
    (hv₀ : v₀ ∈ inst.voters)
    (h₀ : inst.approves v₀ = {c})
    (h_other : ∀ v : V, v ∈ inst.voters → v ≠ v₀ → c ∉ inst.approves v) :
    Peters.SingletonApprovers.is_exclusive_singleton inst c := by
  constructor
  · refine ⟨v₀, ?_⟩
    simp [ABCInstance.singleton_party, hv₀, h₀]
  · ext v
    simp only [ABCInstance.supporters, ABCInstance.singleton_party, mem_filter]
    constructor
    · rintro ⟨hv, hc⟩
      by_cases hvv₀ : v = v₀
      · subst hvv₀; exact ⟨hv, h₀⟩
      · have : c ∉ inst.approves v := h_other v hv hvv₀
        exact False.elim (this hc)
    · rintro ⟨hv, hv_eq⟩
      refine ⟨hv, ?_⟩
      simpa [hv_eq]

lemma singleton_approver_in_W (f : ABCRule V C k) (hwf : IsWellFormedOnPlentiful f) (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality) (hsp : Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f)
    (P : Profile) (hP : ∀ v : V, P v ⊂ allCandidates)
    (hpl : (mkInstance P hP).plentiful)
    (c : C)
    (hsize : (mkInstance P hP).singleton_party_size c = 1)
    (hexcl : Peters.SingletonApprovers.is_exclusive_singleton (mkInstance P hP) c) :
    c ∈ W f hres P hP := by
  have hc : c ∈ (mkInstance P hP).candidates := by
    simpa [mkInstance, allCandidates] using (Finset.mem_univ c)
  have hm : (mkInstance P hP).candidates.card = k + 1 := by
    simp [mkInstance, allCandidates, k]
  have hthr : (mkInstance P hP).singleton_party_size c * k ≥ (mkInstance P hP).voters.card := by
    rw [hsize]
    simp [mkInstance, allVoters, k]
  simpa [W] using
    (Peters.SingletonApprovers.singleton_approvers_elected
      (inst := mkInstance P hP) (c := c) (hc := hc) (hm := hm) (h_size := hthr) (hexcl := hexcl)
      (f := f) (hwf := hwf) (hres := hres) (hprop := hprop) (hsp := hsp) (hpl := hpl))

end Peters.BaseCaseCommon
