import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Card

import ABCVoting.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.Peters.InductionN

open Finset BigOperators ABCInstance
open Peters.InductionN

/-!
# Induction on the Number of Voters (Kluiving et al., Lemma for voters)

We work in the Kluiving setting with `m = k+1` candidates.
The rule for `k` voters is induced by repeating each voter `q` times.

The main new work is showing cautious strategyproofness is preserved.
-/

namespace KluivingDeVriesVrijbergenBoixelEndriss.InductionN

abbrev Cand (k : ℕ) := Fin (k + 1)

-- ============================================================================
-- Dominating candidate efficiency under voter expansion
-- ============================================================================

lemma dominates_expand_voters (k q : ℕ) (hq : 0 < q)
    (inst : ABCInstance (Fin k) (Cand k) k) (a b : Cand k) :
    (expand_voters k q hq inst).dominates a b ↔ inst.dominates a b := by
  classical
  have approves_expand_voters (t : Fin q) (v : Fin k) :
      (expand_voters k q hq inst).approves (finProdFinEquiv (t, v)) = inst.approves v := by
    have hvmod : (finProdFinEquiv (t, v)).modNat = v := by
      have hA :
          finProdFinEquiv.symm (finProdFinEquiv (t, v)) =
            ((finProdFinEquiv (t, v)).divNat, (finProdFinEquiv (t, v)).modNat) := by
        simpa using (finProdFinEquiv_symm_apply (x := finProdFinEquiv (t, v)))
      have hB : finProdFinEquiv.symm (finProdFinEquiv (t, v)) = (t, v) :=
        finProdFinEquiv.symm_apply_apply _
      have hC :
          (t, v) =
            ((finProdFinEquiv (t, v)).divNat, (finProdFinEquiv (t, v)).modNat) := by
        simpa [hB] using hA
      have : v = (finProdFinEquiv (t, v)).modNat := by
        simpa using congrArg Prod.snd hC
      simpa using this.symm
    simp [expand_voters, hvmod]
  constructor
  · intro hdom
    refine ⟨?_, ?_⟩
    · intro v hv hbv
      -- pick the 0-th copy of v
      let v' : Fin (q * k) := finProdFinEquiv (⟨0, hq⟩, v)
      have hv' : v' ∈ (expand_voters k q hq inst).voters := by
        refine Finset.mem_image.mpr ?_
        refine ⟨(⟨0, hq⟩, v), ?_, rfl⟩
        simp [Finset.mem_product, hv]
      have hbv' : b ∈ (expand_voters k q hq inst).approves v' := by
        simpa [approves_expand_voters, v'] using hbv
      have hav' : a ∈ (expand_voters k q hq inst).approves v' := hdom.1 v' hv' hbv'
      simpa [approves_expand_voters, v'] using hav'
    · rcases hdom.2 with ⟨v', hv', hav', hbv'⟩
      let v : Fin k := (finProdFinEquiv.symm v').2
      have hv : v ∈ inst.voters :=
        (mem_expand_voters_iff (k := k) (q := q) hq inst v').1 hv'
      have hav : a ∈ inst.approves v := by
        simpa [expand_voters] using hav'
      have hbv : b ∉ inst.approves v := by
        simpa [expand_voters] using hbv'
      exact ⟨v, hv, hav, hbv⟩
  · intro hdom
    refine ⟨?_, ?_⟩
    · intro v hv hbv
      have hv' : (finProdFinEquiv.symm v).2 ∈ inst.voters :=
        (mem_expand_voters_iff (k := k) (q := q) hq inst v).1 hv
      have hbv' : b ∈ inst.approves (finProdFinEquiv.symm v).2 := by
        simpa [expand_voters] using hbv
      have := hdom.1 _ hv' hbv'
      simpa [expand_voters] using this
    · rcases hdom.2 with ⟨v, hv, hav, hbv⟩
      let v' : Fin (q * k) := finProdFinEquiv (⟨0, hq⟩, v)
      have hv' : v' ∈ (expand_voters k q hq inst).voters := by
        refine Finset.mem_image.mpr ?_
        refine ⟨(⟨0, hq⟩, v), ?_, rfl⟩
        simp [Finset.mem_product, hv]
      have hav' : a ∈ (expand_voters k q hq inst).approves v' := by
        simpa [approves_expand_voters, v'] using hav
      have hbv' : b ∉ (expand_voters k q hq inst).approves v' := by
        simpa [approves_expand_voters, v'] using hbv
      exact ⟨v', hv', hav', hbv'⟩

-- ============================================================================
-- Induced rule preserves axioms
-- ============================================================================

lemma induced_rule_wellFormed (k q : ℕ) (hq : 0 < q)
    (f : ABCRule (Fin (q * k)) (Cand k) k) (hwf : f.IsWellFormed) :
    (induced_rule k q hq f).IsWellFormed := by
  classical
  intro inst
  simpa [induced_rule] using hwf (expand_voters k q hq inst)

lemma induced_rule_dominating_efficiency (k q : ℕ) (hq : 0 < q)
    (f : ABCRule (Fin (q * k)) (Cand k) k)
    (heff : f.SatisfiesDominatingCandidateEfficiency) :
    (induced_rule k q hq f).SatisfiesDominatingCandidateEfficiency := by
  classical
  intro inst a b ha hb hdom W hW hbW
  have ha' : a ∈ (expand_voters k q hq inst).candidates := by
    simpa [expand_voters] using ha
  have hb' : b ∈ (expand_voters k q hq inst).candidates := by
    simpa [expand_voters] using hb
  have hdom' : (expand_voters k q hq inst).dominates a b := by
    exact (dominates_expand_voters (k := k) (q := q) hq inst a b).2 hdom
  exact heff _ _ _ ha' hb' hdom' W (by simpa [induced_rule] using hW) hbW

lemma induced_rule_minimal_proportionality (k q : ℕ) (hq : 0 < q)
    (f : ABCRule (Fin (q * k)) (Cand k) k)
    (hprop : f.SatisfiesMinimalProportionality) :
    (induced_rule k q hq f).SatisfiesMinimalProportionality := by
  -- Minimal proportionality is the same as proportionality.
  simpa [ABCRule.SatisfiesMinimalProportionality] using
    (induced_rule_proportionality k q hq f (by
      simpa [ABCRule.SatisfiesMinimalProportionality] using hprop))

-- ============================================================================
-- Cautious preference classification for m = k + 1
-- ============================================================================

def has_good (A : Finset (Cand k)) (X : Finset (Finset (Cand k))) : Prop :=
  ∃ W ∈ X, A ⊆ W

def has_bad (A : Finset (Cand k)) (X : Finset (Finset (Cand k))) : Prop :=
  ∃ W ∈ X, ¬ A ⊆ W

noncomputable def outcome_class (A : Finset (Cand k)) (X : Finset (Finset (Cand k))) : Nat :=
  by
    classical
    exact if has_good A X then (if has_bad A X then 1 else 2) else 0

lemma outcome_class_eq_two (A : Finset (Cand k)) (X : Finset (Finset (Cand k)))
    (hgood : has_good A X) (hbad : ¬ has_bad A X) :
    outcome_class A X = 2 := by
  classical
  simp [outcome_class, hgood, hbad]

lemma outcome_class_eq_one (A : Finset (Cand k)) (X : Finset (Finset (Cand k)))
    (hgood : has_good A X) (hbad : has_bad A X) :
    outcome_class A X = 1 := by
  classical
  simp [outcome_class, hgood, hbad]

lemma outcome_class_eq_zero (A : Finset (Cand k)) (X : Finset (Finset (Cand k)))
    (hgood : ¬ has_good A X) :
    outcome_class A X = 0 := by
  classical
  simp [outcome_class, hgood]

lemma outcome_class_le_two (A : Finset (Cand k)) (X : Finset (Finset (Cand k))) :
    outcome_class A X ≤ 2 := by
  classical
  by_cases hgood : has_good A X
  · by_cases hbad : has_bad A X
    · simp [outcome_class, hgood, hbad]
    · simp [outcome_class, hgood, hbad]
  · simp [outcome_class, hgood]

lemma has_bad_of_not_has_good (A : Finset (Cand k))
    (X : Finset (Finset (Cand k))) (hXne : X.Nonempty)
    (hnot : ¬ has_good A X) : has_bad A X := by
  classical
  rcases hXne with ⟨W, hW⟩
  by_cases hgood : A ⊆ W
  · exact (hnot ⟨W, hW, hgood⟩).elim
  · exact ⟨W, hW, hgood⟩

lemma committee_eq_erase_of_card (W : Finset (Cand k)) (hW : W.card = k) :
    ∃ x, W = Finset.univ.erase x := by
  classical
  have h_compl : Wᶜ.card = 1 := by
    rw [Finset.card_compl, hW, Fintype.card_fin]
    simp
  rcases Finset.card_eq_one.mp h_compl with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [← Finset.compl_singleton, ← hx, compl_compl]

lemma card_inter_eq_of_subset (A W : Finset (Cand k)) (hsub : A ⊆ W) :
    (W ∩ A).card = A.card := by
  have h : W ∩ A = A := by
    exact Finset.inter_eq_right.mpr hsub
  simpa [h]

lemma card_inter_eq_of_not_subset (A W : Finset (Cand k)) (hW : W.card = k)
    (hnot : ¬ A ⊆ W) :
    (W ∩ A).card = A.card - 1 := by
  classical
  rcases committee_eq_erase_of_card (k := k) W hW with ⟨x, hWx⟩
  have hxA : x ∈ A := by
    by_contra hxA
    apply hnot
    intro y hy
    have hne : y ≠ x := by
      intro h
      subst h
      exact hxA hy
    have : y ∈ (Finset.univ.erase x) := by
      simp [hne]
    simpa [hWx] using this
  have hWInt : W ∩ A = A.erase x := by
    calc
      W ∩ A = (Finset.univ.erase x) ∩ A := by simpa [hWx]
      _ = (Finset.univ ∩ A).erase x := by
        simpa [Finset.erase_inter]
      _ = A.erase x := by simp
  simpa [hWInt] using Finset.card_erase_of_mem hxA

lemma committee_prefeq_iff_good_or_bad (A W W' : Finset (Cand k))
    (hW : W.card = k) (hW' : W'.card = k) :
    committee_prefeq A W W' ↔ (A ⊆ W) ∨ ¬ (A ⊆ W') := by
  classical
  constructor
  · intro hpref
    by_cases hgoodW : A ⊆ W
    · exact Or.inl hgoodW
    · -- W is bad: then W' must be bad as well
      by_cases hgoodW' : A ⊆ W'
      · have hWcard : (W ∩ A).card = A.card - 1 :=
          card_inter_eq_of_not_subset (A := A) (W := W) hW hgoodW
        have hW'card : (W' ∩ A).card = A.card :=
          card_inter_eq_of_subset (A := A) (W := W') (hsub := hgoodW')
        have hApos : 0 < A.card := by
          by_contra hApos
          have hAempty : A = ∅ := by
            exact Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hApos)
          apply hgoodW
          simpa [hAempty] using (Finset.empty_subset W)
        have hlt : A.card - 1 < A.card := by
          have hne : A.card ≠ 0 := by exact Nat.ne_of_gt hApos
          simpa [Nat.pred_eq_sub_one] using (Nat.pred_lt hne)
        have hge : (W ∩ A).card ≥ (W' ∩ A).card := hpref
        rw [hWcard, hW'card] at hge
        have hcontr : False := (not_le_of_gt hlt) hge
        exact hcontr.elim
      · exact Or.inr hgoodW'
  · intro hgood_or_bad
    rcases hgood_or_bad with hgoodW | hbadW'
    · -- good W implies weak preference
      have hWcard : (W ∩ A).card = A.card :=
        card_inter_eq_of_subset (A := A) (W := W) (hsub := hgoodW)
      have hW'card : (W' ∩ A).card ≤ A.card := by
        refine Finset.card_le_card ?_
        intro x hx
        exact (Finset.mem_inter.mp hx).2
      -- A.card ≥ (W' ∩ A).card
      have : A.card ≥ (W' ∩ A).card := hW'card
      simpa [committee_prefeq, hWcard] using this
    · -- both bad committees give equal score
      by_cases hgoodW : A ⊆ W
      · -- good W implies weak preference even if W' is bad
        have hWcard : (W ∩ A).card = A.card :=
          card_inter_eq_of_subset (A := A) (W := W) (hsub := hgoodW)
        have hW'card : (W' ∩ A).card ≤ A.card := by
          refine Finset.card_le_card ?_
          intro x hx
          exact (Finset.mem_inter.mp hx).2
        have : A.card ≥ (W' ∩ A).card := hW'card
        simpa [committee_prefeq, hWcard] using this
      · -- both bad committees give equal score
        have hWcard : (W ∩ A).card = A.card - 1 :=
          card_inter_eq_of_not_subset (A := A) (W := W) hW hgoodW
        have hW'card : (W' ∩ A).card = A.card - 1 :=
          card_inter_eq_of_not_subset (A := A) (W := W') hW' hbadW'
        simp [committee_prefeq, hWcard, hW'card]

lemma cautious_prefeq_iff_not_bad_good (A : Finset (Cand k))
    (X X' : Finset (Finset (Cand k)))
    (hX : ∀ W ∈ X, W.card = k) (hX' : ∀ W ∈ X', W.card = k) :
    cautious_prefeq A X X' ↔ ¬ (has_bad A X ∧ has_good A X') := by
  classical
  constructor
  · intro hpref hbad_good
    rcases hbad_good with ⟨⟨W, hW, hbadW⟩, ⟨W', hW', hgoodW'⟩⟩
    have hWcard := hX W hW
    have hW'card := hX' W' hW'
    have hpref' : committee_prefeq A W W' := hpref W hW W' hW'
    have h := (committee_prefeq_iff_good_or_bad (A := A) (W := W) (W' := W') hWcard hW'card).1 hpref'
    cases h with
    | inl hgood => exact hbadW hgood
    | inr hbad => exact hbad hgoodW'
  · intro hno W hW W' hW'
    have hWcard := hX W hW
    have hW'card := hX' W' hW'
    by_cases hgoodW : A ⊆ W
    · exact (committee_prefeq_iff_good_or_bad (A := A) (W := W) (W' := W') hWcard hW'card).2
        (Or.inl hgoodW)
    · have hbadX : has_bad A X := ⟨W, hW, hgoodW⟩
      have hnot_goodX' : ¬ has_good A X' := by
        intro hgoodX'
        exact hno ⟨hbadX, hgoodX'⟩
      have hbadW' : ¬ A ⊆ W' := by
        intro hgoodW'
        exact hnot_goodX' ⟨W', hW', hgoodW'⟩
      exact (committee_prefeq_iff_good_or_bad (A := A) (W := W) (W' := W') hWcard hW'card).2
        (Or.inr hbadW')

lemma cautious_pref_iff_has_good_bad (A : Finset (Cand k))
    (X X' : Finset (Finset (Cand k)))
    (hX : ∀ W ∈ X, W.card = k) (hX' : ∀ W ∈ X', W.card = k) :
    cautious_pref A X X' ↔
      has_good A X ∧ has_bad A X' ∧ ¬ (has_bad A X ∧ has_good A X') := by
  classical
  constructor
  · intro hpref
    have hpreq : cautious_prefeq A X X' := hpref.1
    have hnotpref' : ¬ cautious_prefeq A X' X := hpref.2
    have hbadgood : has_bad A X' ∧ has_good A X := by
      by_cases h' : has_bad A X' ∧ has_good A X
      · exact h'
      · have hpreq' : cautious_prefeq A X' X :=
          (cautious_prefeq_iff_not_bad_good (A := A) (X := X') (X' := X) hX' hX).2 h'
        exact (hnotpref' hpreq').elim
    have hnot_bad_good : ¬ (has_bad A X ∧ has_good A X') :=
      (cautious_prefeq_iff_not_bad_good (A := A) (X := X) (X' := X') hX hX').1 hpreq
    exact ⟨hbadgood.2, hbadgood.1, hnot_bad_good⟩
  · intro h
    have hpreq : cautious_prefeq A X X' :=
      (cautious_prefeq_iff_not_bad_good (A := A) (X := X) (X' := X') hX hX').2 h.2.2
    have hnotpref' : ¬ cautious_prefeq A X' X := by
      intro hpreq'
      have hno := (cautious_prefeq_iff_not_bad_good (A := A) (X := X') (X' := X) hX' hX).1 hpreq'
      exact hno ⟨h.2.1, h.1⟩
    exact ⟨hpreq, hnotpref'⟩

lemma cautious_pref_iff_class_gt (A : Finset (Cand k))
    (X X' : Finset (Finset (Cand k)))
    (hX : ∀ W ∈ X, W.card = k) (hX' : ∀ W ∈ X', W.card = k)
    (hX'ne : X'.Nonempty) :
    cautious_pref A X X' ↔ outcome_class A X > outcome_class A X' := by
  classical
  constructor
  · intro hpref
    have h :=
      (cautious_pref_iff_has_good_bad (A := A) (X := X) (X' := X') hX hX').1 hpref
    rcases h with ⟨hgoodX, hbadX', hnot_bad_good⟩
    by_cases hbadX : has_bad A X
    · have hnot_goodX' : ¬ has_good A X' := by
        intro hgoodX'
        exact hnot_bad_good ⟨hbadX, hgoodX'⟩
      have hclassX : outcome_class A X = 1 :=
        outcome_class_eq_one (A := A) (X := X) hgoodX hbadX
      have hclassX' : outcome_class A X' = 0 :=
        outcome_class_eq_zero (A := A) (X := X') hnot_goodX'
      simp [hclassX, hclassX']
    · have hclassX : outcome_class A X = 2 := by
        exact outcome_class_eq_two (A := A) (X := X) hgoodX hbadX
      by_cases hgoodX' : has_good A X'
      · have hclassX' : outcome_class A X' = 1 := by
          exact outcome_class_eq_one (A := A) (X := X') hgoodX' hbadX'
        simp [hclassX, hclassX']
      · have hbadX'' : has_bad A X' := has_bad_of_not_has_good (A := A) (X := X') hX'ne hgoodX'
        have hclassX' : outcome_class A X' = 0 := by
          exact outcome_class_eq_zero (A := A) (X := X') hgoodX'
        simp [hclassX, hclassX']
  · intro hgt
    -- show has_good X, has_bad X', and not (has_bad X ∧ has_good X')
    have hgoodX : has_good A X := by
      by_cases hgoodX : has_good A X
      · exact hgoodX
      · have hclassX : outcome_class A X = 0 :=
          outcome_class_eq_zero (A := A) (X := X) hgoodX
        -- then class cannot be greater
        have : outcome_class A X' < 0 := by
          simpa [hclassX] using hgt
        exact (Nat.not_lt_zero _ this).elim
    have hbadX' : has_bad A X' := by
      by_cases hgoodX' : has_good A X'
      · by_cases hbadX' : has_bad A X'
        · exact hbadX'
        · have hclassX' : outcome_class A X' = 2 := by
            exact outcome_class_eq_two (A := A) (X := X') hgoodX' hbadX'
          have hgt' : outcome_class A X > 2 := by
            simpa [hclassX'] using hgt
          exact (not_lt_of_ge (outcome_class_le_two (A := A) (X := X)) hgt').elim
      · exact has_bad_of_not_has_good (A := A) (X := X') hX'ne hgoodX'
    have hnot_bad_good : ¬ (has_bad A X ∧ has_good A X') := by
      by_cases hbadX : has_bad A X
      · -- then X has class 1, so X' must have class 0
        by_cases hgoodX' : has_good A X'
        · have hclassX : outcome_class A X = 1 := by
            exact outcome_class_eq_one (A := A) (X := X) hgoodX hbadX
          have hclassX' : outcome_class A X' = 1 := by
            exact outcome_class_eq_one (A := A) (X := X') hgoodX' hbadX'
          have : (1 : ℕ) > 1 := by simpa [hclassX, hclassX'] using hgt
          exact (lt_irrefl _ this).elim
        · exact by
            intro h
            exact hgoodX' h.2
      · exact by
          intro h
          exact hbadX h.1
    exact (cautious_pref_iff_has_good_bad (A := A) (X := X) (X' := X') hX hX').2
      ⟨hgoodX, hbadX', hnot_bad_good⟩

-- ============================================================================
-- MAIN LEMMA (VOTERS)
-- ============================================================================

theorem induction_n (k q : ℕ)
    (_hk : 3 ≤ k)
    (hq : 1 ≤ q)
    (f : ABCRule (Fin (q * k)) (Cand k) k)
    (hwf : f.IsWellFormed)
    (heff : f.SatisfiesDominatingCandidateEfficiency)
    (hprop : f.SatisfiesMinimalProportionality)
    (hsp : f.SatisfiesCautiousStrategyproofness) :
    ∃ (f' : ABCRule (Fin k) (Cand k) k),
      f'.IsWellFormed ∧
      f'.SatisfiesDominatingCandidateEfficiency ∧
      f'.SatisfiesMinimalProportionality ∧
      f'.SatisfiesCautiousStrategyproofness := by
  have hq_pos : 0 < q := by linarith
  let f' := induced_rule k q hq_pos f
  refine ⟨f', ?_, ?_, ?_, ?_⟩
  · exact induced_rule_wellFormed k q hq_pos f hwf
  · exact induced_rule_dominating_efficiency k q hq_pos f heff
  · exact induced_rule_minimal_proportionality k q hq_pos f hprop
  · -- cautious strategyproofness
    intro inst inst' i hi hvar
    let A := inst.approves i
    let chain (t : ℕ) := chain_instance k q hq_pos inst inst' i hvar t
    have hcard_chain : ∀ t, ∀ W ∈ f (chain t), W.card = k := by
      intro t W hW
      exact (hwf (chain t)).2 _ hW |>.1
    have hne_chain : ∀ t, (f (chain t)).Nonempty := by
      intro t
      exact (hwf (chain t)).1
    have h_step : ∀ t, t < q →
        ¬ cautious_pref A (f (chain (t + 1))) (f (chain t)) := by
      intro t ht
      let v_t : Fin (q * k) := finProdFinEquiv (⟨t, ht⟩, i)
      have hv_t_mem : v_t ∈ (chain t).voters :=
        chain_instance_voter_mem k q hq_pos inst inst' i hi hvar t ht
      have hvar_step : (chain t).is_i_variant (chain (t + 1)) v_t :=
        chain_instance_step_variant k q hq_pos inst inst' i hi hvar t ht
      have hsp_step : ¬ cautious_pref ((chain t).approves v_t)
          (f (chain (t + 1))) (f (chain t)) :=
        hsp (chain t) (chain (t + 1)) v_t hv_t_mem hvar_step
      have hA_old : (chain t).approves v_t = inst.approves i := by
        simpa [chain, v_t] using
          (chain_instance_step_approval k q hq_pos inst inst' i hvar t ht).1
      simpa [A, hA_old] using hsp_step
    have hclass_step : ∀ t, t < q →
        outcome_class A (f (chain (t + 1))) ≤ outcome_class A (f (chain t)) := by
      intro t ht
      have h_notpref := h_step t ht
      have hX : ∀ W ∈ f (chain (t + 1)), W.card = k := hcard_chain (t + 1)
      have hX' : ∀ W ∈ f (chain t), W.card = k := hcard_chain t
      have hneX : (f (chain (t + 1))).Nonempty := hne_chain (t + 1)
      have hneX' : (f (chain t)).Nonempty := hne_chain t
      by_contra hlt
      have hgt : outcome_class A (f (chain (t + 1))) >
          outcome_class A (f (chain t)) := lt_of_not_ge hlt
      have hpref : cautious_pref A (f (chain (t + 1))) (f (chain t)) :=
        (cautious_pref_iff_class_gt (A := A) (X := f (chain (t + 1))) (X' := f (chain t))
          hX hX' hneX').2 hgt
      exact h_notpref hpref
    -- chain monotonicity
    have hclass_q0 : outcome_class A (f (chain q)) ≤ outcome_class A (f (chain 0)) := by
      have aux : ∀ n, n ≤ q → outcome_class A (f (chain n)) ≤
          outcome_class A (f (chain 0)) := by
        intro n hn
        induction n with
        | zero => exact le_refl _
        | succ m ih =>
          have hm : m < q := Nat.lt_of_succ_le hn
          exact le_trans (hclass_step m hm) (ih (le_of_lt hm))
      exact aux q (le_refl q)
    -- relate chain endpoints to f' values
    have hchain0 : f (chain 0) = f' inst := by
      rw [chain_instance_zero_output k q hq_pos inst inst' i hvar f]
      rfl
    have hchainq : f (chain q) = f' inst' := by
      rw [chain_instance_ge_q_output k q hq_pos inst inst' i hvar q (le_refl q) f]
      rfl
    -- conclude no cautious improvement
    have hX : ∀ W ∈ f' inst', W.card = k := by
      intro W hW
      have : W ∈ f (chain q) := by simpa [hchainq] using hW
      exact (hcard_chain q) W this
    have hX' : ∀ W ∈ f' inst, W.card = k := by
      intro W hW
      have : W ∈ f (chain 0) := by simpa [hchain0] using hW
      exact (hcard_chain 0) W this
    have hneX : (f' inst').Nonempty := by
      have : (f (chain q)).Nonempty := hne_chain q
      simpa [hchainq] using this
    have hneX' : (f' inst).Nonempty := by
      have : (f (chain 0)).Nonempty := hne_chain 0
      simpa [hchain0] using this
    -- if there were a strict cautious improvement, class would strictly increase
    by_contra hpref
    have hgt : outcome_class A (f' inst') > outcome_class A (f' inst) :=
      (cautious_pref_iff_class_gt (A := A) (X := f' inst') (X' := f' inst)
        hX hX' hneX').1 hpref
    have hle : outcome_class A (f' inst') ≤ outcome_class A (f' inst) := by
      simpa [hchainq, hchain0] using hclass_q0
    exact (lt_irrefl _ (lt_of_le_of_lt hle hgt)).elim

end KluivingDeVriesVrijbergenBoixelEndriss.InductionN
