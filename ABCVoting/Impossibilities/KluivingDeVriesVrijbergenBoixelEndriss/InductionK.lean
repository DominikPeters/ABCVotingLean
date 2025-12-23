import Mathlib.Data.Finset.Card

import ABCVoting.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.Peters.InductionK
import ABCVoting.Impossibilities.KluivingDeVriesVrijbergenBoixelEndriss.SingletonApprovers

open Finset BigOperators ABCInstance
open Peters.InductionK
open KluivingDeVriesVrijbergenBoixelEndriss.SingletonApprovers

namespace KluivingDeVriesVrijbergenBoixelEndriss.InductionK

-- ============================================================================
-- DUMMY CANDIDATE IS ALWAYS ELECTED
-- ============================================================================

lemma dummy_exclusive_singleton (k : ℕ) (inst : ABCInstance (Fin k) (Fin (k + 1)) k) :
    is_exclusive_singleton (extend_instance k inst) (dummy_candidate k) := by
  refine ⟨?_, ?_⟩
  · -- singleton party nonempty
    rw [dummy_singleton_party (k := k) inst]
    exact Finset.singleton_nonempty _
  · -- supporters = singleton_party
    rw [dummy_supporters (k := k) inst, dummy_singleton_party (k := k) inst]

lemma dummy_in_committee (k : ℕ)
    (inst : ABCInstance (Fin k) (Fin (k + 1)) k)
    (f : ABCRule (Fin (k + 1)) (Fin (k + 2)) (k + 1))
    (hwf : f.IsWellFormed)
    (hprop : f.SatisfiesMinimalProportionality)
    (hsp : f.SatisfiesCautiousStrategyproofness) :
    ∀ W ∈ f (extend_instance k inst), dummy_candidate k ∈ W := by
  classical
  have hcand : dummy_candidate k ∈ (extend_instance k inst).candidates := by
    simp [extend_instance]
  have hsing : (extend_instance k inst).singleton_party_size (dummy_candidate k) = 1 := by
    have hsize := ABCInstance.singleton_party_size_eq_card
      (inst := extend_instance k inst) (c := dummy_candidate k)
    have hparty := dummy_singleton_party (k := k) inst
    calc
      (extend_instance k inst).singleton_party_size (dummy_candidate k)
          = ((extend_instance k inst).singleton_party (dummy_candidate k)).card := hsize
      _ = ({dummy_voter k} : Finset (Fin (k + 1))).card := by simpa [hparty]
      _ = 1 := by simp
  have hvoters_le : (extend_instance k inst).voters.card ≤ k + 1 := by
    simpa using (Finset.card_le_univ (s := (extend_instance k inst).voters))
  have h_size :
      (extend_instance k inst).singleton_party_size (dummy_candidate k) * (k + 1) ≥
        (extend_instance k inst).voters.card := by
    simpa [hsing, Nat.one_mul] using hvoters_le
  have hexcl : is_exclusive_singleton (extend_instance k inst) (dummy_candidate k) :=
    dummy_exclusive_singleton (k := k) inst
  exact singleton_approvers_elected
    (inst := extend_instance k inst) (c := dummy_candidate k)
    hcand h_size hexcl f hwf hprop hsp

-- ============================================================================
-- VARIANT LIFTING TO EXTENDED INSTANCES
-- ============================================================================

lemma extend_instance_is_variant (k : ℕ)
    (inst inst' : ABCInstance (Fin k) (Fin (k + 1)) k) (i : Fin k)
    (hvar : inst.is_i_variant inst' i) :
    (extend_instance k inst).is_i_variant (extend_instance k inst') (embed_voter k i) := by
  rcases hvar with ⟨hv, hc, ha⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [extend_instance, hv]
  · simp [extend_instance, hc]
  · intro v hvv hne
    rcases Finset.mem_union.1 hvv with hvv | hvv
    · rcases Finset.mem_map.1 hvv with ⟨v0, hv0, rfl⟩
      have hne0 : v0 ≠ i := by
        intro hEq
        apply hne
        subst hEq
        rfl
      have ha0 : inst.approves v0 = inst'.approves v0 := ha v0 hv0 hne0
      have hlt : (embed_voter k v0).val < k := by
        simpa [embed_voter] using v0.isLt
      have hvEq : (⟨(embed_voter k v0).val, hlt⟩ : Fin k) = v0 := by
        apply Fin.ext
        simp [embed_voter]
      simp [extend_instance, hlt, ha0, hvEq]
    · have hvd : v = dummy_voter k := by simpa using hvv
      subst hvd
      simp [extend_instance, dummy_voter]

-- ============================================================================
-- PREFERENCE TRANSLATION THROUGH PROJECT COMMITTEE
-- ============================================================================

lemma map_project_inter_eq (k : ℕ) (A : Finset (Fin (k + 1)))
    (W : Finset (Fin (k + 2))) :
    (project_committee k W ∩ A).map
        ⟨embed_candidate k, embed_candidate_injective k⟩ =
      W ∩ A.map ⟨embed_candidate k, embed_candidate_injective k⟩ := by
  classical
  let emb : Fin (k + 1) ↪ Fin (k + 2) := ⟨embed_candidate k, embed_candidate_injective k⟩
  ext x
  constructor
  · intro hx
    rcases Finset.mem_map.1 hx with ⟨c, hc, hxc⟩
    have hcA : c ∈ A := (Finset.mem_inter.mp hc).2
    have hcW : c ∈ project_committee k W := (Finset.mem_inter.mp hc).1
    have hxW : emb c ∈ W :=
      (mem_project_committee_iff (k := k) (W := W) (c := c)).1 hcW
    have hxA : emb c ∈ A.map emb := Finset.mem_map.2 ⟨c, hcA, rfl⟩
    have hxW' : x ∈ W := by simpa [emb, hxc] using hxW
    have hxA' : x ∈ A.map emb := by simpa [emb, hxc] using hxA
    exact Finset.mem_inter.mpr ⟨hxW', hxA'⟩
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxW, hxA⟩
    rcases Finset.mem_map.1 hxA with ⟨c, hcA, hxc⟩
    have hcW : c ∈ project_committee k W := by
      apply (mem_project_committee_iff (k := k) (W := W) (c := c)).2
      simpa [emb, hxc.symm] using hxW
    have hc : c ∈ project_committee k W ∩ A := by
      exact Finset.mem_inter.mpr ⟨hcW, hcA⟩
    exact Finset.mem_map.2 ⟨c, hc, hxc⟩

lemma card_project_inter_eq (k : ℕ) (A : Finset (Fin (k + 1)))
    (W : Finset (Fin (k + 2))) :
    (project_committee k W ∩ A).card =
      (W ∩ A.map ⟨embed_candidate k, embed_candidate_injective k⟩).card := by
  classical
  let emb : Fin (k + 1) ↪ Fin (k + 2) := ⟨embed_candidate k, embed_candidate_injective k⟩
  have hmap := Finset.card_map (s := project_committee k W ∩ A) emb
  have hmap' :
      (project_committee k W ∩ A).map emb = W ∩ A.map emb :=
    map_project_inter_eq (k := k) (A := A) (W := W)
  simpa [hmap'] using hmap.symm

lemma committee_prefeq_project_iff (k : ℕ) (A : Finset (Fin (k + 1)))
    (W W' : Finset (Fin (k + 2))) :
    committee_prefeq A (project_committee k W) (project_committee k W') ↔
      committee_prefeq (A.map ⟨embed_candidate k, embed_candidate_injective k⟩) W W' := by
  classical
  simp [committee_prefeq, card_project_inter_eq]

lemma cautious_prefeq_project_iff (k : ℕ) (A : Finset (Fin (k + 1)))
    (X X' : Finset (Finset (Fin (k + 2)))) :
    cautious_prefeq A (X.image (project_committee k)) (X'.image (project_committee k)) ↔
      cautious_prefeq (A.map ⟨embed_candidate k, embed_candidate_injective k⟩) X X' := by
  classical
  constructor
  · intro h W hW W' hW'
    have hWimg : project_committee k W ∈ X.image (project_committee k) :=
      Finset.mem_image.mpr ⟨W, hW, rfl⟩
    have hW'img : project_committee k W' ∈ X'.image (project_committee k) :=
      Finset.mem_image.mpr ⟨W', hW', rfl⟩
    have hpref := h _ hWimg _ hW'img
    exact (committee_prefeq_project_iff (k := k) (A := A) (W := W) (W' := W')).1 hpref
  · intro h W hW W' hW'
    rcases Finset.mem_image.mp hW with ⟨X0, hX0, rfl⟩
    rcases Finset.mem_image.mp hW' with ⟨X1, hX1, rfl⟩
    have hpref := h X0 hX0 X1 hX1
    exact (committee_prefeq_project_iff (k := k) (A := A) (W := X0) (W' := X1)).2 hpref

-- ============================================================================
-- DOMINANCE LIFTING
-- ============================================================================

lemma dominates_extend_instance (k : ℕ) (inst : ABCInstance (Fin k) (Fin (k + 1)) k)
    (a b : Fin (k + 1)) (hdom : inst.dominates a b) :
    (extend_instance k inst).dominates (embed_candidate k a) (embed_candidate k b) := by
  classical
  refine ⟨?_, ?_⟩
  · intro v hv hbv
    rcases Finset.mem_union.1 hv with hv | hv
    · rcases Finset.mem_map.1 hv with ⟨v0, hv0, rfl⟩
      have hlt : (embed_voter k v0).val < k := by
        simpa [embed_voter] using v0.isLt
      have hvEq : (⟨(embed_voter k v0).val, hlt⟩ : Fin k) = v0 := by
        apply Fin.ext
        simp [embed_voter]
      have hbv' : b ∈ inst.approves v0 := by
        have hbv' :
            embed_candidate k b ∈ (inst.approves v0).map
              ⟨embed_candidate k, embed_candidate_injective k⟩ := by
          simpa [extend_instance, hlt, hvEq] using hbv
        rcases Finset.mem_map.1 hbv' with ⟨b0, hb0, hbEq⟩
        have hb0' : b0 = b := by
          apply embed_candidate_injective k
          simpa using hbEq
        simpa [hb0'] using hb0
      have hav' : a ∈ inst.approves v0 := hdom.1 v0 hv0 hbv'
      have hav'' : embed_candidate k a ∈ (inst.approves v0).map
          ⟨embed_candidate k, embed_candidate_injective k⟩ :=
        Finset.mem_map.2 ⟨a, hav', rfl⟩
      simpa [extend_instance, hlt, hvEq] using hav''
    · have hvd : v = dummy_voter k := by simpa using hv
      subst hvd
      have hlt : ¬(dummy_voter k).val < k := by simp [dummy_voter]
      have hbv' : embed_candidate k b ∈ ({dummy_candidate k} : Finset (Fin (k + 2))) := by
        simpa [extend_instance, hlt, dummy_voter] using hbv
      have hbEq : embed_candidate k b = dummy_candidate k := by
        simpa using (Finset.mem_singleton.1 hbv')
      exact (dummy_not_embedded k b hbEq).elim
  · rcases hdom.2 with ⟨v, hv, hav, hbv⟩
    let v' : Fin (k + 1) := embed_voter k v
    have hv' : v' ∈ (extend_instance k inst).voters :=
      Finset.mem_union_left _ (Finset.mem_map.2 ⟨v, hv, rfl⟩)
    have hlt : v'.val < k := by simpa [v', embed_voter] using v.isLt
    have hvEq : (⟨v'.val, hlt⟩ : Fin k) = v := by
      apply Fin.ext
      simp [v', embed_voter]
    have hav' : embed_candidate k a ∈ (extend_instance k inst).approves v' := by
      have hmem : embed_candidate k a ∈ (inst.approves v).map
          ⟨embed_candidate k, embed_candidate_injective k⟩ :=
        Finset.mem_map.2 ⟨a, hav, rfl⟩
      simpa [extend_instance, hlt, hvEq] using hmem
    have hbv' : embed_candidate k b ∉ (extend_instance k inst).approves v' := by
      intro hbv'
      have hbv'' :
          embed_candidate k b ∈ (inst.approves v).map
            ⟨embed_candidate k, embed_candidate_injective k⟩ := by
        simpa [extend_instance, hlt, hvEq] using hbv'
      rcases Finset.mem_map.1 hbv'' with ⟨b0, hb0, hbEq⟩
      have hb0' : b0 = b := by
        apply embed_candidate_injective k
        simpa using hbEq
      exact hbv (by simpa [hb0'] using hb0)
    exact ⟨v', hv', hav', hbv'⟩

-- ============================================================================
-- INDUCED RULE
-- ============================================================================

noncomputable def induced_rule (k : ℕ)
    (f : ABCRule (Fin (k + 1)) (Fin (k + 2)) (k + 1)) :
    ABCRule (Fin k) (Fin (k + 1)) k where
  apply inst :=
    (f (extend_instance k inst)).image (project_committee k)
  extensional := by
    intro inst inst' hv hc ha
    classical
    have h_ext : f (extend_instance k inst) = f (extend_instance k inst') := by
      apply f.extensional
      · simp [extend_instance, hv]
      · simp [extend_instance, hc]
      · intro v hvv
        rcases Finset.mem_union.1 hvv with hvv | hvv
        · rcases Finset.mem_map.1 hvv with ⟨v0, hv0, rfl⟩
          have hlt : (embed_voter k v0).val < k := by
            simpa [embed_voter] using v0.isLt
          have hvEq : (⟨(embed_voter k v0).val, hlt⟩ : Fin k) = v0 := by
            apply Fin.ext
            simp [embed_voter]
          have ha0 : inst.approves v0 = inst'.approves v0 := ha v0 hv0
          simp [extend_instance, hlt, ha0, hvEq]
        · have hvd : v = dummy_voter k := by simpa using hvv
          subst hvd
          simp [extend_instance, dummy_voter]
    simp [h_ext]

lemma induced_rule_wellFormed (k : ℕ)
    (f : ABCRule (Fin (k + 1)) (Fin (k + 2)) (k + 1))
    (hwf : f.IsWellFormed)
    (hprop : f.SatisfiesMinimalProportionality)
    (hsp : f.SatisfiesCautiousStrategyproofness) :
    (induced_rule k f).IsWellFormed := by
  classical
  intro inst
  have hnonempty : (f (extend_instance k inst)).Nonempty := (hwf _).1
  obtain ⟨W0, hW0⟩ := hnonempty
  have hnonempty' :
      ((f (extend_instance k inst)).image (project_committee k)).Nonempty :=
    ⟨project_committee k W0, Finset.mem_image.mpr ⟨W0, hW0, rfl⟩⟩
  refine ⟨?_, ?_⟩
  · simpa [induced_rule] using hnonempty'
  · intro W hW
    simp [induced_rule] at hW
    rcases hW with ⟨W0, hW0, rfl⟩
    have hW0_card : W0.card = k + 1 := (hwf _).2 _ hW0 |>.1
    have hW0_sub : W0 ⊆ (extend_instance k inst).candidates :=
      (hwf _).2 _ hW0 |>.2
    have hdummy : dummy_candidate k ∈ W0 :=
      dummy_in_committee (k := k) (inst := inst) (f := f) hwf hprop hsp W0 hW0
    have hcard_erase : (W0.erase (dummy_candidate k)).card = k := by
      have := Finset.card_erase_add_one hdummy
      linarith [hW0_card]
    have hmap_eq :
        (project_committee k W0).map ⟨embed_candidate k, embed_candidate_injective k⟩ =
          W0.erase (dummy_candidate k) :=
      map_project_committee_eq_erase_dummy (k := k) (W := W0)
    have hcard_W : (project_committee k W0).card = k := by
      have hmap_card :
          ((project_committee k W0).map
            ⟨embed_candidate k, embed_candidate_injective k⟩).card =
            (project_committee k W0).card := by
        simpa using (Finset.card_map
          (s := project_committee k W0) ⟨embed_candidate k, embed_candidate_injective k⟩)
      have hmap_card' :
          ((project_committee k W0).map
            ⟨embed_candidate k, embed_candidate_injective k⟩).card = k := by
        simpa [hmap_eq] using hcard_erase
      linarith
    have hsub_W : project_committee k W0 ⊆ inst.candidates := by
      intro c hc
      have hc_map : embed_candidate k c ∈ W0 :=
        (mem_project_committee_iff (k := k) (W := W0) (c := c)).1 hc
      have hc_in : embed_candidate k c ∈ (extend_instance k inst).candidates := hW0_sub hc_map
      rcases Finset.mem_union.1 hc_in with hmap | hdummy'
      · rcases Finset.mem_map.1 hmap with ⟨c0, hc0, hEq⟩
        have hEq' : c0 = c := embed_candidate_injective k (by simpa using hEq)
        subst hEq'
        exact hc0
      · cases (dummy_not_embedded k c) (by simpa using hdummy')
    exact ⟨hcard_W, hsub_W⟩

-- ============================================================================
-- MAIN INDUCTION LEMMA
-- ============================================================================

theorem induction_k (k : ℕ) (_hk : 3 ≤ k)
    (f : ABCRule (Fin (k + 1)) (Fin (k + 2)) (k + 1))
    (hwf : f.IsWellFormed)
    (heff : f.SatisfiesDominatingCandidateEfficiency)
    (hprop : f.SatisfiesMinimalProportionality)
    (hsp : f.SatisfiesCautiousStrategyproofness) :
    ∃ (f' : ABCRule (Fin k) (Fin (k + 1)) k),
      f'.IsWellFormed ∧
      f'.SatisfiesDominatingCandidateEfficiency ∧
      f'.SatisfiesMinimalProportionality ∧
      f'.SatisfiesCautiousStrategyproofness := by
  classical
  let f' : ABCRule (Fin k) (Fin (k + 1)) k := induced_rule k f
  refine ⟨f', ?_, ?_, ?_, ?_⟩
  · exact induced_rule_wellFormed (k := k) (f := f) hwf hprop hsp
  · -- dominating candidate efficiency
    intro inst a b ha hb hdom W hW hbW
    have hW_mem :
        W ∈ (f (extend_instance k inst)).image (project_committee k) := by
      simpa [f', induced_rule] using hW
    rcases Finset.mem_image.mp hW_mem with ⟨W0, hW0, rfl⟩
    have hbW0 : embed_candidate k b ∈ W0 :=
      (mem_project_committee_iff (k := k) (W := W0) (c := b)).1 hbW
    have ha_ext : embed_candidate k a ∈ (extend_instance k inst).candidates := by
      have : embed_candidate k a ∈ inst.candidates.map
          ⟨embed_candidate k, embed_candidate_injective k⟩ :=
        Finset.mem_map.2 ⟨a, ha, rfl⟩
      exact Finset.mem_union_left _ this
    have hb_ext : embed_candidate k b ∈ (extend_instance k inst).candidates := by
      have : embed_candidate k b ∈ inst.candidates.map
          ⟨embed_candidate k, embed_candidate_injective k⟩ :=
        Finset.mem_map.2 ⟨b, hb, rfl⟩
      exact Finset.mem_union_left _ this
    have hdom_ext :
        (extend_instance k inst).dominates (embed_candidate k a) (embed_candidate k b) :=
      dominates_extend_instance (k := k) (inst := inst) (a := a) (b := b) hdom
    have haW0 : embed_candidate k a ∈ W0 :=
      heff _ _ _ ha_ext hb_ext hdom_ext W0 hW0 hbW0
    exact (mem_project_committee_iff (k := k) (W := W0) (c := a)).2 haW0
  · -- minimal proportionality
    intro inst cand hpl hcand hquota W hW
    have hW_mem :
        W ∈ (f (extend_instance k inst)).image (project_committee k) := by
      simpa [f', induced_rule] using hW
    rcases Finset.mem_image.mp hW_mem with ⟨W0, hW0, rfl⟩
    -- extend party-list profile
    have hpl_ext : (extend_instance k inst).is_party_list := by
      classical
      let embC : Fin (k + 1) ↪ Fin (k + 2) := ⟨embed_candidate k, embed_candidate_injective k⟩
      intro v₁ hv₁ v₂ hv₂
      rcases Finset.mem_union.1 hv₁ with hv₁ | hv₁ <;>
      rcases Finset.mem_union.1 hv₂ with hv₂ | hv₂
      · rcases Finset.mem_map.1 hv₁ with ⟨a1, ha1, rfl⟩
        rcases Finset.mem_map.1 hv₂ with ⟨a2, ha2, rfl⟩
        have hlt1 : (embed_voter k a1).val < k := by simpa [embed_voter] using a1.isLt
        have hlt2 : (embed_voter k a2).val < k := by simpa [embed_voter] using a2.isLt
        have hvEq1 : (⟨(embed_voter k a1).val, hlt1⟩ : Fin k) = a1 := by
          apply Fin.ext
          simp [embed_voter]
        have hvEq2 : (⟨(embed_voter k a2).val, hlt2⟩ : Fin k) = a2 := by
          apply Fin.ext
          simp [embed_voter]
        have happ1 :
            (extend_instance k inst).approves (embed_voter k a1) =
              (inst.approves a1).map embC := by
          simpa [extend_instance, hlt1, hvEq1, embC]
        have happ2 :
            (extend_instance k inst).approves (embed_voter k a2) =
              (inst.approves a2).map embC := by
          simpa [extend_instance, hlt2, hvEq2, embC]
        rcases hpl a1 ha1 a2 ha2 with ha | ha
        · left
          simpa [happ1, happ2, ha]
        · right
          have : Disjoint ((inst.approves a1).map embC) ((inst.approves a2).map embC) :=
            (Finset.disjoint_map (s := inst.approves a1) (t := inst.approves a2) embC).2 ha
          simpa [happ1, happ2] using this
      · -- v₁ embedded, v₂ dummy
        right
        rcases Finset.mem_map.1 hv₁ with ⟨a1, _, rfl⟩
        have hlt1 : (embed_voter k a1).val < k := by simpa [embed_voter] using a1.isLt
        have hvEq1 : (⟨(embed_voter k a1).val, hlt1⟩ : Fin k) = a1 := by
          apply Fin.ext
          simp [embed_voter]
        have happ1 :
            (extend_instance k inst).approves (embed_voter k a1) =
              (inst.approves a1).map embC := by
          simpa [extend_instance, hlt1, hvEq1, embC]
        have hvd2 : v₂ = dummy_voter k := by simpa using hv₂
        subst hvd2
        have happD :
            (extend_instance k inst).approves (dummy_voter k) = {dummy_candidate k} := by
          simp [extend_instance, dummy_voter]
        have hdummy :
            dummy_candidate k ∉ (inst.approves a1).map embC := by
          intro hx
          rcases Finset.mem_map.1 hx with ⟨c0, _, hEq⟩
          exact dummy_not_embedded k c0 (by simpa using hEq)
        simpa [happ1, happD] using (Finset.disjoint_singleton_left.2 hdummy)
      · -- v₁ dummy, v₂ embedded
        right
        rcases Finset.mem_map.1 hv₂ with ⟨a2, _, rfl⟩
        have hlt2 : (embed_voter k a2).val < k := by simpa [embed_voter] using a2.isLt
        have hvEq2 : (⟨(embed_voter k a2).val, hlt2⟩ : Fin k) = a2 := by
          apply Fin.ext
          simp [embed_voter]
        have happ2 :
            (extend_instance k inst).approves (embed_voter k a2) =
              (inst.approves a2).map embC := by
          simpa [extend_instance, hlt2, hvEq2, embC]
        have hvd1 : v₁ = dummy_voter k := by simpa using hv₁
        subst hvd1
        have happD :
            (extend_instance k inst).approves (dummy_voter k) = {dummy_candidate k} := by
          simp [extend_instance, dummy_voter]
        have hdummy :
            dummy_candidate k ∉ (inst.approves a2).map embC := by
          intro hx
          rcases Finset.mem_map.1 hx with ⟨c0, _, hEq⟩
          exact dummy_not_embedded k c0 (by simpa using hEq)
        simpa [happ2, happD] using (Finset.disjoint_singleton_left.2 hdummy)
      · -- both dummy
        left
        have hvd1 : v₁ = dummy_voter k := by simpa using hv₁
        have hvd2 : v₂ = dummy_voter k := by simpa using hv₂
        subst hvd1
        subst hvd2
        have happD :
            (extend_instance k inst).approves (dummy_voter k) = {dummy_candidate k} := by
          simp [extend_instance, dummy_voter]
        simpa [happD]
    -- candidate lifts to extended candidates
    have hcand_ext :
        embed_candidate k cand ∈ (extend_instance k inst).candidates := by
      have : embed_candidate k cand ∈ inst.candidates.map
          ⟨embed_candidate k, embed_candidate_injective k⟩ :=
        Finset.mem_map.2 ⟨cand, hcand, rfl⟩
      exact Finset.mem_union_left _ this
    -- quota lifts: if a*k ≥ n then a*(k+1) ≥ n+1 (since a>0)
    have hquota_ext :
        (extend_instance k inst).singleton_party_size (embed_candidate k cand) * (k + 1) ≥
          (extend_instance k inst).voters.card := by
      have hmul_pos : 0 < inst.singleton_party_size cand * k := by
        have hpos : 0 < inst.voters.card := Finset.card_pos.mpr inst.voters_nonempty
        exact lt_of_lt_of_le hpos hquota
      have hsize_pos : 0 < inst.singleton_party_size cand := by
        have hmul_pos' : 0 < k * inst.singleton_party_size cand := by
          simpa [Nat.mul_comm] using hmul_pos
        exact Nat.pos_of_mul_pos_left hmul_pos'
      have ha_pos : 1 ≤ inst.singleton_party_size cand := Nat.succ_le_iff.2 hsize_pos
      -- extend singleton parties: size does not decrease
      let embV : Fin k ↪ Fin (k + 1) := ⟨embed_voter k, embed_voter_injective k⟩
      have hsub :
          (inst.singleton_party cand).map embV ⊆
            (extend_instance k inst).singleton_party (embed_candidate k cand) := by
        intro v hv
        rcases Finset.mem_map.1 hv with ⟨v0, hv0, rfl⟩
        have hvv : embed_voter k v0 ∈ (extend_instance k inst).voters :=
          Finset.mem_union_left _ (Finset.mem_map.2 ⟨v0, (Finset.mem_filter.1 hv0).1, rfl⟩)
        have hvapp0 : inst.approves v0 = {cand} := (Finset.mem_filter.1 hv0).2
        have hlt : (embed_voter k v0).val < k := by
          simpa [embed_voter] using v0.isLt
        have hvEq : (⟨(embed_voter k v0).val, hlt⟩ : Fin k) = v0 := by
          apply Fin.ext
          simp [embed_voter]
        have hvapp :
            (extend_instance k inst).approves (embed_voter k v0) = {embed_candidate k cand} := by
          simpa [extend_instance, hlt, hvEq, hvapp0] using
            (Finset.map_singleton
              ⟨embed_candidate k, embed_candidate_injective k⟩ cand)
        exact Finset.mem_filter.2 ⟨hvv, hvapp⟩
      have hcard_le :
          (inst.singleton_party cand).card ≤
            ((extend_instance k inst).singleton_party (embed_candidate k cand)).card := by
        have hmap_card :
            ((inst.singleton_party cand).map embV).card = (inst.singleton_party cand).card := by
          simpa using (Finset.card_map (s := inst.singleton_party cand) embV)
        have hcard_sub : ((inst.singleton_party cand).map embV).card ≤
            ((extend_instance k inst).singleton_party (embed_candidate k cand)).card :=
          Finset.card_le_card hsub
        simpa [hmap_card] using hcard_sub
      have hvoters_card :
          (extend_instance k inst).voters.card = inst.voters.card + 1 := by
        have hd : dummy_voter k ∉ inst.voters.map embV := by
          intro hx
          rcases Finset.mem_map.1 hx with ⟨v0, _, hEq⟩
          have : (embed_voter k v0).val = k := by
            simpa [dummy_voter] using congrArg Fin.val hEq
          have : v0.val = k := by simpa [embed_voter] using this
          exact (Nat.ne_of_lt v0.isLt) this
        have hdisj : Disjoint (inst.voters.map embV) {dummy_voter k} :=
          Finset.disjoint_singleton_right.2 hd
        calc
          (extend_instance k inst).voters.card
              = (inst.voters.map embV ∪ {dummy_voter k}).card := by rfl
          _ = (inst.voters.map embV).card + 1 := by
              simpa [Finset.card_singleton] using Finset.card_union_of_disjoint hdisj
          _ = inst.voters.card + 1 := by
              simpa using congrArg (fun t => t + 1) (Finset.card_map (s := inst.voters) embV)
      have hsingle_le :
          inst.singleton_party_size cand ≤
            (extend_instance k inst).singleton_party_size (embed_candidate k cand) := by
        simpa [ABCInstance.singleton_party_size] using hcard_le
      have hquota' :
          inst.singleton_party_size cand * (k + 1) ≥ inst.voters.card + 1 := by
        have : inst.singleton_party_size cand * (k + 1) =
            inst.singleton_party_size cand * k + inst.singleton_party_size cand := by
          simpa [Nat.mul_succ]
        rw [this]
        exact add_le_add hquota ha_pos
      have hquota'' :
          (extend_instance k inst).singleton_party_size (embed_candidate k cand) * (k + 1) ≥
            inst.voters.card + 1 := by
        exact le_trans hquota' (Nat.mul_le_mul_right (k + 1) hsingle_le)
      simpa [hvoters_card] using hquota''
    have hc_ext : embed_candidate k cand ∈ W0 := by
      exact hprop (extend_instance k inst) (embed_candidate k cand)
        hpl_ext hcand_ext hquota_ext W0 hW0
    exact (mem_project_committee_iff (k := k) (W := W0) (c := cand)).2 hc_ext
  · -- cautious strategyproofness
    intro inst inst' i hi hvar
    classical
    intro hpref
    have h_prefeq :
        cautious_prefeq (inst.approves i) (f' inst') (f' inst) := hpref.1
    have h_not_prefeq :
        ¬cautious_prefeq (inst.approves i) (f' inst) (f' inst') := hpref.2
    have h_prefeq' :
        cautious_prefeq ((inst.approves i).map
          ⟨embed_candidate k, embed_candidate_injective k⟩)
          (f (extend_instance k inst')) (f (extend_instance k inst)) := by
      have h1 :
          cautious_prefeq (inst.approves i)
            ((f (extend_instance k inst')).image (project_committee k))
            ((f (extend_instance k inst)).image (project_committee k)) := by
        simpa [f', induced_rule] using h_prefeq
      exact (cautious_prefeq_project_iff (k := k) (A := inst.approves i)
        (X := f (extend_instance k inst'))
        (X' := f (extend_instance k inst))).1 h1
    have h_not_prefeq' :
        ¬cautious_prefeq ((inst.approves i).map
          ⟨embed_candidate k, embed_candidate_injective k⟩)
          (f (extend_instance k inst)) (f (extend_instance k inst')) := by
      intro h
      have h1 :
          cautious_prefeq (inst.approves i)
            ((f (extend_instance k inst)).image (project_committee k))
            ((f (extend_instance k inst')).image (project_committee k)) :=
        (cautious_prefeq_project_iff (k := k) (A := inst.approves i)
          (X := f (extend_instance k inst))
          (X' := f (extend_instance k inst'))).2 h
      exact h_not_prefeq (by simpa [f', induced_rule] using h1)
    have hvar_ext :
        (extend_instance k inst).is_i_variant
          (extend_instance k inst') (embed_voter k i) :=
      extend_instance_is_variant (k := k) (inst := inst) (inst' := inst') i hvar
    have hi_ext :
        embed_voter k i ∈ (extend_instance k inst).voters :=
      Finset.mem_union_left _ (Finset.mem_map.2 ⟨i, hi, rfl⟩)
    let embC : Fin (k + 1) ↪ Fin (k + 2) := ⟨embed_candidate k, embed_candidate_injective k⟩
    have happ :
        (extend_instance k inst).approves (embed_voter k i) =
          (inst.approves i).map embC := by
      have hlt : (embed_voter k i).val < k := by
        simpa [embed_voter] using i.isLt
      have hvEq : (⟨(embed_voter k i).val, hlt⟩ : Fin k) = i := by
        apply Fin.ext
        simp [embed_voter]
      simpa [extend_instance, hlt, embC, hvEq]
    have hpref'' :
        cautious_pref ((extend_instance k inst).approves (embed_voter k i))
          (f (extend_instance k inst')) (f (extend_instance k inst)) := by
      simpa [happ] using (⟨h_prefeq', h_not_prefeq'⟩ : cautious_pref
        ((inst.approves i).map embC)
        (f (extend_instance k inst')) (f (extend_instance k inst)))
    exact (hsp (extend_instance k inst) (extend_instance k inst') (embed_voter k i)
      hi_ext hvar_ext hpref'')

end KluivingDeVriesVrijbergenBoixelEndriss.InductionK
