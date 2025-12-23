import ABCVoting.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.Peters.InductionM
import Mathlib.Data.Finset.Card

open Finset BigOperators ABCInstance
open Peters.InductionM

namespace KluivingDeVriesVrijbergenBoixelEndriss.InductionM

variable {V : Type*} [DecidableEq V] {k : ℕ}

-- ============================================================================
-- HELPER LEMMAS
-- ============================================================================

lemma mem_approvedCandidates_iff_approved (inst : ABCInstance V (Fin m) k) (c : Fin m) :
    c ∈ inst.approvedCandidates ↔ inst.is_approved c := by
  constructor
  · intro hc
    rcases Finset.mem_biUnion.mp (by
        simpa [ABCInstance.approvedCandidates] using hc) with ⟨v, hv, hcv⟩
    exact ⟨v, hv, hcv⟩
  · rintro ⟨v, hv, hcv⟩
    exact Finset.mem_biUnion.mpr ⟨v, hv, hcv⟩

lemma approvedCandidates_subset_candidates (inst : ABCInstance V (Fin m) k) :
    inst.approvedCandidates ⊆ inst.candidates := by
  intro c hc
  rcases Finset.mem_biUnion.mp (by
      simpa [ABCInstance.approvedCandidates] using hc) with ⟨v, hv, hcv⟩
  exact inst.approves_subset v hv hcv

lemma approvedCandidates_ext {inst inst' : ABCInstance V (Fin m) k}
    (hv : inst.voters = inst'.voters) (_hc : inst.candidates = inst'.candidates)
    (ha : ∀ v ∈ inst.voters, inst.approves v = inst'.approves v) :
    inst.approvedCandidates = inst'.approvedCandidates := by
  ext c
  constructor
  · intro hc_mem
    rcases Finset.mem_biUnion.mp (by
        simpa [ABCInstance.approvedCandidates] using hc_mem) with ⟨v, hv', hcv⟩
    have hv'' : v ∈ inst'.voters := by simpa [hv] using hv'
    have hcv' : c ∈ inst'.approves v := by
      simpa [ha v hv'] using hcv
    exact Finset.mem_biUnion.mpr ⟨v, hv'', hcv'⟩
  · intro hc_mem
    rcases Finset.mem_biUnion.mp (by
        simpa [ABCInstance.approvedCandidates] using hc_mem) with ⟨v, hv', hcv⟩
    have hv'' : v ∈ inst.voters := by simpa [hv] using hv'
    have hcv' : c ∈ inst.approves v := by
      have := ha v hv''
      simpa [this] using hcv
    exact Finset.mem_biUnion.mpr ⟨v, hv'', hcv'⟩

lemma approvedCandidates_extend_candidates (m : ℕ) (inst : ABCInstance V (Fin m) k) :
    (extend_candidates m inst).approvedCandidates =
      inst.approvedCandidates.map ⟨embed_candidate m, embed_candidate_injective m⟩ := by
  classical
  let emb : Fin m ↪ Fin (m + 1) := ⟨embed_candidate m, embed_candidate_injective m⟩
  ext c
  constructor
  · intro hc
    rcases Finset.mem_biUnion.mp (by
        simpa [ABCInstance.approvedCandidates] using hc) with ⟨v, hv, hcv⟩
    have hcv' : c ∈ (inst.approves v).map emb := by
      simpa [extend_candidates, emb] using hcv
    rcases Finset.mem_map.1 hcv' with ⟨c', hc', rfl⟩
    exact Finset.mem_map.2 ⟨c', by
      exact (by
        simpa [ABCInstance.approvedCandidates] using
          (Finset.mem_biUnion.mpr ⟨v, hv, hc'⟩)), rfl⟩
  · intro hc
    rcases Finset.mem_map.1 hc with ⟨c', hc', rfl⟩
    rcases Finset.mem_biUnion.mp (by
        simpa [ABCInstance.approvedCandidates] using hc') with ⟨v, hv, hcv⟩
    have hcv' : embed_candidate m c' ∈ (inst.approves v).map emb :=
      Finset.mem_map.2 ⟨c', hcv, rfl⟩
    have hcv'' : embed_candidate m c' ∈ (extend_candidates m inst).approves v := by
      simpa [extend_candidates, emb] using hcv'
    exact Finset.mem_biUnion.mpr ⟨v, hv, hcv''⟩

lemma dominates_unapproved (inst : ABCInstance V (Fin m) k) (a b : Fin m)
    (ha : inst.is_approved a) (hb : inst.is_unapproved b) :
    inst.dominates a b := by
  refine ⟨?_, ?_⟩
  · intro v hv hbv
    exact (hb v hv hbv).elim
  · rcases ha with ⟨v, hv, hav⟩
    exact ⟨v, hv, hav, hb v hv⟩

lemma no_unapproved_in_committee_of_many_approved
    (inst : ABCInstance V (Fin m) k)
    (f : ABCRule V (Fin m) k)
    (hwf : f.IsWellFormed)
    (heff : f.SatisfiesDominatingCandidateEfficiency)
    (hcard : inst.approvedCandidates.card ≥ k)
    (W : Finset (Fin m)) (hW : W ∈ f inst) :
    W ⊆ inst.approvedCandidates := by
  intro b hbW
  by_contra hb
  have hb_unapproved : inst.is_unapproved b := by
    intro v hv hbv
    exact hb (Finset.mem_biUnion.mpr ⟨v, hv, hbv⟩)
  have hW_card : W.card = k := (hwf inst).2 _ hW |>.1
  have hW_sub : W ⊆ inst.candidates := (hwf inst).2 _ hW |>.2
  have hsub : inst.approvedCandidates ⊆ W := by
    intro a ha
    have ha_approved : inst.is_approved a :=
      (mem_approvedCandidates_iff_approved inst a).1 ha
    have hdom : inst.dominates a b := dominates_unapproved inst a b ha_approved hb_unapproved
    exact heff inst a b (approvedCandidates_subset_candidates inst ha) (hW_sub hbW) hdom W hW hbW
  have hcard_le : inst.approvedCandidates.card ≤ W.card :=
    Finset.card_le_card hsub
  have hcard_ge : W.card ≤ inst.approvedCandidates.card := by
    have : k ≤ inst.approvedCandidates.card := hcard
    simpa [hW_card] using this
  have h_eq : inst.approvedCandidates = W :=
    Finset.subset_iff_eq_of_card_le hcard_ge |>.mp hsub
  exact hb (by simpa [h_eq] using hbW)

lemma dummy_not_in_committee_of_many_approved
    (m : ℕ) (inst : ABCInstance V (Fin m) k)
    (f : ABCRule V (Fin (m + 1)) k)
    (hwf : f.IsWellFormed)
    (heff : f.SatisfiesDominatingCandidateEfficiency)
    (hcard : inst.approvedCandidates.card ≥ k)
    (W : Finset (Fin (m + 1))) (hW : W ∈ f (extend_candidates m inst)) :
    dummy_candidate m ∉ W := by
  have hcard_ext : (extend_candidates m inst).approvedCandidates.card ≥ k := by
    have hmap :=
      congrArg Finset.card (approvedCandidates_extend_candidates (V := V) (k := k) m inst)
    have hcard_map :
        (extend_candidates m inst).approvedCandidates.card =
          inst.approvedCandidates.card := by
      simpa using hmap
    simpa [hcard_map] using hcard
  have hsubset :=
    no_unapproved_in_committee_of_many_approved
      (inst := extend_candidates m inst) (f := f) (hwf := hwf) (heff := heff)
      hcard_ext W hW
  intro hd
  have hmem :
      dummy_candidate m ∈ (extend_candidates m inst).approvedCandidates := hsubset hd
  rcases (mem_approvedCandidates_iff_approved (extend_candidates m inst) (dummy_candidate m)).1 hmem with
    ⟨v, hv, hcv⟩
  exact (dummy_unapproved (V := V) (k := k) (m := m) inst v hv hcv).elim

lemma map_project_inter_eq (m : ℕ) (A : Finset (Fin m)) (W : Finset (Fin (m + 1))) :
    (project_committee m W ∩ A).map
        ⟨embed_candidate m, embed_candidate_injective m⟩ =
      W ∩ A.map ⟨embed_candidate m, embed_candidate_injective m⟩ := by
  classical
  let emb : Fin m ↪ Fin (m + 1) := ⟨embed_candidate m, embed_candidate_injective m⟩
  ext x
  constructor
  · intro hx
    rcases Finset.mem_map.1 hx with ⟨c, hc, hxc⟩
    have hcA : c ∈ A := (Finset.mem_inter.mp hc).2
    have hcW : c ∈ project_committee m W := (Finset.mem_inter.mp hc).1
    have hxW : emb c ∈ W := (mem_project_committee_iff (m := m) (W := W) (c := c)).1 hcW
    have hxA : emb c ∈ A.map emb := Finset.mem_map.2 ⟨c, hcA, rfl⟩
    have hxW' : x ∈ W := by simpa [emb, hxc] using hxW
    have hxA' : x ∈ A.map emb := by simpa [emb, hxc] using hxA
    exact Finset.mem_inter.mpr ⟨hxW', hxA'⟩
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxW, hxA⟩
    rcases Finset.mem_map.1 hxA with ⟨c, hcA, hxc⟩
    have hcW : c ∈ project_committee m W := by
      apply (mem_project_committee_iff (m := m) (W := W) (c := c)).2
      simpa [emb, hxc.symm] using hxW
    have hc : c ∈ project_committee m W ∩ A := by
      exact Finset.mem_inter.mpr ⟨hcW, hcA⟩
    exact Finset.mem_map.2 ⟨c, hc, hxc⟩

lemma card_project_inter_eq (m : ℕ) (A : Finset (Fin m)) (W : Finset (Fin (m + 1))) :
    (project_committee m W ∩ A).card =
      (W ∩ A.map ⟨embed_candidate m, embed_candidate_injective m⟩).card := by
  classical
  let emb : Fin m ↪ Fin (m + 1) := ⟨embed_candidate m, embed_candidate_injective m⟩
  have hmap := Finset.card_map (s := project_committee m W ∩ A) emb
  have hmap' : (project_committee m W ∩ A).map emb = W ∩ A.map emb :=
    map_project_inter_eq (m := m) (A := A) (W := W)
  simpa [hmap'] using hmap.symm

lemma committee_prefeq_project_iff (m : ℕ) (A : Finset (Fin m))
    (W W' : Finset (Fin (m + 1))) :
    committee_prefeq A (project_committee m W) (project_committee m W') ↔
      committee_prefeq (A.map ⟨embed_candidate m, embed_candidate_injective m⟩) W W' := by
  classical
  simp [committee_prefeq, card_project_inter_eq]

lemma cautious_prefeq_project_iff (m : ℕ) (A : Finset (Fin m))
    (X X' : Finset (Finset (Fin (m + 1)))) :
    cautious_prefeq A (X.image (project_committee m)) (X'.image (project_committee m)) ↔
      cautious_prefeq (A.map ⟨embed_candidate m, embed_candidate_injective m⟩) X X' := by
  classical
  constructor
  · intro h W hW W' hW'
    have hWimg : project_committee m W ∈ X.image (project_committee m) :=
      Finset.mem_image.mpr ⟨W, hW, rfl⟩
    have hW'img : project_committee m W' ∈ X'.image (project_committee m) :=
      Finset.mem_image.mpr ⟨W', hW', rfl⟩
    have hpref := h _ hWimg _ hW'img
    exact (committee_prefeq_project_iff (m := m) (A := A) (W := W) (W' := W')).1 hpref
  · intro h W hW W' hW'
    rcases Finset.mem_image.mp hW with ⟨X0, hX0, rfl⟩
    rcases Finset.mem_image.mp hW' with ⟨X1, hX1, rfl⟩
    have hpref := h X0 hX0 X1 hX1
    exact (committee_prefeq_project_iff (m := m) (A := A) (W := X0) (W' := X1)).2 hpref

lemma extend_candidates_is_variant (m : ℕ) (inst inst' : ABCInstance V (Fin m) k) (i : V)
    (hvar : inst.is_i_variant inst' i) :
    (extend_candidates m inst).is_i_variant (extend_candidates m inst') i := by
  refine ⟨hvar.1, rfl, ?_⟩
  intro v hv hne
  have hv' : v ∈ inst.voters := by simpa [extend_candidates] using hv
  have h_eq := hvar.2.2 v hv' hne
  simp [extend_candidates, h_eq]

-- ============================================================================
-- INDUCED RULE
-- ============================================================================

noncomputable def induced_rule (m : ℕ) {k : ℕ} (f : ABCRule V (Fin (m + 1)) k) :
    ABCRule V (Fin m) k where
  apply inst :=
    if h : inst.approvedCandidates.card ≥ k then
      (f (extend_candidates m inst)).image (project_committee m)
    else
      inst.candidates.powerset.filter (fun W => W.card = k ∧ inst.approvedCandidates ⊆ W)
  extensional := by
    intro inst inst' hv hc ha
    classical
    have hApproved := approvedCandidates_ext (m := m) (inst := inst) (inst' := inst') hv hc ha
    by_cases h1 : inst.approvedCandidates.card ≥ k
    · have h2 : inst'.approvedCandidates.card ≥ k := by simpa [hApproved] using h1
      have h_ext :
          f (extend_candidates m inst) = f (extend_candidates m inst') := by
        apply f.extensional
        · simpa [extend_candidates] using hv
        · rfl
        · intro v hv'
          have hv'' : v ∈ inst.voters := by simpa [extend_candidates] using hv'
          simp [extend_candidates, ha v hv'']
      simp [h2, hApproved, h_ext]
    · have h2 : ¬inst'.approvedCandidates.card ≥ k := by simpa [hApproved] using h1
      simp [h2, hApproved, hc]

-- ============================================================================
-- MAIN LEMMA (CANDIDATES)
-- ============================================================================

theorem induction_m (n m k : ℕ) (_hk : 3 ≤ k) (_hm : k ≤ m)
    (f : ABCRule (Fin n) (Fin (m + 1)) k)
    (hwf : f.IsWellFormed)
    (heff : f.SatisfiesDominatingCandidateEfficiency)
    (hprop : f.SatisfiesMinimalProportionality)
    (hsp : f.SatisfiesCautiousStrategyproofness) :
    ∃ (f' : ABCRule (Fin n) (Fin m) k),
      f'.IsWellFormed ∧
      f'.SatisfiesDominatingCandidateEfficiency ∧
      f'.SatisfiesMinimalProportionality ∧
      f'.SatisfiesCautiousStrategyproofness := by
  classical
  let f' : ABCRule (Fin n) (Fin m) k := induced_rule (V := Fin n) (k := k) m f
  refine ⟨f', ?_⟩
  constructor
  · -- well-formed
    intro inst
    by_cases hcard : inst.approvedCandidates.card ≥ k
    · have hnonempty : (f (extend_candidates m inst)).Nonempty := (hwf _).1
      obtain ⟨W0, hW0⟩ := hnonempty
      have hnonempty' :
          ((f (extend_candidates m inst)).image (project_committee m)).Nonempty :=
        ⟨project_committee m W0, Finset.mem_image.mpr ⟨W0, hW0, rfl⟩⟩
      constructor
      · simpa [f', induced_rule, hcard] using hnonempty'
      · intro W hW
        simp [f', induced_rule, hcard] at hW
        rcases hW with ⟨W', hW', rfl⟩
        have hcardW' : W'.card = k := (hwf _).2 _ hW' |>.1
        have hW'_sub : W' ⊆ (extend_candidates m inst).candidates :=
          (hwf _).2 _ hW' |>.2
        have hdummy :
            dummy_candidate m ∉ W' :=
          dummy_not_in_committee_of_many_approved
            (m := m) (inst := inst) (f := f) (hwf := hwf) (heff := heff) hcard W' hW'
        have hmap :
            (project_committee m W').map
              ⟨embed_candidate m, embed_candidate_injective m⟩ = W' :=
          map_project_committee_eq_of_not_dummy (m := m) (W := W') hdummy
        have hcard_proj : (project_committee m W').card = k := by
          have hcard_map := Finset.card_map (s := project_committee m W')
            ⟨embed_candidate m, embed_candidate_injective m⟩
          have hcard_map' :
              (project_committee m W').card = W'.card := by
            simpa [hmap] using hcard_map.symm
          simpa [hcardW'] using hcard_map'
        constructor
        · exact hcard_proj
        · intro c hc
          have hc' :
              embed_candidate m c ∈ W' :=
            (mem_project_committee_iff (m := m) (W := W') (c := c)).1 hc
          have hmem :
              embed_candidate m c ∈ (extend_candidates m inst).approvedCandidates := by
            have hsubset :=
              no_unapproved_in_committee_of_many_approved
                (inst := extend_candidates m inst) (f := f) (hwf := hwf) (heff := heff)
                (by
                  have hmap :=
                    congrArg Finset.card (approvedCandidates_extend_candidates
                      (V := Fin n) (k := k) m inst)
                  simpa [hmap] using hcard)
                W' hW'
            exact hsubset hc'
          have hmem' :
              c ∈ inst.approvedCandidates := by
            have hmap :=
              approvedCandidates_extend_candidates (V := Fin n) (k := k) m inst
            have hmem_map :
                embed_candidate m c ∈ inst.approvedCandidates.map
                  ⟨embed_candidate m, embed_candidate_injective m⟩ := by
              simpa [hmap] using hmem
            rcases Finset.mem_map.1 hmem_map with ⟨c', hc', hEq⟩
            have hc_eq : c' = c := by
              apply embed_candidate_injective m
              simpa using hEq
            simpa [hc_eq] using hc'
          exact approvedCandidates_subset_candidates inst hmem'
    · constructor
      · -- nonempty: choose any superset of approvedCandidates of size k
        have hsub : inst.approvedCandidates ⊆ inst.candidates :=
          approvedCandidates_subset_candidates inst
        have hsize : inst.approvedCandidates.card ≤ k := Nat.le_of_not_ge hcard
        obtain ⟨W, hWsub, hWcand, hWcard⟩ :=
          Finset.exists_subsuperset_card_eq hsub hsize inst.k_le_m
        have hWmem :
            W ∈ inst.candidates.powerset.filter
              (fun W => W.card = k ∧ inst.approvedCandidates ⊆ W) := by
          simp [Finset.mem_filter, Finset.mem_powerset, hWcand, hWcard, hWsub]
        simpa [f', induced_rule, hcard] using ⟨W, hWmem⟩
      · intro W hW
        simp [f', induced_rule, hcard] at hW
        rcases hW with ⟨hWsub, hWcard, _⟩
        exact ⟨hWcard, hWsub⟩
  constructor
  · -- dominating candidate efficiency
    intro inst a b ha hb hdom W hW hbW
    by_cases hcard : inst.approvedCandidates.card ≥ k
    · simp [f', induced_rule, hcard] at hW
      rcases hW with ⟨W', hW', rfl⟩
      have hb' :
          embed_candidate m b ∈ W' :=
        (mem_project_committee_iff (m := m) (W := W') (c := b)).1 hbW
      have hdom' : (extend_candidates m inst).dominates
          (embed_candidate m a) (embed_candidate m b) := by
        refine ⟨?_, ?_⟩
        · intro v hv hbv
          rcases Finset.mem_map.1 hbv with ⟨b', hb', hEq⟩
          have hb_eq : b' = b := by
            apply embed_candidate_injective m
            simpa using hEq
          have hbv' : b ∈ inst.approves v := by simpa [hb_eq] using hb'
          have hav : a ∈ inst.approves v := hdom.1 v hv hbv'
          exact Finset.mem_map.2 ⟨a, hav, rfl⟩
        · rcases hdom.2 with ⟨v, hv, hav, hbv⟩
          refine ⟨v, hv, ?_, ?_⟩
          · exact Finset.mem_map.2 ⟨a, hav, rfl⟩
          · intro hbv'
            rcases Finset.mem_map.1 hbv' with ⟨b', hb', hEq⟩
            have hb_eq : b' = b := by
              apply embed_candidate_injective m
              simpa using hEq
            exact hbv (by simpa [hb_eq] using hb')
      have ha' :
          embed_candidate m a ∈ W' :=
        heff (extend_candidates m inst) (embed_candidate m a) (embed_candidate m b)
          (by simp [extend_candidates]) (by simp [extend_candidates]) hdom' W' hW' hb'
      exact (mem_project_committee_iff (m := m) (W := W') (c := a)).2 ha'
    · simp [f', induced_rule, hcard] at hW
      rcases hW with ⟨_, _, hWap⟩
      have ha_approved : inst.is_approved a := by
        rcases hdom.2 with ⟨v, hv, hav, _⟩
        exact ⟨v, hv, hav⟩
      have ha_mem : a ∈ inst.approvedCandidates :=
        (mem_approvedCandidates_iff_approved inst a).2 ha_approved
      exact hWap ha_mem
  constructor
  · -- minimal proportionality
    intro inst c hpl hc hsize W hW
    by_cases hcard : inst.approvedCandidates.card ≥ k
    · simp [f', induced_rule, hcard] at hW
      rcases hW with ⟨W', hW', rfl⟩
      have hpl' : (extend_candidates m inst).is_party_list :=
        extend_candidates_party_list (V := Fin n) (k := k) (m := m) inst hpl
      have hsize' :
          (extend_candidates m inst).singleton_party_size
              (embed_candidate m c) * k ≥ (extend_candidates m inst).voters.card := by
        have hsize_voters : inst.singleton_party_size c * k ≥ (extend_candidates m inst).voters.card := by
          simpa [extend_candidates] using hsize
        simpa [singleton_party_size_extend_candidates (m := m) (inst := inst) (c := c)] using hsize_voters
      have hc' :
          embed_candidate m c ∈ (extend_candidates m inst).candidates := by
        simp [extend_candidates]
      have hc_in :
          embed_candidate m c ∈ W' :=
        hprop (extend_candidates m inst) (embed_candidate m c) hpl' hc' hsize' W' hW'
      exact (mem_project_committee_iff (m := m) (W := W') (c := c)).2 hc_in
    · simp [f', induced_rule, hcard] at hW
      rcases hW with ⟨_, _, hWap⟩
      have hc_mem : c ∈ inst.approvedCandidates := by
        -- singleton party size ≥ n/k implies c is approved
        have hvpos : 0 < inst.voters.card := Finset.card_pos.mpr inst.voters_nonempty
        have hmul_pos : 0 < inst.singleton_party_size c * k :=
          lt_of_lt_of_le hvpos hsize
        have hsize_pos : 0 < inst.singleton_party_size c := by
          have hmul_pos' : 0 < k * inst.singleton_party_size c := by
            simpa [Nat.mul_comm] using hmul_pos
          exact Nat.pos_of_mul_pos_left hmul_pos'
        have hnonempty : (inst.singleton_party c).Nonempty := by
          have : 0 < (inst.singleton_party c).card := by
            simpa [ABCInstance.singleton_party_size] using hsize_pos
          exact Finset.card_pos.mp this
        rcases hnonempty with ⟨v, hv⟩
        have hv' : v ∈ inst.voters := (mem_singleton_party_iff inst c v).1 hv |>.1
        have hcv : c ∈ inst.approves v := singleton_party_approves inst c v hv
        exact (mem_approvedCandidates_iff_approved inst c).2 ⟨v, hv', hcv⟩
      exact hWap hc_mem
  · -- cautious strategyproofness
    intro inst inst' i hi hvar
    classical
    by_cases hcard : inst.approvedCandidates.card ≥ k
    · by_cases hcard' : inst'.approvedCandidates.card ≥ k
      · -- both branches use f on the extended instances
        intro hpref
        have h_prefeq :
            cautious_prefeq (inst.approves i)
              (f' inst') (f' inst) := hpref.1
        have h_not_prefeq :
            ¬cautious_prefeq (inst.approves i)
              (f' inst) (f' inst') := hpref.2
        have h_prefeq' :
            cautious_prefeq ((inst.approves i).map
              ⟨embed_candidate m, embed_candidate_injective m⟩)
              (f (extend_candidates m inst')) (f (extend_candidates m inst)) := by
          have h1 :
              cautious_prefeq (inst.approves i)
                ((f (extend_candidates m inst')).image (project_committee m))
                ((f (extend_candidates m inst)).image (project_committee m)) := by
            simpa [f', induced_rule, hcard', hcard] using h_prefeq
          exact (cautious_prefeq_project_iff (m := m) (A := inst.approves i)
            (X := f (extend_candidates m inst')) (X' := f (extend_candidates m inst))).1 h1
        have h_not_prefeq' :
            ¬cautious_prefeq ((inst.approves i).map
              ⟨embed_candidate m, embed_candidate_injective m⟩)
              (f (extend_candidates m inst)) (f (extend_candidates m inst')) := by
          intro h
          have h1 :
              cautious_prefeq (inst.approves i)
                ((f (extend_candidates m inst)).image (project_committee m))
                ((f (extend_candidates m inst')).image (project_committee m)) :=
            (cautious_prefeq_project_iff (m := m) (A := inst.approves i)
              (X := f (extend_candidates m inst)) (X' := f (extend_candidates m inst'))).2 h
          exact h_not_prefeq (by simpa [f', induced_rule, hcard', hcard] using h1)
        have hvar_ext :
            (extend_candidates m inst).is_i_variant
              (extend_candidates m inst') i :=
          extend_candidates_is_variant (m := m) (inst := inst) (inst' := inst') i hvar
        have hpref' :
            cautious_pref
              ((inst.approves i).map ⟨embed_candidate m, embed_candidate_injective m⟩)
              (f (extend_candidates m inst')) (f (extend_candidates m inst)) :=
          ⟨h_prefeq', h_not_prefeq'⟩
        exact (hsp (extend_candidates m inst) (extend_candidates m inst') i hi hvar_ext hpref')
      · -- inst uses f, inst' uses "all supersets" branch
        intro hpref
        have hcard'' : inst'.approvedCandidates.card < k :=
          Nat.lt_of_not_ge hcard'
        let S : Finset (Fin n) := inst.voters.erase i
        let T : Finset (Fin m) := inst.union_approvals S \ inst.approves i
        have hT_subset' :
            T ⊆ inst'.approvedCandidates := by
          intro c hc
          have hc' : c ∈ inst.union_approvals S := (Finset.mem_sdiff.mp hc).1
          rcases Finset.mem_biUnion.mp (by
              simpa [ABCInstance.union_approvals] using hc') with ⟨v, hv, hcv⟩
          have hv' : v ∈ inst'.voters := by
            have hv'' : v ∈ inst.voters := (Finset.mem_erase.mp hv).2
            simpa [hvar.1] using hv''
          have hne : v ≠ i := (Finset.mem_erase.mp hv).1
          have hcv' : c ∈ inst'.approves v := by
            have h_eq := hvar.2.2 v (Finset.mem_erase.mp hv).2 hne
            simpa [h_eq] using hcv
          exact Finset.mem_biUnion.mpr ⟨v, hv', hcv'⟩
        have hT_card : T.card < k := by
          have hcard_le :
              T.card ≤ inst'.approvedCandidates.card :=
            Finset.card_le_card hT_subset'
          exact lt_of_le_of_lt hcard_le hcard''
        have h_prefeq :
            cautious_prefeq (inst.approves i) (f' inst) (f' inst') := by
          intro W hW W' hW'
          -- lower bound for W
          have hW_mem :
              W ∈ (f (extend_candidates m inst)).image (project_committee m) := by
            simpa [f', induced_rule, hcard] using hW
          rcases Finset.mem_image.mp hW_mem with ⟨W0, hW0, rfl⟩
          have hW0_sub :
              W0 ⊆ (extend_candidates m inst).approvedCandidates :=
            no_unapproved_in_committee_of_many_approved
              (inst := extend_candidates m inst) (f := f) (hwf := hwf) (heff := heff)
              (by
                have hmap :=
                  congrArg Finset.card (approvedCandidates_extend_candidates
                    (V := Fin n) (k := k) m inst)
                simpa [hmap] using hcard)
              W0 hW0
          have hW_sub :
              (project_committee m W0) ⊆ inst.approvedCandidates := by
            intro c hc
            have hc' : embed_candidate m c ∈ W0 :=
              (mem_project_committee_iff (m := m) (W := W0) (c := c)).1 hc
            have hmem :
                embed_candidate m c ∈ (extend_candidates m inst).approvedCandidates :=
              hW0_sub hc'
            have hmap :=
              approvedCandidates_extend_candidates (V := Fin n) (k := k) m inst
            have hmem' :
                embed_candidate m c ∈ inst.approvedCandidates.map
                  ⟨embed_candidate m, embed_candidate_injective m⟩ := by
              simpa [hmap] using hmem
            rcases Finset.mem_map.1 hmem' with ⟨c', hc', hEq⟩
            have hc_eq : c' = c := by
              apply embed_candidate_injective m
              simpa using hEq
            simpa [hc_eq] using hc'
          have hW_sub' : (project_committee m W0 \ inst.approves i) ⊆ T := by
            intro c hc
            have hcW : c ∈ project_committee m W0 := (Finset.mem_sdiff.mp hc).1
            have hcA : c ∉ inst.approves i := (Finset.mem_sdiff.mp hc).2
            have hcApp : c ∈ inst.approvedCandidates := hW_sub hcW
            have hcUnion : c ∈ inst.union_approvals S := by
              rcases Finset.mem_biUnion.mp (by
                  simpa [ABCInstance.approvedCandidates] using hcApp) with ⟨v, hv, hcv⟩
              by_cases hvi : v = i
              · subst hvi
                exact (hcA hcv).elim
              · have hvS : v ∈ S := by
                  exact Finset.mem_erase.mpr ⟨hvi, hv⟩
                exact Finset.mem_biUnion.mpr ⟨v, hvS, hcv⟩
            exact Finset.mem_sdiff.mpr ⟨hcUnion, hcA⟩
          have hW_card : (project_committee m W0).card = k := by
            have hcardW0 : W0.card = k := (hwf _).2 _ hW0 |>.1
            have hdummy :
                dummy_candidate m ∉ W0 :=
              dummy_not_in_committee_of_many_approved
                (m := m) (inst := inst) (f := f) (hwf := hwf) (heff := heff) hcard W0 hW0
            have hmap :
                (project_committee m W0).map
                  ⟨embed_candidate m, embed_candidate_injective m⟩ = W0 :=
              map_project_committee_eq_of_not_dummy (m := m) (W := W0) hdummy
            have hcard_map := Finset.card_map (s := project_committee m W0)
              ⟨embed_candidate m, embed_candidate_injective m⟩
            have hcard_map' :
                (project_committee m W0).card = W0.card := by
              simpa [hmap] using hcard_map.symm
            simpa [hcardW0] using hcard_map'
          have hW_lower : (project_committee m W0 ∩ inst.approves i).card ≥ k - T.card := by
            have hcard_eq :
                (project_committee m W0 ∩ inst.approves i).card +
                    (project_committee m W0 \ inst.approves i).card =
                  k := by
              simpa [hW_card] using
                (Finset.card_inter_add_card_sdiff (project_committee m W0) (inst.approves i))
            have hsdiff_le :
                (project_committee m W0 \ inst.approves i).card ≤ T.card :=
              Finset.card_le_card hW_sub'
            omega
          -- upper bound for W'
          have hW'branch :
              inst'.approvedCandidates ⊆ W' := by
            simp [f', induced_rule, hcard'] at hW'
            exact hW'.2.2
          have hT_in : T ⊆ W' := by
            intro c hc
            exact hW'branch (by
              exact hT_subset' hc)
          have hW'card : W'.card = k := by
            simp [f', induced_rule, hcard'] at hW'
            exact hW'.2.1
          have hW'upper : (W' ∩ inst.approves i).card ≤ k - T.card := by
            have hsdiff_ge : T.card ≤ (W' \ inst.approves i).card := by
              have hsub : T ⊆ W' \ inst.approves i := by
                intro c hc
                have hcT : c ∈ T := hc
                have hcW : c ∈ W' := hT_in hcT
                have hcA : c ∉ inst.approves i := (Finset.mem_sdiff.mp hcT).2
                exact Finset.mem_sdiff.mpr ⟨hcW, hcA⟩
              exact Finset.card_le_card hsub
            have hcard_eq :
                (W' ∩ inst.approves i).card +
                    (W' \ inst.approves i).card = k := by
              simpa [hW'card] using
                (Finset.card_inter_add_card_sdiff W' (inst.approves i))
            omega
          exact le_trans hW'upper hW_lower
        exact hpref.2 h_prefeq
    · -- inst uses "all supersets" branch
      intro hpref
      have hcard' : ¬inst.approvedCandidates.card ≥ k := by
        exact Nat.not_le_of_lt (Nat.lt_of_not_ge hcard)
      have h_prefeq :
          cautious_prefeq (inst.approves i) (f' inst) (f' inst') := by
        intro W hW W' hW'
        have hWmem : inst.approvedCandidates ⊆ W := by
          simp [f', induced_rule, hcard'] at hW
          exact hW.2.2
        have hAi : inst.approves i ⊆ W := by
          intro c hc
          exact hWmem (Finset.mem_biUnion.mpr ⟨i, hi, hc⟩)
        have hW_inter : (W ∩ inst.approves i) = inst.approves i := by
          exact Finset.inter_eq_right.mpr hAi
        have hW'_inter_le :
            (W' ∩ inst.approves i).card ≤ (inst.approves i).card :=
          Finset.card_le_card (by exact Finset.inter_subset_right)
        have hW_card :
            (W ∩ inst.approves i).card = (inst.approves i).card := by
          simpa [hW_inter]
        have := hW'_inter_le
        simpa [committee_prefeq, hW_card] using this
      exact hpref.2 h_prefeq

end KluivingDeVriesVrijbergenBoixelEndriss.InductionM
