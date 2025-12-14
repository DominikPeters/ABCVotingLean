import ABCVoting.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.Peters.RestrictToPlentiful
import ABCVoting.Impossibilities.Peters.SingletonApprovers

open Finset BigOperators ABCInstance

/-!
# Induction on Committee Size (Lemma 7 from Peters)

This file proves that if there exists a rule satisfying the axioms for
committee size k+1 (with k+1 voters and k+2 candidates), then there exists
such a rule for committee size k (with k voters and k+1 candidates).

The construction adds:
1. A dummy voter who approves only a new dummy candidate
2. A dummy candidate approved only by the dummy voter

By the singleton approvers lemma, the dummy candidate is always elected.
Removing it from the committee gives a size-k committee for the original instance.
-/

namespace Peters.InductionK

open Peters.SingletonApprovers

-- ============================================================================
-- TYPE MAPPINGS
-- ============================================================================

/--
Embed a voter from Fin k into Fin (k+1).
-/
def embed_voter (k : ℕ) : Fin k → Fin (k + 1) :=
  fun v => ⟨v.val, Nat.lt_succ_of_lt v.isLt⟩

lemma embed_voter_injective (k : ℕ) : Function.Injective (embed_voter k) := by
  intro v1 v2 h
  simp [embed_voter, Fin.mk.injEq] at h
  exact Fin.ext h

/--
The dummy voter is the last one (index k).
-/
def dummy_voter (k : ℕ) : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩

/--
Embed a candidate from Fin (k+1) into Fin (k+2).
-/
def embed_candidate (k : ℕ) : Fin (k + 1) → Fin (k + 2) :=
  fun c => ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩

lemma embed_candidate_injective (k : ℕ) : Function.Injective (embed_candidate k) := by
  intro c1 c2 h
  simp [embed_candidate, Fin.mk.injEq] at h
  exact Fin.ext h

/--
The dummy candidate is the last one (index k+1).
-/
def dummy_candidate (k : ℕ) : Fin (k + 2) := ⟨k + 1, Nat.lt_succ_self (k + 1)⟩

lemma dummy_not_embedded (k : ℕ) (c : Fin (k + 1)) :
    embed_candidate k c ≠ dummy_candidate k := by
  simp [embed_candidate, dummy_candidate, Fin.mk.injEq]
  exact Nat.ne_of_lt c.isLt

-- ============================================================================
-- INSTANCE EXTENSION
-- ============================================================================

/--
Given an instance with k voters and k+1 candidates (committee size k),
create an instance with k+1 voters and k+2 candidates (committee size k+1).

The new voter (dummy) approves only the new candidate (dummy).
-/
def extend_instance (k : ℕ) (inst : ABCInstance (Fin k) (Fin (k + 1)) k) :
    ABCInstance (Fin (k + 1)) (Fin (k + 2)) (k + 1) where
  voters :=
    inst.voters.map ⟨embed_voter k, embed_voter_injective k⟩ ∪ {dummy_voter k}
  candidates :=
    inst.candidates.map ⟨embed_candidate k, embed_candidate_injective k⟩ ∪ {dummy_candidate k}
  approves := fun v =>
    if h : v.val < k then
      -- Original voter: embed their approval set
      (inst.approves ⟨v.val, h⟩).map ⟨embed_candidate k, embed_candidate_injective k⟩
    else
      -- Dummy voter: approves only dummy candidate
      {dummy_candidate k}
  approves_subset := by
    classical
    intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · -- embedded voter
      rcases Finset.mem_map.1 hv with ⟨v0, hv0, rfl⟩
      have hlt : (embed_voter k v0).val < k := by
        simpa [embed_voter] using v0.isLt
      -- approvals are the map of inst.approves v0
      have happ :
          (if h : (embed_voter k v0).val < k then
              (inst.approves ⟨(embed_voter k v0).val, h⟩).map
                ⟨embed_candidate k, by
                  intro c1 c2 heq
                  simp only [embed_candidate, Fin.mk.injEq] at heq
                  exact Fin.ext heq⟩
            else {dummy_candidate k}) =
            (inst.approves v0).map ⟨embed_candidate k, embed_candidate_injective k⟩ := by
        simp [hlt, embed_voter, embed_candidate]
      -- subset of mapped candidates
      have hsub0 : inst.approves v0 ⊆ inst.candidates := inst.approves_subset v0 hv0
      have hsub1 :
          (inst.approves v0).map ⟨embed_candidate k, embed_candidate_injective k⟩ ⊆
            inst.candidates.map ⟨embed_candidate k, embed_candidate_injective k⟩ :=
        Finset.map_subset_map.2 hsub0
      have hsub2 :
          inst.candidates.map ⟨embed_candidate k, embed_candidate_injective k⟩ ⊆
            inst.candidates.map ⟨embed_candidate k, embed_candidate_injective k⟩ ∪ {dummy_candidate k} :=
        Finset.subset_union_left
      have : (inst.approves v0).map ⟨embed_candidate k, embed_candidate_injective k⟩ ⊆
          inst.candidates.map ⟨embed_candidate k, embed_candidate_injective k⟩ ∪ {dummy_candidate k} :=
        hsub1.trans hsub2
      -- now rewrite the approval set at this voter
      simpa [hlt, happ] using this
    · -- dummy voter
      have : v = dummy_voter k := by simpa using hv
      subst this
      have hklt : ¬(dummy_voter k).val < k := by
        simp [dummy_voter]
      intro x hx
      have hx' : x = dummy_candidate k := by
        simpa [hklt] using hx
      subst hx'
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  voters_nonempty := by
    classical
    rcases inst.voters_nonempty with ⟨v0, hv0⟩
    refine ⟨embed_voter k v0, ?_⟩
    exact Finset.mem_union_left _ (Finset.mem_map.2 ⟨v0, hv0, rfl⟩)
  k_pos := Nat.succ_pos k
  k_le_m := by
    classical
    let embC : Fin (k + 1) ↪ Fin (k + 2) := ⟨embed_candidate k, embed_candidate_injective k⟩
    have hdummy : dummy_candidate k ∉ inst.candidates.map embC := by
      intro hx
      rcases Finset.mem_map.1 hx with ⟨c, hc, hEq⟩
      exact dummy_not_embedded k c (by simpa [embC] using hEq)
    have hdisj : Disjoint (inst.candidates.map embC) {dummy_candidate k} :=
      Finset.disjoint_singleton_right.2 hdummy
    have hcard :
        (inst.candidates.map embC ∪ {dummy_candidate k}).card =
          (inst.candidates.map embC).card + 1 := by
      simpa [Finset.card_singleton] using (Finset.card_union_of_disjoint hdisj)
    have hcard_map : (inst.candidates.map embC).card = inst.candidates.card := by
      simpa using (Finset.card_map (s := inst.candidates) embC)
    have hcand_card :
        (inst.candidates.map embC ∪ {dummy_candidate k}).card = inst.candidates.card + 1 := by
      calc
        (inst.candidates.map embC ∪ {dummy_candidate k}).card
            = (inst.candidates.map embC).card + 1 := hcard
        _ = inst.candidates.card + 1 := by simpa [hcard_map]
    -- rewrite the goal to the simpler cardinality bound
    rw [hcand_card]
    exact Nat.add_le_add_right inst.k_le_m 1

/--
The dummy candidate is approved only by the dummy voter.
This means its singleton party has size 1, which equals (k+1)/(k+1) = 1.
-/
lemma dummy_singleton_party (k : ℕ) (inst : ABCInstance (Fin k) (Fin (k + 1)) k) :
    (extend_instance k inst).singleton_party (dummy_candidate k) =
    {dummy_voter k} := by
  classical
  ext v
  simp only [ABCInstance.singleton_party, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · intro hv
    rcases hv with ⟨hvoters, happ⟩
    rcases Finset.mem_union.1 hvoters with hvoters | hvoters
    · -- embedded voter: approval is a mapped set, cannot equal singleton dummy
      rcases Finset.mem_map.1 hvoters with ⟨v0, hv0, rfl⟩
      have hlt : (embed_voter k v0).val < k := by
        simpa [embed_voter] using v0.isLt
      have happ' :
          (inst.approves v0).map ⟨embed_candidate k, embed_candidate_injective k⟩ =
            {dummy_candidate k} := by
        simpa [extend_instance, hlt] using happ
      -- dummy_candidate not in the image of embed_candidate
      have hmem :
          dummy_candidate k ∈ (inst.approves v0).map ⟨embed_candidate k, embed_candidate_injective k⟩ := by
        -- avoid simp rewriting `mem_map` to an existential
        rw [happ']
        simp
      rcases Finset.mem_map.1 hmem with ⟨c, _, hc⟩
      -- contradiction
      exfalso
      exact dummy_not_embedded k c hc
    · -- dummy voter
      have : v = dummy_voter k := by simpa using hvoters
      exact this
  · intro hv
    subst hv
    refine ⟨?_, ?_⟩
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · have : ¬(k < k) := Nat.lt_irrefl k
      simp [extend_instance, dummy_voter, this]

lemma dummy_supporters (k : ℕ) (inst : ABCInstance (Fin k) (Fin (k + 1)) k) :
    (extend_instance k inst).supporters (dummy_candidate k) = {dummy_voter k} := by
  classical
  ext v
  simp only [ABCInstance.supporters, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · intro hv
    rcases hv with ⟨hvoters, happ⟩
    by_cases hlt : v.val < k
    · -- embedded voter: dummy candidate not approved
      have : dummy_candidate k ∉ (extend_instance k inst).approves v := by
        simp [extend_instance, hlt, dummy_not_embedded]
      exact (False.elim ((this happ)))
    · -- the only voter in the voter set with `val ≥ k` is the dummy voter
      have : v = dummy_voter k := by
        -- if v ∈ voters and not val<k, it must be the inserted dummy
        rcases Finset.mem_union.1 hvoters with hvoters | hvoters
        · exfalso
          rcases Finset.mem_map.1 hvoters with ⟨v0, _, hvEq⟩
          have : (embed_voter k v0).val < k := by simpa [embed_voter] using v0.isLt
          exact hlt (hvEq ▸ this)
        · simpa using hvoters
      simpa [this]
  · intro hv
    rw [hv]
    have : ¬(k < k) := Nat.lt_irrefl k
    refine ⟨?_, ?_⟩
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · simp [extend_instance, dummy_voter, this]

lemma dummy_exclusive_singleton (k : ℕ) (inst : ABCInstance (Fin k) (Fin (k + 1)) k) :
    is_exclusive_singleton (extend_instance k inst) (dummy_candidate k) := by
  refine ⟨?_, ?_⟩
  · -- singleton party nonempty
    rw [dummy_singleton_party (k := k) inst]
    exact Finset.singleton_nonempty _
  · -- supporters = singleton_party
    rw [dummy_supporters (k := k) inst, dummy_singleton_party (k := k) inst]

-- ============================================================================
-- COMMITTEE PROJECTION (DROP DUMMY CANDIDATE)
-- ============================================================================

/--
Project a committee in `Fin (k+2)` to one in `Fin (k+1)` by dropping the last element.
-/
def project_committee (k : ℕ) (W : Finset (Fin (k + 2))) : Finset (Fin (k + 1)) :=
  W.filterMap (fun c =>
    if h : c.val < k + 1 then some ⟨c.val, h⟩ else none) (by
      intro c1 c2 b hb1 hb2
      have hb1' :
          (if h : c1.val < k + 1 then some ⟨c1.val, h⟩ else none) = some b := by
        simpa [Option.mem_def] using hb1
      have hb2' :
          (if h : c2.val < k + 1 then some ⟨c2.val, h⟩ else none) = some b := by
        simpa [Option.mem_def] using hb2
      by_cases h1 : c1.val < k + 1
      · have hb1'' : (⟨c1.val, h1⟩ : Fin (k + 1)) = b := by
          simpa [h1] using hb1'
        by_cases h2 : c2.val < k + 1
        · have hb2'' : (⟨c2.val, h2⟩ : Fin (k + 1)) = b := by
            simpa [h2] using hb2'
          have : c1.val = c2.val := by
            have := congrArg Fin.val (hb1''.trans hb2''.symm)
            simpa using this
          exact Fin.ext this
        · have : (none : Option (Fin (k + 1))) = some b := by
            simpa [h2] using hb2'
          cases this
      · have : (none : Option (Fin (k + 1))) = some b := by
          simpa [h1] using hb1'
        cases this)

lemma mem_project_committee_iff (k : ℕ) (W : Finset (Fin (k + 2))) (c : Fin (k + 1)) :
    c ∈ project_committee k W ↔ embed_candidate k c ∈ W := by
  classical
  constructor
  · intro hc
    rcases (by
        simpa [project_committee] using hc) with ⟨c', hc'W, hc'⟩
    by_cases hlt : c'.val < k + 1
    · have hc'' : (⟨c'.val, hlt⟩ : Fin (k + 1)) = c := by
        simpa [hlt] using hc'
      have hval : c'.val = c.val := by
        have := congrArg Fin.val hc''
        simpa using this
      have : c' = embed_candidate k c := by
        apply Fin.ext
        simpa [embed_candidate, hval]
      simpa [this] using hc'W
    · simp [hlt] at hc'
  · intro hcW
    have hlt : (embed_candidate k c).val < k + 1 := by
      simpa [embed_candidate] using c.isLt
    have hEq : (⟨(embed_candidate k c).val, hlt⟩ : Fin (k + 1)) = c := by
      apply Fin.ext
      simp [embed_candidate]
    have hex :
        ∃ a ∈ W,
          (if h : a.val < k + 1 then some ⟨a.val, h⟩ else none) = some c := by
      refine ⟨embed_candidate k c, hcW, ?_⟩
      simp [hlt, hEq]
    simpa [project_committee] using hex

lemma map_project_committee_eq_of_not_dummy (k : ℕ) (W : Finset (Fin (k + 2)))
    (hdummy : dummy_candidate k ∉ W) :
    (project_committee k W).map ⟨embed_candidate k, embed_candidate_injective k⟩ = W := by
  classical
  let emb : Fin (k + 1) ↪ Fin (k + 2) := ⟨embed_candidate k, embed_candidate_injective k⟩
  ext x
  constructor
  · intro hx
    rcases Finset.mem_map.1 hx with ⟨c, hc, rfl⟩
    exact (mem_project_committee_iff (k := k) (W := W) (c := c)).1 hc
  · intro hxW
    have hxne : x ≠ dummy_candidate k := by
      intro hxEq
      exact hdummy (hxEq ▸ hxW)
    have hxval_ne : x.val ≠ k + 1 := by
      intro hxval
      apply hxne
      apply Fin.ext
      simpa [dummy_candidate, hxval]
    have hxval_le : x.val ≤ k + 1 := Nat.le_of_lt_succ x.isLt
    have hxlt : x.val < k + 1 := Nat.lt_of_le_of_ne hxval_le hxval_ne
    let c : Fin (k + 1) := ⟨x.val, hxlt⟩
    have hxc : emb c = x := by
      apply Fin.ext
      rfl
    have hcW : emb c ∈ W := by simpa [hxc] using hxW
    have hcproj : c ∈ project_committee k W :=
      (mem_project_committee_iff (k := k) (W := W) (c := c)).2 hcW
    exact Finset.mem_map.2 ⟨c, hcproj, hxc⟩

lemma map_project_committee_eq_erase_dummy (k : ℕ) (W : Finset (Fin (k + 2))) :
    (project_committee k W).map ⟨embed_candidate k, embed_candidate_injective k⟩ =
      W.erase (dummy_candidate k) := by
  classical
  let emb : Fin (k + 1) ↪ Fin (k + 2) := ⟨embed_candidate k, embed_candidate_injective k⟩
  ext x
  constructor
  · intro hx
    rcases Finset.mem_map.1 hx with ⟨c, hc, rfl⟩
    have hcW : embed_candidate k c ∈ W :=
      (mem_project_committee_iff (k := k) (W := W) (c := c)).1 hc
    refine Finset.mem_erase.2 ?_
    exact ⟨dummy_not_embedded k c, hcW⟩
  · intro hx
    rcases Finset.mem_erase.1 hx with ⟨hxne, hxW⟩
    have hxval_ne : x.val ≠ k + 1 := by
      intro hxval
      apply hxne
      apply Fin.ext
      simpa [dummy_candidate, hxval]
    have hxval_le : x.val ≤ k + 1 := Nat.le_of_lt_succ x.isLt
    have hxlt : x.val < k + 1 := Nat.lt_of_le_of_ne hxval_le hxval_ne
    let c : Fin (k + 1) := ⟨x.val, hxlt⟩
    have hxc : emb c = x := by
      apply Fin.ext
      rfl
    have hcW : emb c ∈ W := by simpa [hxc] using hxW
    have hcproj : c ∈ project_committee k W :=
      (mem_project_committee_iff (k := k) (W := W) (c := c)).2 hcW
    exact Finset.mem_map.2 ⟨c, hcproj, hxc⟩

lemma plentiful_extend_instance (k : ℕ) (inst : ABCInstance (Fin k) (Fin (k + 1)) k) :
    inst.plentiful → (extend_instance k inst).plentiful := by
  classical
  intro hpl
  -- The embedded approved candidates plus the dummy candidate are all approved in the extension.
  let emb : Fin (k + 1) ↪ Fin (k + 2) := ⟨embed_candidate k, embed_candidate_injective k⟩
  have hsubset :
      inst.approvedCandidates.map emb ∪ {dummy_candidate k} ⊆
        (extend_instance k inst).approvedCandidates := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · rcases Finset.mem_map.1 hx with ⟨c, hc, rfl⟩
      rcases (by
          simpa [ABCInstance.approvedCandidates] using hc) with ⟨v, hv, hcv⟩
      -- embedded voter approves the embedded candidate
      have hv' : embed_voter k v ∈ (extend_instance k inst).voters :=
        Finset.mem_union_left _ (Finset.mem_map.2 ⟨v, hv, rfl⟩)
      have hmem :
          emb c ∈ (extend_instance k inst).approves (embed_voter k v) := by
        have hlt : (embed_voter k v).val < k := by
          simpa [embed_voter] using v.isLt
        have hvEq : (⟨(embed_voter k v).val, hlt⟩ : Fin k) = v := by
          apply Fin.ext
          simp [embed_voter]
        simpa [extend_instance, hlt, emb, hvEq] using hcv
      have : emb c ∈ (extend_instance k inst).voters.biUnion (extend_instance k inst).approves :=
        Finset.mem_biUnion.2 ⟨embed_voter k v, hv', hmem⟩
      simpa [ABCInstance.approvedCandidates] using this
    · have hx' : x = dummy_candidate k := by
        simpa using (Finset.mem_singleton.1 hx)
      subst hx'
      -- dummy voter approves dummy candidate
      have hv' : dummy_voter k ∈ (extend_instance k inst).voters :=
        Finset.mem_union_right _ (Finset.mem_singleton_self _)
      have hmem : dummy_candidate k ∈ (extend_instance k inst).approves (dummy_voter k) := by
        have : ¬(dummy_voter k).val < k := by simp [dummy_voter]
        simp [extend_instance, dummy_voter, this]
      have : dummy_candidate k ∈
          (extend_instance k inst).voters.biUnion (extend_instance k inst).approves :=
        Finset.mem_biUnion.2 ⟨dummy_voter k, hv', hmem⟩
      simpa [ABCInstance.approvedCandidates] using this
  have hcard_le :
      inst.approvedCandidates.card + 1 ≤ (extend_instance k inst).approvedCandidates.card := by
    -- use subset + card computation on `map ∪ {dummy}`
    have hcard_map : (inst.approvedCandidates.map emb).card = inst.approvedCandidates.card := by
      simpa using (Finset.card_map (s := inst.approvedCandidates) emb)
    have hdummy : dummy_candidate k ∉ inst.approvedCandidates.map emb := by
      intro hx
      rcases Finset.mem_map.1 hx with ⟨c, _, hEq⟩
      exact dummy_not_embedded k c (by simpa [emb] using hEq)
    have hdisj : Disjoint (inst.approvedCandidates.map emb) {dummy_candidate k} :=
      Finset.disjoint_singleton_right.2 hdummy
    have hcard_union :
        (inst.approvedCandidates.map emb ∪ {dummy_candidate k}).card =
          (inst.approvedCandidates.map emb).card + 1 := by
      simpa [Finset.card_singleton] using Finset.card_union_of_disjoint hdisj
    have hcard_subset :
        (inst.approvedCandidates.map emb ∪ {dummy_candidate k}).card ≤
          (extend_instance k inst).approvedCandidates.card :=
      Finset.card_le_card hsubset
    -- combine
    have hcard_eq :
        inst.approvedCandidates.card + 1 =
          (inst.approvedCandidates.map emb ∪ {dummy_candidate k}).card := by
      calc
        inst.approvedCandidates.card + 1
            = (inst.approvedCandidates.map emb).card + 1 := by simpa [hcard_map]
        _ = (inst.approvedCandidates.map emb ∪ {dummy_candidate k}).card := by
            simpa using hcard_union.symm
    have : inst.approvedCandidates.card + 1 ≤ (inst.approvedCandidates.map emb ∪ {dummy_candidate k}).card := by
      simpa [hcard_eq] using (Nat.le_refl (inst.approvedCandidates.card + 1))
    exact le_trans this hcard_subset
  -- conclude `k+1 ≤ ...` from `k ≤ ...` for the original instance
  have : k + 1 ≤ (extend_instance k inst).approvedCandidates.card := by
    have : k ≤ inst.approvedCandidates.card := hpl
    exact le_trans (Nat.add_le_add_right this 1) hcard_le
  simpa [ABCInstance.plentiful] using this

-- ============================================================================
-- INDUCED RULE
-- ============================================================================

/--
Given a rule f for k+1 voters and k+2 candidates (size k+1),
induce a rule for k voters and k+1 candidates (size k).

The induced rule:
1. Extends the instance by adding dummy voter/candidate
2. Applies f (which always includes dummy candidate by singleton approvers lemma)
3. Removes the dummy candidate from the result
-/
noncomputable def induced_rule (k : ℕ)
    (f : ABCRule (Fin (k + 1)) (Fin (k + 2)) (k + 1))
    (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality)
    (hsp : Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f) :
    ABCRule (Fin k) (Fin (k + 1)) k := by
  classical
  let g : ResoluteABCRule (Fin k) (Fin (k + 1)) k :=
    fun inst =>
      project_committee k (f.resolute_committee (extend_instance k inst) hres)
  refine g.toABCRule ?_
  intro inst inst' hv hc ha
  have hcomm :
      f.resolute_committee (extend_instance k inst) hres =
        f.resolute_committee (extend_instance k inst') hres := by
    apply ABCRule.resolute_ballot_ext (f := f)
      (inst := extend_instance k inst) (inst' := extend_instance k inst') (hres := hres)
    · simp [extend_instance, hv]
    · simp [extend_instance, hc]
    · intro v hvv
      rcases Finset.mem_union.1 hvv with hvv | hvv
      · rcases Finset.mem_map.1 hvv with ⟨v0, hv0, rfl⟩
        have hlt : (embed_voter k v0).val < k := by
          simpa [embed_voter] using v0.isLt
        have ha0 : inst.approves v0 = inst'.approves v0 := ha v0 hv0
        have hvEq : (⟨(embed_voter k v0).val, hlt⟩ : Fin k) = v0 := by
          apply Fin.ext
          simp [embed_voter]
        simp [extend_instance, hlt, ha0, hvEq]
      · have hvd : v = dummy_voter k := by simpa using hvv
        subst hvd
        have hlt : ¬(dummy_voter k).val < k := by simp [dummy_voter]
        simp [extend_instance, dummy_voter, hlt]
  simp [g, hcomm]

-- ============================================================================
-- MAIN INDUCTION LEMMA
-- ============================================================================

/--
Lemma 7 (Peters): If there exists a rule satisfying the axioms for
committee size k+1 (with k+1 voters and k+2 candidates), then there exists
such a rule for committee size k (with k voters and k+1 candidates).
-/
theorem induction_k (k : ℕ) (hk : 2 ≤ k)
    (f : ABCRule (Fin (k + 1)) (Fin (k + 2)) (k + 1))
    (hwf : f.IsWellFormed)
    (hres : f.IsResolute)
    (heff : f.SatisfiesWeakEfficiency)
    (hprop : f.SatisfiesProportionality)
    (hsp : Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f) :
    ∃ (f' : ABCRule (Fin k) (Fin (k + 1)) k),
      f'.IsResolute ∧
      f'.SatisfiesWeakEfficiency ∧
      f'.SatisfiesProportionality ∧
      Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f' := by
  classical
  let f' : ABCRule (Fin k) (Fin (k + 1)) k := induced_rule k f hres hprop hsp
  refine ⟨f', ?_, ?_, ?_, ?_⟩
  · -- resolute
    intro inst
    simp [f', induced_rule, ResoluteABCRule.toABCRule]
  · -- weak efficiency (on plentiful instances)
    intro inst hpl W hW c hc
    have hW' :
        W = project_committee k (f.resolute_committee (extend_instance k inst) hres) := by
      simpa [f', induced_rule, ResoluteABCRule.toABCRule] using hW
    subst hW'
    have hpl_ext : (extend_instance k inst).plentiful :=
      plentiful_extend_instance (k := k) inst hpl
    have hc_ext :
        embed_candidate k c ∈ f.resolute_committee (extend_instance k inst) hres :=
      (mem_project_committee_iff (k := k)
        (W := f.resolute_committee (extend_instance k inst) hres) (c := c)).1 hc
    intro hunapp
    have hunapp_ext : (extend_instance k inst).is_unapproved (embed_candidate k c) := by
      intro v hvv
      rcases Finset.mem_union.1 hvv with hvv | hvv
      · rcases Finset.mem_map.1 hvv with ⟨v0, hv0, rfl⟩
        have hun0 : c ∉ inst.approves v0 := hunapp v0 hv0
        intro hmem
        have hlt : (embed_voter k v0).val < k := by
          simpa [embed_voter] using v0.isLt
        have hvEq : (⟨(embed_voter k v0).val, hlt⟩ : Fin k) = v0 := by
          apply Fin.ext
          simp [embed_voter]
        have hmem' : embed_candidate k c ∈ (inst.approves v0).map
            ⟨embed_candidate k, embed_candidate_injective k⟩ := by
          simpa [extend_instance, hlt, hvEq] using hmem
        rcases Finset.mem_map.1 hmem' with ⟨c0, hc0, hEq⟩
        have : c0 = c := by
          apply embed_candidate_injective k
          simpa using hEq
        subst this
        exact hun0 hc0
      · have hvd : v = dummy_voter k := by simpa using hvv
        subst hvd
        have : ¬(dummy_voter k).val < k := by simp [dummy_voter]
        simp [extend_instance, this, dummy_not_embedded]
    exact (heff (extend_instance k inst) hpl_ext
      (f.resolute_committee (extend_instance k inst) hres)
      (f.resolute_committee_mem (extend_instance k inst) hres)
      (embed_candidate k c) hc_ext) hunapp_ext
  · -- proportionality
    intro inst cand hpl hcand hquota W hW
    have hW' :
        W = project_committee k (f.resolute_committee (extend_instance k inst) hres) := by
      simpa [f', induced_rule, ResoluteABCRule.toABCRule] using hW
    subst hW'
    -- party-list is preserved by the extension (dummy party is disjoint)
    have hpl_ext : (extend_instance k inst).is_party_list := by
      classical
      let embC : Fin (k + 1) ↪ Fin (k + 2) := ⟨embed_candidate k, embed_candidate_injective k⟩
      intro v₁ hv₁ v₂ hv₂
      -- cases on whether v₁/v₂ are dummy or embedded
      rcases Finset.mem_union.1 hv₁ with hv₁ | hv₁ <;>
      rcases Finset.mem_union.1 hv₂ with hv₂ | hv₂
      · -- both embedded
        rcases Finset.mem_map.1 hv₁ with ⟨a1, ha1, rfl⟩
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
            (extend_instance k inst).approves (embed_voter k a1) = (inst.approves a1).map embC := by
          simpa [extend_instance, hlt1, hvEq1, embC]
        have happ2 :
            (extend_instance k inst).approves (embed_voter k a2) = (inst.approves a2).map embC := by
          simpa [extend_instance, hlt2, hvEq2, embC]
        rcases hpl a1 ha1 a2 ha2 with ha | ha
        · left
          simpa [happ1, happ2, ha]
        · right
          have : Disjoint ((inst.approves a1).map embC) ((inst.approves a2).map embC) :=
            (Finset.disjoint_map (s := inst.approves a1) (t := inst.approves a2) embC).2 ha
          simpa [happ1, happ2] using this
      · -- v₁ embedded, v₂ dummy
        rcases Finset.mem_map.1 hv₁ with ⟨a1, ha1, rfl⟩
        right
        have hvd : v₂ = dummy_voter k := by simpa using hv₂
        subst hvd
        have hlt1 : (embed_voter k a1).val < k := by simpa [embed_voter] using a1.isLt
        have hvEq1 : (⟨(embed_voter k a1).val, hlt1⟩ : Fin k) = a1 := by
          apply Fin.ext
          simp [embed_voter]
        have happ1 :
            (extend_instance k inst).approves (embed_voter k a1) = (inst.approves a1).map embC := by
          simpa [extend_instance, hlt1, hvEq1, embC]
        have happD :
            (extend_instance k inst).approves (dummy_voter k) = {dummy_candidate k} := by
          have hltD : ¬(dummy_voter k).val < k := by simp [dummy_voter]
          simp [extend_instance, dummy_voter, hltD]
        have hdummy : dummy_candidate k ∉ (inst.approves a1).map embC := by
          intro hx
          rcases Finset.mem_map.1 hx with ⟨c0, _, hEq⟩
          exact dummy_not_embedded k c0 (by simpa using hEq)
        -- disjointness with singleton
        simpa [happ1, happD] using (Finset.disjoint_singleton_right.2 hdummy)
      · -- v₁ dummy, v₂ embedded
        rcases Finset.mem_map.1 hv₂ with ⟨a2, ha2, rfl⟩
        right
        have hvd : v₁ = dummy_voter k := by simpa using hv₁
        subst hvd
        have hlt2 : (embed_voter k a2).val < k := by simpa [embed_voter] using a2.isLt
        have hvEq2 : (⟨(embed_voter k a2).val, hlt2⟩ : Fin k) = a2 := by
          apply Fin.ext
          simp [embed_voter]
        have happ2 :
            (extend_instance k inst).approves (embed_voter k a2) = (inst.approves a2).map embC := by
          simpa [extend_instance, hlt2, hvEq2, embC]
        have happD :
            (extend_instance k inst).approves (dummy_voter k) = {dummy_candidate k} := by
          have hltD : ¬(dummy_voter k).val < k := by simp [dummy_voter]
          simp [extend_instance, dummy_voter, hltD]
        have hdummy : dummy_candidate k ∉ (inst.approves a2).map embC := by
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
          have hltD : ¬(dummy_voter k).val < k := by simp [dummy_voter]
          simp [extend_instance, dummy_voter, hltD]
        simpa [happD]
    -- candidate lifts to extended candidates
    have hcand_ext :
        embed_candidate k cand ∈ (extend_instance k inst).candidates := by
      have : embed_candidate k cand ∈ inst.candidates.map ⟨embed_candidate k, embed_candidate_injective k⟩ :=
        Finset.mem_map.2 ⟨cand, hcand, rfl⟩
      exact Finset.mem_union_left _ this
    -- quota lifts: if a*k ≥ n then a*(k+1) ≥ n+1 (since a>0)
    have hquota_ext :
        (extend_instance k inst).singleton_party_size (embed_candidate k cand) * (k + 1) ≥
          (extend_instance k inst).voters.card := by
      classical
      let embV : Fin k ↪ Fin (k + 1) := ⟨embed_voter k, embed_voter_injective k⟩
      let embC : Fin (k + 1) ↪ Fin (k + 2) := ⟨embed_candidate k, embed_candidate_injective k⟩

      have hd : dummy_voter k ∉ inst.voters.map embV := by
        intro hx
        rcases Finset.mem_map.1 hx with ⟨v0, _, hEq⟩
        have : (embed_voter k v0).val = k := by
          simpa [dummy_voter] using congrArg Fin.val hEq
        have : v0.val = k := by simpa [embed_voter] using this
        exact (Nat.ne_of_lt v0.isLt) this

      have hvoters_card :
          (extend_instance k inst).voters.card = inst.voters.card + 1 := by
        have hdisj : Disjoint (inst.voters.map embV) {dummy_voter k} :=
          Finset.disjoint_singleton_right.2 hd
        calc
          (extend_instance k inst).voters.card
              = (inst.voters.map embV ∪ {dummy_voter k}).card := by rfl
          _ = (inst.voters.map embV).card + 1 := by
              simpa [Finset.card_singleton] using Finset.card_union_of_disjoint hdisj
          _ = inst.voters.card + 1 := by
              simpa using congrArg (fun t => t + 1) (Finset.card_map (s := inst.voters) embV)

      have hsingle_party :
          (extend_instance k inst).singleton_party (embed_candidate k cand) =
            (inst.singleton_party cand).map embV := by
        ext v
        constructor
        · intro hv
          have hvv : v ∈ (extend_instance k inst).voters := (Finset.mem_filter.1 hv).1
          have hvapp : (extend_instance k inst).approves v = {embed_candidate k cand} :=
            (Finset.mem_filter.1 hv).2
          rcases Finset.mem_union.1 hvv with hvv | hvv
          · rcases Finset.mem_map.1 hvv with ⟨v0, hv0, rfl⟩
            have hlt : (embed_voter k v0).val < k := by
              simpa [embed_voter] using v0.isLt
            have hvEq : (⟨(embed_voter k v0).val, hlt⟩ : Fin k) = v0 := by
              apply Fin.ext
              simp [embed_voter]
            have hmap :
                (inst.approves v0).map embC = {embed_candidate k cand} := by
              -- rewrite `hvapp` using the definition of `extend_instance`
              simpa [extend_instance, hlt, embC, hvEq] using hvapp
            have happ_eq : inst.approves v0 = {cand} := by
              ext y
              constructor
              · intro hy
                have hy' : embC y ∈ (inst.approves v0).map embC :=
                  Finset.mem_map.2 ⟨y, hy, rfl⟩
                have hy'' : embC y ∈ ({embed_candidate k cand} : Finset (Fin (k + 2))) := by
                  simpa [hmap] using hy'
                have hyEq : embC y = embC cand := by
                  have hyEq' : embC y = embed_candidate k cand := by
                    simpa using (Finset.mem_singleton.1 hy'')
                  simpa [embC] using hyEq'
                have : y = cand := embC.injective hyEq
                simpa [this]
              · intro hy
                have hyEq : y = cand := by
                  simpa using (Finset.mem_singleton.1 hy)
                subst y
                have : embed_candidate k cand ∈ (inst.approves v0).map embC := by
                  simpa [hmap] using (Finset.mem_singleton_self (embed_candidate k cand))
                rcases Finset.mem_map.1 this with ⟨c0, hc0, hcEq⟩
                have : c0 = cand := embC.injective (by simpa [embC] using hcEq)
                subst this
                simpa using hc0
            have : v0 ∈ inst.singleton_party cand := by
              simp [ABCInstance.singleton_party, hv0, happ_eq]
            exact Finset.mem_map.2 ⟨v0, this, rfl⟩
          · have hvd : v = dummy_voter k := by simpa using hvv
            subst hvd
            have hcontra :
                (extend_instance k inst).approves (dummy_voter k) ≠ {embed_candidate k cand} := by
              have hlt : ¬(dummy_voter k).val < k := by simp [dummy_voter]
              have happD :
                  (extend_instance k inst).approves (dummy_voter k) = {dummy_candidate k} := by
                simp [extend_instance, dummy_voter, hlt]
              intro hEq
              have hset : ({dummy_candidate k} : Finset (Fin (k + 2))) = {embed_candidate k cand} := by
                simpa [happD] using hEq
              have hmem : dummy_candidate k ∈ ({embed_candidate k cand} : Finset (Fin (k + 2))) := by
                have : dummy_candidate k ∈ ({dummy_candidate k} : Finset (Fin (k + 2))) := by simp
                simpa [hset] using this
              have hdc : dummy_candidate k = embed_candidate k cand := by
                simpa using (Finset.mem_singleton.1 hmem)
              exact dummy_not_embedded k cand (by simpa using hdc.symm)
            exact (hcontra hvapp).elim
        · intro hv
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
            simpa [extend_instance, hlt, embC, hvEq, hvapp0] using
              (Finset.map_singleton embC cand)
          exact Finset.mem_filter.2 ⟨hvv, hvapp⟩

      have hsingle :
          (extend_instance k inst).singleton_party_size (embed_candidate k cand) =
            inst.singleton_party_size cand := by
        calc
          (extend_instance k inst).singleton_party_size (embed_candidate k cand)
              = ((extend_instance k inst).singleton_party (embed_candidate k cand)).card := by rfl
          _ = ((inst.singleton_party cand).map embV).card := by simpa [hsingle_party]
          _ = (inst.singleton_party cand).card := by
              simpa using (Finset.card_map (s := inst.singleton_party cand) embV)
          _ = inst.singleton_party_size cand := by rfl

      have ha_pos : 1 ≤ inst.singleton_party_size cand := by
        have hnpos : 0 < inst.voters.card := Finset.card_pos.mpr inst.voters_nonempty
        have : inst.singleton_party_size cand ≠ 0 := by
          intro h0
          have : inst.voters.card = 0 := by
            apply Nat.eq_zero_of_le_zero
            simpa [h0] using hquota
          exact (Nat.ne_of_gt hnpos) this
        exact Nat.succ_le_iff.2 (Nat.pos_of_ne_zero this)

      have hquota' : inst.singleton_party_size cand * (k + 1) ≥ inst.voters.card + 1 := by
        -- `a*(k+1) = a*k + a`
        have : inst.singleton_party_size cand * (k + 1) =
            inst.singleton_party_size cand * k + inst.singleton_party_size cand := by
          simpa [Nat.mul_succ]
        rw [this]
        exact add_le_add hquota ha_pos

      simpa [hvoters_card, hsingle] using hquota'
    have hc_ext :
        embed_candidate k cand ∈ f.resolute_committee (extend_instance k inst) hres :=
      ABCRule.resolute_proportionality (f := f) (hres := hres) (hprop := hprop)
        (inst := extend_instance k inst) (c := embed_candidate k cand)
        hpl_ext hcand_ext hquota_ext
    exact (mem_project_committee_iff (k := k)
      (W := f.resolute_committee (extend_instance k inst) hres) (c := cand)).2 hc_ext
  · -- strategyproofness on plentiful instances
    intro inst inst' i hpl hpl' hi hvar hsub hres'
    intro hgain
    -- lift to extended instances and contradict `hsp`
    let embV : Fin k ↪ Fin (k + 1) := ⟨embed_voter k, embed_voter_injective k⟩
    let embC : Fin (k + 1) ↪ Fin (k + 2) := ⟨embed_candidate k, embed_candidate_injective k⟩
    let extInst := extend_instance k inst
    let extInst' := extend_instance k inst'
    have hpl_ext : extInst.plentiful := plentiful_extend_instance (k := k) inst hpl
    have hpl'_ext : extInst'.plentiful := plentiful_extend_instance (k := k) inst' hpl'
    have hi_ext : embV i ∈ extInst.voters :=
      Finset.mem_union_left _ (Finset.mem_map.2 ⟨i, hi, rfl⟩)
    have hvar_ext : extInst.is_i_variant extInst' (embV i) := by
      rcases hvar with ⟨hv, hc, ha⟩
      refine ⟨?_, ?_, ?_⟩
      · simp [extInst, extInst', extend_instance, hv]
      · simp [extInst, extInst', extend_instance, hc]
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
          simp [extInst, extInst', extend_instance, hlt, ha0, embC, hvEq]
        · have hvd : v = dummy_voter k := by simpa using hvv
          subst hvd
          simp [extInst, extInst', extend_instance, dummy_voter]
    have hsub_ext :
        extInst'.approves (embV i) ⊂ extInst.approves (embV i) := by
      have hlt : (embV i).val < k := by simpa [embV, embed_voter] using i.isLt
      have hvEq : (⟨(embV i).val, hlt⟩ : Fin k) = i := by
        apply Fin.ext
        simp [embV, embed_voter]
      have happ : extInst.approves (embV i) = (inst.approves i).map embC := by
        simpa [extInst, extend_instance, hlt, embC, hvEq]
      have happ' : extInst'.approves (embV i) = (inst'.approves i).map embC := by
        simpa [extInst', extend_instance, hlt, embC, hvEq]
      simpa [happ, happ'] using (Finset.map_ssubset_map (f := embC)).2 hsub

    have hcomm_inst :
        f'.resolute_committee inst hres' =
          project_committee k (f.resolute_committee extInst hres) := by
      have hmem :
          project_committee k (f.resolute_committee extInst hres) ∈ f' inst := by
        simp [f', induced_rule, ResoluteABCRule.toABCRule, extInst]
      exact ((ABCRule.mem_resolute_iff (f := f') (inst := inst) (hres := hres')
        (W := project_committee k (f.resolute_committee extInst hres))).1 hmem).symm
    have hcomm_inst' :
        f'.resolute_committee inst' hres' =
          project_committee k (f.resolute_committee extInst' hres) := by
      have hmem :
          project_committee k (f.resolute_committee extInst' hres) ∈ f' inst' := by
        simp [f', induced_rule, ResoluteABCRule.toABCRule, extInst']
      exact ((ABCRule.mem_resolute_iff (f := f') (inst := inst') (hres := hres')
        (W := project_committee k (f.resolute_committee extInst' hres))).1 hmem).symm

    have hgain_ss :
        (f'.resolute_committee inst hres' ∩ inst.approves i) ⊂
          (f'.resolute_committee inst' hres' ∩ inst.approves i) := by
      simpa using hgain
    have hgain_map :
        ((f'.resolute_committee inst hres' ∩ inst.approves i).map embC) ⊂
          ((f'.resolute_committee inst' hres' ∩ inst.approves i).map embC) :=
      (Finset.map_ssubset_map (f := embC)).2 hgain_ss

    have hdummy_not :
        dummy_candidate k ∉ (inst.approves i).map embC := by
      intro hx
      rcases Finset.mem_map.1 hx with ⟨c0, _, hEq⟩
      exact dummy_not_embedded k c0 (by simpa [embC] using hEq)

    have happ :
        extInst.approves (embV i) = (inst.approves i).map embC := by
      have hlt : (embV i).val < k := by simpa [embV, embed_voter] using i.isLt
      have hvEq : (⟨(embV i).val, hlt⟩ : Fin k) = i := by
        apply Fin.ext
        simp [embV, embed_voter]
      simpa [extInst, extend_instance, hlt, embC, hvEq]

    have hgain_core :
        (f.resolute_committee extInst hres ∩ extInst.approves (embV i)) ⊂
          (f.resolute_committee extInst' hres ∩ extInst.approves (embV i)) := by
      have hgain_map' :
          (project_committee k (f.resolute_committee extInst hres) ∩ inst.approves i).map embC ⊂
            (project_committee k (f.resolute_committee extInst' hres) ∩ inst.approves i).map embC := by
        simpa [hcomm_inst, hcomm_inst'] using hgain_map
      have hgain_erase :
          ((f.resolute_committee extInst hres).erase (dummy_candidate k) ∩ (inst.approves i).map embC) ⊂
            ((f.resolute_committee extInst' hres).erase (dummy_candidate k) ∩ (inst.approves i).map embC) := by
        simpa [Finset.map_inter, embC,
          map_project_committee_eq_erase_dummy (k := k) (W := f.resolute_committee extInst hres),
          map_project_committee_eq_erase_dummy (k := k) (W := f.resolute_committee extInst' hres)]
          using hgain_map'
      -- remove the dummy erase inside the intersections (dummy not approved by i)
      have hleft :
          (f.resolute_committee extInst hres).erase (dummy_candidate k) ∩ (inst.approves i).map embC =
            f.resolute_committee extInst hres ∩ (inst.approves i).map embC := by
        calc
          (f.resolute_committee extInst hres).erase (dummy_candidate k) ∩ (inst.approves i).map embC
              = (f.resolute_committee extInst hres ∩ (inst.approves i).map embC).erase (dummy_candidate k) := by
                  simpa [Finset.erase_inter]
          _ = f.resolute_committee extInst hres ∩ (inst.approves i).map embC := by
              apply Finset.erase_eq_of_notMem
              intro hx
              exact hdummy_not ((Finset.mem_inter.mp hx).2)
      have hright :
          (f.resolute_committee extInst' hres).erase (dummy_candidate k) ∩ (inst.approves i).map embC =
            f.resolute_committee extInst' hres ∩ (inst.approves i).map embC := by
        calc
          (f.resolute_committee extInst' hres).erase (dummy_candidate k) ∩ (inst.approves i).map embC
              = (f.resolute_committee extInst' hres ∩ (inst.approves i).map embC).erase (dummy_candidate k) := by
                  simpa [Finset.erase_inter]
          _ = f.resolute_committee extInst' hres ∩ (inst.approves i).map embC := by
              apply Finset.erase_eq_of_notMem
              intro hx
              exact hdummy_not ((Finset.mem_inter.mp hx).2)
      -- finish
      have hgain_core' :
          (f.resolute_committee extInst hres ∩ (inst.approves i).map embC) ⊂
            (f.resolute_committee extInst' hres ∩ (inst.approves i).map embC) := by
        simpa [hleft, hright] using hgain_erase
      simpa [happ] using hgain_core'

    have hgain_f :
        (f.resolute_committee extInst' hres ∩ extInst.approves (embV i)) ⊃
          (f.resolute_committee extInst hres ∩ extInst.approves (embV i)) := by
      simpa using hgain_core

    exact hsp extInst extInst' (embV i) hpl_ext hpl'_ext hi_ext hvar_ext hsub_ext hres hgain_f

end Peters.InductionK
