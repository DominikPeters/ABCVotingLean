import ABCVoting.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.Peters.RestrictToPlentiful

open Finset BigOperators ABCInstance

/-!
# Induction on Number of Candidates (Lemma 6 from Peters)

This file proves that if there exists a rule satisfying the axioms for m+1 candidates,
then there also exists such a rule for m candidates.

The construction adds a "dummy" candidate that no voter approves. By weak efficiency,
this dummy candidate is never elected, so we can restrict the output to the original
m candidates.
-/

namespace Peters.InductionM

variable {V : Type*} [DecidableEq V] {k : ℕ}

-- ============================================================================
-- CANDIDATE EMBEDDING
-- ============================================================================

/--
Embed a Fin m into Fin (m+1) as the first m elements.
-/
def embed_candidate (m : ℕ) : Fin m → Fin (m + 1) :=
  fun c => ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩

/--
The embedding is injective.
-/
lemma embed_candidate_injective (m : ℕ) : Function.Injective (embed_candidate m) := by
  intro c1 c2 h
  simp only [embed_candidate, Fin.mk.injEq] at h
  exact Fin.ext h

/--
The dummy candidate is the last one (index m).
-/
def dummy_candidate (m : ℕ) : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩

/--
The dummy candidate is not in the image of the embedding.
-/
lemma dummy_not_embedded (m : ℕ) (c : Fin m) :
    embed_candidate m c ≠ dummy_candidate m := by
  simp only [embed_candidate, dummy_candidate, Fin.mk.injEq, ne_eq]
  exact Nat.ne_of_lt c.isLt

-- ============================================================================
-- INSTANCE EXTENSION
-- ============================================================================

/--
Given an instance with m candidates, create an instance with m+1 candidates
by adding a dummy candidate that no voter approves.
-/
def extend_candidates (m : ℕ) (inst : ABCInstance V (Fin m) k) :
    ABCInstance V (Fin (m + 1)) k where
  voters := inst.voters
  candidates := Finset.univ
  approves := fun v => (inst.approves v).map ⟨embed_candidate m, embed_candidate_injective m⟩
  approves_subset := by
    intro v _
    exact Finset.subset_univ _
  voters_nonempty := inst.voters_nonempty
  k_pos := inst.k_pos
  k_le_m := by
    have h1 : inst.candidates.card ≤ m := by
      simpa using (Finset.card_le_univ inst.candidates)
    have h2 : inst.candidates.card ≤ m + 1 := le_trans h1 (Nat.le_succ m)
    have : k ≤ m + 1 := le_trans inst.k_le_m h2
    simpa [Finset.card_fin] using this

/--
The dummy candidate is unapproved in the extended instance.
-/
lemma dummy_unapproved (m : ℕ) (inst : ABCInstance V (Fin m) k) :
    (extend_candidates m inst).is_unapproved (dummy_candidate m) := by
  intro v _
  simp only [extend_candidates, Finset.mem_map, Function.Embedding.coeFn_mk]
  intro ⟨c, _, hc⟩
  exact dummy_not_embedded m c hc

-- ============================================================================
-- COMMITTEE RESTRICTION
-- ============================================================================

/--
Project a committee in `Fin (m+1)` to one in `Fin m` by dropping the last element.

This is defined for all committees (even if they contain the dummy).
-/
def project_committee (m : ℕ) (W : Finset (Fin (m + 1))) : Finset (Fin m) :=
  W.filterMap (fun c =>
    if h : c.val < m then some ⟨c.val, h⟩ else none) (by
      intro c1 c2 b hb1 hb2
      have hb1' : (if h : c1.val < m then some ⟨c1.val, h⟩ else none) = some b := by
        simpa [Option.mem_def] using hb1
      have hb2' : (if h : c2.val < m then some ⟨c2.val, h⟩ else none) = some b := by
        simpa [Option.mem_def] using hb2
      by_cases h1 : c1.val < m
      · have hb1'' : (⟨c1.val, h1⟩ : Fin m) = b := by
          simpa [h1] using hb1'
        by_cases h2 : c2.val < m
        · have hb2'' : (⟨c2.val, h2⟩ : Fin m) = b := by
            simpa [h2] using hb2'
          have : c1.val = c2.val := by
            have := congrArg Fin.val (hb1''.trans hb2''.symm)
            simpa using this
          exact Fin.ext this
        · have : (none : Option (Fin m)) = some b := by
            simpa [h2] using hb2'
          cases this
      · have : (none : Option (Fin m)) = some b := by
          simpa [h1] using hb1'
        cases this)

lemma mem_project_committee_iff (m : ℕ) (W : Finset (Fin (m + 1))) (c : Fin m) :
    c ∈ project_committee m W ↔ embed_candidate m c ∈ W := by
  classical
  constructor
  · intro hc
    rcases (by
        simpa [project_committee] using hc) with ⟨c', hc'W, hc'⟩
    by_cases hlt : c'.val < m
    · -- `c'` projects to `c`, hence `c' = embed c`.
      have hc'' : (⟨c'.val, hlt⟩ : Fin m) = c := by
        simpa [hlt] using hc'
      have hval : c'.val = c.val := by
        have := congrArg Fin.val hc''
        simpa using this
      have : c' = embed_candidate m c := by
        apply Fin.ext
        simpa [embed_candidate, hval]
      simpa [this] using hc'W
    · -- Impossible: projection would be `none`.
      simp [hlt] at hc'
  · intro hc
    have hlt : (embed_candidate m c).val < m := by
      simpa [embed_candidate] using c.isLt
    have hEq : (⟨(embed_candidate m c).val, hlt⟩ : Fin m) = c := by
      apply Fin.ext
      simp [embed_candidate]
    have hex :
        ∃ a ∈ W,
          (if h : a.val < m then some ⟨a.val, h⟩ else none) = some c := by
      refine ⟨embed_candidate m c, hc, ?_⟩
      simp [hlt, hEq]
    simpa [project_committee] using hex

lemma is_unapproved_embed_iff (m : ℕ) (inst : ABCInstance V (Fin m) k) (c : Fin m) :
    (extend_candidates m inst).is_unapproved (embed_candidate m c) ↔ inst.is_unapproved c := by
  classical
  constructor
  · intro hun v hv hc
    have : embed_candidate m c ∈ (extend_candidates m inst).approves v :=
      Finset.mem_map.2 ⟨c, hc, rfl⟩
    exact hun v hv this
  · intro hun v hv hc
    rcases Finset.mem_map.1 hc with ⟨c', hc', hEq⟩
    have : c' = c := by
      apply embed_candidate_injective m
      simpa using hEq
    subst this
    exact hun v hv hc'

lemma plentiful_extend_candidates (m : ℕ) (inst : ABCInstance V (Fin m) k) :
    inst.plentiful → (extend_candidates m inst).plentiful := by
  classical
  intro hpl
  -- Show that mapping approved candidates into the extended instance yields a subset
  -- of the extended approved candidates.
  let emb : Fin m ↪ Fin (m + 1) := ⟨embed_candidate m, embed_candidate_injective m⟩
  have hsubset :
      inst.approvedCandidates.map emb ⊆ (extend_candidates m inst).approvedCandidates := by
    intro x hx
    rcases Finset.mem_map.1 hx with ⟨c, hc, rfl⟩
    rcases (by
        simpa [ABCInstance.approvedCandidates] using hc) with ⟨v, hv, hcv⟩
    have hex :
        ∃ a ∈ inst.voters,
          embed_candidate m c ∈ (inst.approves a).map emb := by
      refine ⟨v, hv, ?_⟩
      exact Finset.mem_map.2 ⟨c, hcv, rfl⟩
    simpa [ABCInstance.approvedCandidates, extend_candidates] using hex
  have hmap_le :
      (inst.approvedCandidates.map emb).card ≤ (extend_candidates m inst).approvedCandidates.card :=
    Finset.card_le_card hsubset
  have hcard_map : (inst.approvedCandidates.map emb).card = inst.approvedCandidates.card := by
    simpa using (Finset.card_map (s := inst.approvedCandidates) emb)
  have hinst_le :
      inst.approvedCandidates.card ≤ (extend_candidates m inst).approvedCandidates.card := by
    simpa [hcard_map] using hmap_le
  exact le_trans hpl hinst_le

lemma singleton_party_size_extend_candidates (m : ℕ) (inst : ABCInstance V (Fin m) k)
    (c : Fin m) :
    (extend_candidates m inst).singleton_party_size (embed_candidate m c) =
      inst.singleton_party_size c := by
  classical
  let emb : Fin m ↪ Fin (m + 1) := ⟨embed_candidate m, embed_candidate_injective m⟩
  have hfilter :
      inst.voters.filter (fun v => (inst.approves v).map emb = {emb c}) =
        inst.voters.filter (fun v => inst.approves v = {c}) := by
    ext v
    constructor <;> intro hv
    · have hv' : (inst.approves v).map emb = {emb c} := (Finset.mem_filter.1 hv).2
      have hv'' : (inst.approves v).map emb = (({c} : Finset (Fin m)).map emb) := by
        simpa [Finset.map_singleton] using hv'
      have : inst.approves v = {c} := (Finset.map_inj (f := emb)).1 hv''
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hv).1, this⟩
    · have hv' : inst.approves v = {c} := (Finset.mem_filter.1 hv).2
      have : (inst.approves v).map emb = {emb c} := by
        simpa [hv', Finset.map_singleton]
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hv).1, this⟩
  -- finish by rewriting singleton_party_size to card(filter ...)
  have := congrArg Finset.card hfilter
  simpa [ABCInstance.singleton_party_size, extend_candidates, emb] using this

lemma extend_candidates_party_list (m : ℕ) (inst : ABCInstance V (Fin m) k) :
    inst.is_party_list → (extend_candidates m inst).is_party_list := by
  classical
  intro hpl v₁ hv₁ v₂ hv₂
  have hv₁' : v₁ ∈ inst.voters := by simpa [extend_candidates] using hv₁
  have hv₂' : v₂ ∈ inst.voters := by simpa [extend_candidates] using hv₂
  rcases hpl v₁ hv₁' v₂ hv₂' with hEq | hDisj
  · left
    simp [extend_candidates, hEq]
  · right
    let emb : Fin m ↪ Fin (m + 1) := ⟨embed_candidate m, embed_candidate_injective m⟩
    -- Disjointness is preserved by mapping through an embedding.
    simpa [extend_candidates, emb] using (Finset.disjoint_map (f := emb)).2 hDisj

lemma map_project_committee_eq_of_not_dummy (m : ℕ) (W : Finset (Fin (m + 1)))
    (hdummy : dummy_candidate m ∉ W) :
    (project_committee m W).map ⟨embed_candidate m, embed_candidate_injective m⟩ = W := by
  classical
  let emb : Fin m ↪ Fin (m + 1) := ⟨embed_candidate m, embed_candidate_injective m⟩
  ext x
  constructor
  · intro hx
    rcases Finset.mem_map.1 hx with ⟨c, hc, rfl⟩
    exact (mem_project_committee_iff (m := m) (W := W) (c := c)).1 hc
  · intro hxW
    have hxne : x ≠ dummy_candidate m := by
      intro hxEq
      exact hdummy (hxEq ▸ hxW)
    have hxval_ne : x.val ≠ m := by
      intro hxval
      apply hxne
      apply Fin.ext
      simpa [dummy_candidate, hxval]
    have hxval_le : x.val ≤ m := Nat.le_of_lt_succ x.isLt
    have hxlt : x.val < m := Nat.lt_of_le_of_ne hxval_le hxval_ne
    let c : Fin m := ⟨x.val, hxlt⟩
    have hxc : emb c = x := by
      apply Fin.ext
      rfl
    have hcW : emb c ∈ W := by simpa [hxc] using hxW
    have hcproj : c ∈ project_committee m W :=
      (mem_project_committee_iff (m := m) (W := W) (c := c)).2 hcW
    exact Finset.mem_map.2 ⟨c, hcproj, hxc⟩

-- ============================================================================
-- INDUCED RULE
-- ============================================================================

/--
Given a rule for m+1 candidates, induce a rule for m candidates.
The induced rule extends the instance, applies f, and restricts the output.
-/
noncomputable def induced_rule (m : ℕ) {k : ℕ} (f : ABCRule V (Fin (m + 1)) k)
    (hres : f.IsResolute) :
    ABCRule V (Fin m) k := by
  classical
  let g : ResoluteABCRule V (Fin m) k :=
    fun inst =>
      project_committee m (f.resolute_committee (extend_candidates m inst) hres)
  refine g.toABCRule ?_
  intro inst inst' hv hc ha
  -- Compare the extended instances, then use extensionality of f.
  have hcomm :
      f.resolute_committee (extend_candidates m inst) hres =
        f.resolute_committee (extend_candidates m inst') hres := by
    apply ABCRule.resolute_ballot_ext (f := f)
      (inst := extend_candidates m inst) (inst' := extend_candidates m inst') (hres := hres)
    · simpa [extend_candidates] using hv
    · simp [extend_candidates]
    · intro v hvv
      have := ha v (by simpa [extend_candidates] using hvv)
      simp [extend_candidates, this]
  simp [g, hcomm]

-- ============================================================================
-- MAIN INDUCTION LEMMA
-- ============================================================================

/--
Lemma 6 (Peters): If there exists a rule satisfying the axioms for m+1 candidates,
then there exists such a rule for m candidates (when m ≥ k).
-/
theorem induction_m (n m k : ℕ) (_hk : 3 ≤ k) (_hm : k ≤ m)
    (f : ABCRule (Fin n) (Fin (m + 1)) k)
    (hwf : IsWellFormedOnPlentiful f)
    (hres : f.IsResolute)
    (heff : f.SatisfiesWeakEfficiency)
    (hprop : f.SatisfiesProportionality)
    (hsp : Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f) :
    ∃ (f' : ABCRule (Fin n) (Fin m) k),
      IsWellFormedOnPlentiful f' ∧
      f'.IsResolute ∧
      f'.SatisfiesWeakEfficiency ∧
      f'.SatisfiesProportionality ∧
      Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f' := by
  classical
  let f' : ABCRule (Fin n) (Fin m) k := induced_rule (V := Fin n) (k := k) m f hres
  have hres' : f'.IsResolute := by
    intro inst
    simp [f', induced_rule, ResoluteABCRule.toABCRule]
  refine ⟨f', ?_⟩
  constructor
  · -- well-formed on plentiful instances
    intro inst hpl
    -- the unique committee of f' on inst
    have hcomm :
        f'.resolute_committee inst hres' =
          project_committee m (f.resolute_committee (extend_candidates m inst) hres) := by
      have hmem := f'.resolute_committee_mem inst hres'
      simpa [f', induced_rule, ResoluteABCRule.toABCRule] using hmem
    -- nonempty
    have hnonempty : (f' inst).Nonempty := by
      simpa [f', induced_rule, ResoluteABCRule.toABCRule] using
          (Finset.singleton_nonempty (f'.resolute_committee inst hres'))
    -- cardinality and subset
    have hpl_ext : (extend_candidates m inst).plentiful :=
      plentiful_extend_candidates (V := Fin n) (k := k) (m := m) inst hpl
    have hW_ext_mem := f.resolute_committee_mem (extend_candidates m inst) hres
    have hWF_ext := hwf (extend_candidates m inst) hpl_ext
    have hcard_ext : (f.resolute_committee (extend_candidates m inst) hres).card = k := by
      have hWF_ext' := (hWF_ext).2 _ hW_ext_mem
      exact hWF_ext'.1
    have hdummy :
        dummy_candidate m ∉ f.resolute_committee (extend_candidates m inst) hres := by
      refine ABCRule.unapproved_not_in_resolute (f := f) (hres := hres) (heff := heff)
        (inst := extend_candidates m inst) (c := dummy_candidate m) hpl_ext
        (dummy_unapproved (V := Fin n) (k := k) (m := m) inst)
    let emb : Fin m ↪ Fin (m + 1) := ⟨embed_candidate m, embed_candidate_injective m⟩
    have hmap :
        (project_committee m (f.resolute_committee (extend_candidates m inst) hres)).map emb =
          f.resolute_committee (extend_candidates m inst) hres :=
      map_project_committee_eq_of_not_dummy (m := m)
        (W := f.resolute_committee (extend_candidates m inst) hres) hdummy
    have hcard_proj :
        (project_committee m (f.resolute_committee (extend_candidates m inst) hres)).card = k := by
      have hcard_map := Finset.card_map (s := project_committee m
        (f.resolute_committee (extend_candidates m inst) hres)) emb
      have hcard_map' :
          (project_committee m (f.resolute_committee (extend_candidates m inst) hres)).card =
            (f.resolute_committee (extend_candidates m inst) hres).card := by
        simpa [hmap] using hcard_map.symm
      simpa [hcard_ext] using hcard_map'
    constructor
    · exact hnonempty
    · intro W hW
      have hW' :
          W = project_committee m (f.resolute_committee (extend_candidates m inst) hres) := by
        simpa [f', induced_rule, ResoluteABCRule.toABCRule, hcomm] using hW
      subst hW'
      constructor
      · simpa using hcard_proj
      · intro c hc
        have hc_ext : embed_candidate m c ∈
            f.resolute_committee (extend_candidates m inst) hres :=
          (mem_project_committee_iff (m := m)
            (W := f.resolute_committee (extend_candidates m inst) hres) (c := c)).1 hc
        have happ : (extend_candidates m inst).is_approved (embed_candidate m c) :=
          ABCRule.resolute_weak_efficiency (f := f) (hres := hres) (heff := heff)
            (inst := extend_candidates m inst) (c := embed_candidate m c) hpl_ext hc_ext
        rcases happ with ⟨v, hv, hcv⟩
        rcases Finset.mem_map.1 hcv with ⟨c', hc_mem, hEq⟩
        have hc_candidates : c ∈ inst.approves v := by
          have hc_eq : c' = c := by
            apply embed_candidate_injective m
            simpa using hEq
          subst hc_eq
          simpa using hc_mem
        have hv' : v ∈ inst.voters := by simpa [extend_candidates] using hv
        exact (inst.approves_subset v hv') hc_candidates
  constructor
  · -- resolute
    exact hres'
  constructor
  · -- weak efficiency (on plentiful instances)
    intro inst hpl W hW c hc
    -- Since `f' inst` is a singleton, reduce to the projected resolute committee.
    have hW' :
        W = project_committee m (f.resolute_committee (extend_candidates m inst) hres) := by
      simpa [f', induced_rule, ResoluteABCRule.toABCRule] using hW
    subst hW'
    have hpl_ext : (extend_candidates m inst).plentiful :=
      plentiful_extend_candidates (V := Fin n) (k := k) (m := m) inst hpl
    have hc_ext :
        embed_candidate m c ∈ f.resolute_committee (extend_candidates m inst) hres := by
      exact (mem_project_committee_iff (m := m)
          (W := f.resolute_committee (extend_candidates m inst) hres) (c := c)).1 hc
    -- If c were unapproved in the original instance, its embedding would be
    -- unapproved after extension.
    intro hunapp
    have hunapp_ext :
        (extend_candidates m inst).is_unapproved (embed_candidate m c) :=
      (is_unapproved_embed_iff (V := Fin n) (k := k) (m := m) inst c).2 hunapp
    -- Contradiction with weak efficiency of f on the plentiful extended instance.
    exact (heff (extend_candidates m inst) hpl_ext
      (f.resolute_committee (extend_candidates m inst) hres)
      (f.resolute_committee_mem (extend_candidates m inst) hres)
      (embed_candidate m c) hc_ext) hunapp_ext
  constructor
  · -- proportionality
    intro inst c hpl hcand hquota W hW
    have hW' :
        W = project_committee m (f.resolute_committee (extend_candidates m inst) hres) := by
      simpa [f', induced_rule, ResoluteABCRule.toABCRule] using hW
    subst hW'
    have hpl_ext : (extend_candidates m inst).is_party_list :=
      extend_candidates_party_list (V := Fin n) (k := k) (m := m) inst hpl
    have hcand_ext : embed_candidate m c ∈ (extend_candidates m inst).candidates := by
      simp [extend_candidates]
    have hquota_ext :
        (extend_candidates m inst).singleton_party_size (embed_candidate m c) * k ≥
          (extend_candidates m inst).voters.card := by
      -- voters are unchanged and singleton parties correspond via embedding
      have hs :
          (extend_candidates m inst).singleton_party_size (embed_candidate m c) =
            inst.singleton_party_size c :=
        singleton_party_size_extend_candidates (V := Fin n) (k := k) (m := m) inst c
      have hv : (extend_candidates m inst).voters.card = inst.voters.card := by
        simp [extend_candidates]
      simpa [hs, hv] using hquota
    have hc_ext :
        embed_candidate m c ∈ f.resolute_committee (extend_candidates m inst) hres :=
      ABCRule.resolute_proportionality (f := f) (hres := hres) (hprop := hprop)
        (inst := extend_candidates m inst)
        (c := embed_candidate m c)
        hpl_ext hcand_ext hquota_ext
    exact (mem_project_committee_iff (m := m)
        (W := f.resolute_committee (extend_candidates m inst) hres) (c := c)).2 hc_ext
  · -- strategyproofness on plentiful instances
    intro inst inst' i hpl hpl' hi hvar hsub hres''
    -- Pick the embedding once.
    let emb : Fin m ↪ Fin (m + 1) := ⟨embed_candidate m, embed_candidate_injective m⟩
    -- Normalize both extracted committees to the explicit projected committees.
    have hcomm_inst :
        f'.resolute_committee inst hres'' =
          project_committee m (f.resolute_committee (extend_candidates m inst) hres) := by
      have hmem := f'.resolute_committee_mem inst hres''
      simpa [f', induced_rule, ResoluteABCRule.toABCRule] using hmem
    have hcomm_inst' :
        f'.resolute_committee inst' hres'' =
          project_committee m (f.resolute_committee (extend_candidates m inst') hres) := by
      have hmem := f'.resolute_committee_mem inst' hres''
      simpa [f', induced_rule, ResoluteABCRule.toABCRule] using hmem
    -- Assume a successful manipulation for f' and derive one for f.
    intro hgain
    have hgain_ss :
        (project_committee m (f.resolute_committee (extend_candidates m inst) hres) ∩
          inst.approves i) ⊂
        (project_committee m (f.resolute_committee (extend_candidates m inst') hres) ∩
          inst.approves i) := by
      -- `⊃` is strict superset, i.e. reverse strict subset.
      simpa [hcomm_inst, hcomm_inst'] using hgain
    -- Extend plentifulness and exclude the dummy by weak efficiency.
    have hpl_ext : (extend_candidates m inst).plentiful :=
      plentiful_extend_candidates (V := Fin n) (k := k) (m := m) inst hpl
    have hpl'_ext : (extend_candidates m inst').plentiful :=
      plentiful_extend_candidates (V := Fin n) (k := k) (m := m) inst' hpl'
    have hdummy :
        dummy_candidate m ∉ f.resolute_committee (extend_candidates m inst) hres := by
      refine ABCRule.unapproved_not_in_resolute (f := f) (hres := hres) (heff := heff)
        (inst := extend_candidates m inst) (c := dummy_candidate m) hpl_ext
        (dummy_unapproved (V := Fin n) (k := k) (m := m) inst)
    have hdummy' :
        dummy_candidate m ∉ f.resolute_committee (extend_candidates m inst') hres := by
      refine ABCRule.unapproved_not_in_resolute (f := f) (hres := hres) (heff := heff)
        (inst := extend_candidates m inst')
        (c := dummy_candidate m) hpl'_ext
        (dummy_unapproved (V := Fin n) (k := k) (m := m) inst')
    -- Map the strict improvement through the embedding.
    have hgain_map :
        ((project_committee m (f.resolute_committee (extend_candidates m inst) hres) ∩
            inst.approves i).map emb) ⊂
          ((project_committee m (f.resolute_committee (extend_candidates m inst') hres) ∩
            inst.approves i).map emb) :=
      (Finset.map_ssubset_map (f := emb)).2 hgain_ss
    have hgain_map' :
        (f.resolute_committee (extend_candidates m inst) hres ∩
            (inst.approves i).map emb) ⊂
          (f.resolute_committee (extend_candidates m inst') hres ∩
            (inst.approves i).map emb) := by
      -- rewrite by `map_inter` and by `map_project_committee_eq_of_not_dummy`
      simpa [Finset.map_inter, emb,
        map_project_committee_eq_of_not_dummy (m := m)
          (W := f.resolute_committee (extend_candidates m inst) hres) hdummy,
        map_project_committee_eq_of_not_dummy (m := m)
          (W := f.resolute_committee (extend_candidates m inst') hres) hdummy'] using hgain_map
    have hgain_f :
        (f.resolute_committee (extend_candidates m inst') hres ∩
            (extend_candidates m inst).approves i) ⊃
          (f.resolute_committee (extend_candidates m inst) hres ∩
            (extend_candidates m inst).approves i) := by
      -- `approves` is mapped by the embedding in the extended instance.
      simpa [extend_candidates, emb] using hgain_map'
    -- Show that the manipulation data lifts to the extended instances.
    have hi_ext : i ∈ (extend_candidates m inst).voters := by
      simpa [extend_candidates] using hi
    have hvar_ext : (extend_candidates m inst).is_i_variant (extend_candidates m inst') i := by
      rcases hvar with ⟨hv, hc, ha⟩
      refine ⟨hv, ?_, ?_⟩
      · simp [extend_candidates]
      · intro v hvv hne
        have hvv' : v ∈ inst.voters := by simpa [extend_candidates] using hvv
        have := ha v hvv' hne
        simp [extend_candidates, this]
    have hsub_ext :
        (extend_candidates m inst').approves i ⊂ (extend_candidates m inst).approves i := by
      -- strict subset preserved by mapping through an embedding
      simpa [extend_candidates, emb] using (Finset.map_ssubset_map (f := emb)).2 hsub
    exact hsp (extend_candidates m inst) (extend_candidates m inst') i
      hpl_ext hpl'_ext hi_ext hvar_ext hsub_ext hres hgain_f

end Peters.InductionM
