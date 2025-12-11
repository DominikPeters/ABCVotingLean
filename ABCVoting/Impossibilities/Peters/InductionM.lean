import ABCVoting.Axioms.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness

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

variable {V : Type*} [DecidableEq V]

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
def extend_candidates (m : ℕ) (inst : ABCInstance V (Fin m)) :
    ABCInstance V (Fin (m + 1)) where
  voters := inst.voters
  candidates := Finset.univ
  approves := fun v => (inst.approves v).map ⟨embed_candidate m, embed_candidate_injective m⟩
  approves_subset := by
    intro v _
    exact Finset.subset_univ _
  voters_nonempty := inst.voters_nonempty
  k := inst.k
  k_pos := inst.k_pos
  k_le_m := by
    simp only [Finset.card_fin]
    exact Nat.le_succ_of_le inst.k_le_m

/--
The extended instance has the same k value.
-/
lemma extend_candidates_k (m : ℕ) (inst : ABCInstance V (Fin m)) :
    (extend_candidates m inst).k = inst.k := rfl

/--
The dummy candidate is unapproved in the extended instance.
-/
lemma dummy_unapproved (m : ℕ) (inst : ABCInstance V (Fin m)) :
    (extend_candidates m inst).is_unapproved (dummy_candidate m) := by
  intro v _
  simp only [extend_candidates, Finset.mem_map, Function.Embedding.coeFn_mk]
  intro ⟨c, _, hc⟩
  exact dummy_not_embedded m c hc

-- ============================================================================
-- COMMITTEE RESTRICTION
-- ============================================================================

/--
Given a committee in Fin (m+1) that doesn't contain the dummy,
restrict it to Fin m.
-/
def restrict_committee (m : ℕ) (W : Finset (Fin (m + 1)))
    (hdummy : dummy_candidate m ∉ W) : Finset (Fin m) :=
  W.filterMap (fun c =>
    if h : c.val < m then some ⟨c.val, h⟩ else none) (by
      intro c1 c2 hc1 hc2
      simp only [Option.mem_def] at hc1 hc2
      split_ifs at hc1 hc2 with h1 h2
      · simp only [Option.some.injEq, Fin.mk.injEq] at hc1 hc2
        exact Fin.ext (hc1 ▸ hc2)
      all_goals simp_all)

-- ============================================================================
-- INDUCED RULE
-- ============================================================================

/--
Given a rule for m+1 candidates, induce a rule for m candidates.
The induced rule extends the instance, applies f, and restricts the output.
-/
def induced_rule (m : ℕ) {k : ℕ} (f : ABCRule V (Fin (m + 1)) k)
    (heff : f.SatisfiesWeakEfficiency) :
    ABCRule V (Fin m) k :=
  fun inst hk =>
    let ext_inst := extend_candidates m inst
    (f ext_inst (by simp [extend_candidates, hk])).image (fun W =>
      -- By weak efficiency, the dummy is never elected
      restrict_committee m W sorry)

-- The actual implementation is tricky because we need to handle the
-- weak efficiency proof inline. Let's use a simpler approach.

/--
Alternative: Define the induced rule assuming f always excludes unapproved candidates.
-/
noncomputable def induced_rule' (m : ℕ) {k : ℕ} (f : ABCRule V (Fin (m + 1)) k)
    (hres : f.IsResolute)
    (heff : f.SatisfiesWeakEfficiency) :
    ABCRule V (Fin m) k :=
  fun inst hk =>
    let ext_inst := extend_candidates m inst
    let hk_ext : ext_inst.k = k := by simp [extend_candidates, hk]
    let W := f.resolute_committee ext_inst hk_ext hres
    have hdummy : dummy_candidate m ∉ W := by
      apply heff ext_inst hk_ext W (f.resolute_committee_mem ext_inst hk_ext hres)
        (dummy_candidate m)
      · -- Need to show dummy is in W, which we're trying to prove it's not
        -- This approach doesn't work directly
        sorry
      · exact dummy_unapproved m inst
    {restrict_committee m W hdummy}

-- ============================================================================
-- MAIN INDUCTION LEMMA
-- ============================================================================

/--
Lemma 6 (Peters): If there exists a rule satisfying the axioms for m+1 candidates,
then there exists such a rule for m candidates (when m ≥ k).
-/
theorem induction_m (n m k : ℕ) (hk : 3 ≤ k) (hm : k ≤ m)
    (f : ABCRule (Fin n) (Fin (m + 1)) k)
    (hres : f.IsResolute)
    (heff : f.SatisfiesWeakEfficiency)
    (hprop : f.SatisfiesProportionality)
    (hsp : f.SatisfiesResoluteStrategyproofness) :
    ∃ (f' : ABCRule (Fin n) (Fin m) k),
      f'.IsResolute ∧
      f'.SatisfiesWeakEfficiency ∧
      f'.SatisfiesProportionality ∧
      f'.SatisfiesResoluteStrategyproofness := by
  -- The proof constructs the induced rule and verifies all axioms
  sorry

end Peters.InductionM
