import ABCVoting.ABCRule
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
Given a committee in Fin (m+1) that doesn't contain the dummy,
restrict it to Fin m.
-/
def restrict_committee (m : ℕ) (W : Finset (Fin (m + 1)))
    (hdummy : dummy_candidate m ∉ W) : Finset (Fin m) :=
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

-- ============================================================================
-- INDUCED RULE
-- ============================================================================

/--
Given a rule for m+1 candidates, induce a rule for m candidates.
The induced rule extends the instance, applies f, and restricts the output.
-/
def induced_rule (m : ℕ) {k : ℕ} (f : ABCRule V (Fin (m + 1)) k)
    (heff : f.SatisfiesWeakEfficiency) :
    ABCRule V (Fin m) k := by
  classical
  -- TODO: refactor to new ABCRule structure
  sorry

-- The actual implementation is tricky because we need to handle the
-- weak efficiency proof inline. Let's use a simpler approach.

/--
Alternative: Define the induced rule assuming f always excludes unapproved candidates.
-/
noncomputable def induced_rule' (m : ℕ) {k : ℕ} (f : ABCRule V (Fin (m + 1)) k)
    (hres : f.IsResolute)
    (heff : f.SatisfiesWeakEfficiency) :
    ABCRule V (Fin m) k := by
  classical
  -- TODO: refactor to new ABCRule structure
  sorry

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
