import ABCVoting.ABCRule

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- WEAK EFFICIENCY
-- ============================================================================

/--
The set of candidates approved by at least one voter.

This is `⋃ i ∈ voters, approves i` as a `Finset`.
-/
def approvedCandidates (inst : ABCInstance V C k) : Finset C :=
  inst.voters.biUnion inst.approves

/--
An instance is *plentiful* if there are at least `k` distinct approved candidates in total.

This corresponds to the domain restriction in Peters' paper:
`|⋃_{i∈N} P(i)| ≥ k`.
-/
def plentiful (inst : ABCInstance V C k) : Prop :=
  inst.approvedCandidates.card ≥ k

/--
A candidate is unapproved if no voter approves it.
-/
def is_unapproved (inst : ABCInstance V C k) (c : C) : Prop :=
  ∀ v ∈ inst.voters, c ∉ inst.approves v

/--
Equivalently, a candidate is unapproved iff it has no supporters.
-/
lemma is_unapproved_iff_supporters_empty (inst : ABCInstance V C k) (c : C) :
    inst.is_unapproved c ↔ inst.supporters c = ∅ := by
  simp only [is_unapproved, supporters, filter_eq_empty_iff]

/--
A candidate is approved if at least one voter approves it.
-/
def is_approved (inst : ABCInstance V C k) (c : C) : Prop :=
  ∃ v ∈ inst.voters, c ∈ inst.approves v

/--
is_approved is the negation of is_unapproved.
-/
lemma is_approved_iff_not_unapproved (inst : ABCInstance V C k) (c : C) :
    inst.is_approved c ↔ ¬inst.is_unapproved c := by
  simp only [is_approved, is_unapproved, not_forall, not_not, exists_prop]

-- ============================================================================
-- WEAK EFFICIENCY AXIOM
-- ============================================================================

/--
An ABC rule satisfies weak efficiency if, on plentiful instances,
no unapproved candidate is ever elected.

This is a mild efficiency condition: we should not waste committee seats on
candidates that no voter approves.
-/
def ABCRule.SatisfiesWeakEfficiency (f : ABCRule V C k) : Prop :=
  ∀ inst : ABCInstance V C k,
    inst.plentiful →
    ∀ W ∈ f inst, ∀ c ∈ W, ¬inst.is_unapproved c

-- ============================================================================
-- DOMINATING CANDIDATE EFFICIENCY (Kluiving et al.)
-- ============================================================================

/--
Candidate a dominates candidate b if every voter who approves b also approves a,
and at least one voter approves a but not b.
-/
def dominates (inst : ABCInstance V C k) (a b : C) : Prop :=
  (∀ v ∈ inst.voters, b ∈ inst.approves v → a ∈ inst.approves v) ∧
  (∃ v ∈ inst.voters, a ∈ inst.approves v ∧ b ∉ inst.approves v)

/--
Dominating candidate efficiency: if a dominates b, then any winning committee
containing b must also contain a.
-/
def ABCRule.SatisfiesDominatingCandidateEfficiency (f : ABCRule V C k) : Prop :=
  ∀ (inst : ABCInstance V C k) (a b : C),
    a ∈ inst.candidates →
    b ∈ inst.candidates →
    inst.dominates a b →
    ∀ W ∈ f inst, b ∈ W → a ∈ W

/--
Equivalently: every elected candidate must have at least one supporter.
-/
lemma ABCRule.satisfiesWeakEfficiency_iff_approved (f : ABCRule V C k) :
    f.SatisfiesWeakEfficiency ↔
    ∀ inst : ABCInstance V C k,
      inst.plentiful →
      ∀ W ∈ f inst, ∀ c ∈ W, inst.is_approved c := by
  simp only [ABCRule.SatisfiesWeakEfficiency, is_approved_iff_not_unapproved]

/--
For a resolute rule satisfying weak efficiency, the unique committee
contains only approved candidates.
-/
lemma ABCRule.resolute_weak_efficiency (f : ABCRule V C k)
    (hres : f.IsResolute) (heff : f.SatisfiesWeakEfficiency)
    (inst : ABCInstance V C k) (c : C)
    (hpl : inst.plentiful)
    (hc : c ∈ f.resolute_committee inst hres) :
    inst.is_approved c := by
  rw [is_approved_iff_not_unapproved]
  exact heff inst hpl (f.resolute_committee inst hres) (f.resolute_committee_mem inst hres) c hc

/--
Equivalently: unapproved candidates are not in the resolute committee.
-/
lemma ABCRule.unapproved_not_in_resolute (f : ABCRule V C k)
    (hres : f.IsResolute) (heff : f.SatisfiesWeakEfficiency)
    (inst : ABCInstance V C k) (c : C)
    (hpl : inst.plentiful)
    (hunapproved : inst.is_unapproved c) :
    c ∉ f.resolute_committee inst hres := by
  intro hc
  exact (heff inst hpl (f.resolute_committee inst hres) (f.resolute_committee_mem inst hres) c hc)
    hunapproved

end ABCInstance
