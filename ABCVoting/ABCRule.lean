import ABCVoting.Basic

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C]

-- ============================================================================
-- ABC RULE TYPE
-- ============================================================================

/--
An ABC voting rule for committee size k is a structure with:
- An apply function that maps an ABCInstance to a set of committees
- An extensionality property: the rule's output depends only on the voters,
  candidates, and approval ballots of voters (not on the parameter k)

The rule may return multiple committees (irresolute) or exactly one (resolute).
-/
structure ABCRule (V C : Type*) [DecidableEq V] [DecidableEq C] (k : ℕ) where
  apply : ABCInstance V C k → Finset (Finset C)
  extensional : ∀ inst inst',
    inst.voters = inst'.voters →
    inst.candidates = inst'.candidates →
    (∀ v ∈ inst.voters, inst.approves v = inst'.approves v) →
    apply inst = apply inst'

/--
Coerce ABCRule to a function via its apply field.
-/
instance : CoeFun (ABCRule V C k) (fun _ => ABCInstance V C k → Finset (Finset C)) where
  coe f := f.apply

-- ============================================================================
-- WELL-FORMEDNESS
-- ============================================================================

/--
An ABC rule is well-formed if for every instance, it returns a non-empty set
of committees, and each committee has size k and is a subset of candidates.
-/
def ABCRule.IsWellFormed (f : ABCRule V C k) : Prop :=
  ∀ (inst : ABCInstance V C k),
    (f inst).Nonempty ∧
    ∀ W ∈ f inst, W.card = k ∧ W ⊆ inst.candidates

-- ============================================================================
-- RESOLUTENESS
-- ============================================================================

/--
An ABC rule is resolute if it always returns exactly one committee.
-/
def ABCRule.IsResolute (f : ABCRule V C k) : Prop :=
  ∀ (inst : ABCInstance V C k), (f inst).card = 1

/--
A resolute rule is automatically well-formed in terms of returning non-empty sets.
-/
lemma ABCRule.resolute_nonempty (f : ABCRule V C k) (hres : f.IsResolute)
    (inst : ABCInstance V C k) : (f inst).Nonempty := by
  have h := hres inst
  exact Finset.card_pos.mp (by omega)

-- ============================================================================
-- EXTRACTING THE UNIQUE COMMITTEE FROM A RESOLUTE RULE
-- ============================================================================

/--
For a resolute rule, extract the unique committee from the singleton set.
-/
noncomputable def ABCRule.resolute_committee (f : ABCRule V C k)
    (inst : ABCInstance V C k) (hres : f.IsResolute) : Finset C :=
  (f.resolute_nonempty hres inst).choose

/--
The extracted committee is a member of the rule's output.
-/
lemma ABCRule.resolute_committee_mem (f : ABCRule V C k)
    (inst : ABCInstance V C k) (hres : f.IsResolute) :
    f.resolute_committee inst hres ∈ f inst :=
  (f.resolute_nonempty hres inst).choose_spec

/--
The rule's output equals the singleton containing the extracted committee.
-/
lemma ABCRule.resolute_committee_spec (f : ABCRule V C k)
    (inst : ABCInstance V C k) (hres : f.IsResolute) :
    f inst = {f.resolute_committee inst hres} := by
  have h := hres inst
  rw [Finset.card_eq_one] at h
  obtain ⟨W, hW⟩ := h
  have hmem : f.resolute_committee inst hres ∈ f inst := f.resolute_committee_mem inst hres
  rw [hW] at hmem ⊢
  simp only [Finset.mem_singleton] at hmem
  exact congrArg _ hmem.symm

/--
Membership in a resolute rule's output is equivalent to equality with the extracted committee.
-/
lemma ABCRule.mem_resolute_iff (f : ABCRule V C k)
    (inst : ABCInstance V C k) (hres : f.IsResolute) (W : Finset C) :
    W ∈ f inst ↔ W = f.resolute_committee inst hres := by
  rw [f.resolute_committee_spec inst hres]
  simp only [Finset.mem_singleton]

/--
If a property holds for all committees in a resolute rule's output,
it holds for the extracted committee.
-/
lemma ABCRule.resolute_property (f : ABCRule V C k)
    (inst : ABCInstance V C k) (hres : f.IsResolute) (P : Finset C → Prop)
    (hP : ∀ W ∈ f inst, P W) :
    P (f.resolute_committee inst hres) :=
  hP _ (f.resolute_committee_mem inst hres)

/--
Two committees from a resolute rule's output must be equal.
-/
lemma ABCRule.resolute_unique (f : ABCRule V C k)
    (inst : ABCInstance V C k) (hres : f.IsResolute)
    (W₁ W₂ : Finset C) (h₁ : W₁ ∈ f inst) (h₂ : W₂ ∈ f inst) :
    W₁ = W₂ := by
  rw [f.mem_resolute_iff inst hres] at h₁ h₂
  exact h₁.trans h₂.symm

-- ============================================================================
-- ALTERNATE CHARACTERIZATION: RESOLUTE FUNCTION TYPE
-- ============================================================================

/--
A resolute ABC rule can be viewed as a function returning a single committee.
This is the "unwrapped" version that returns Finset C directly.
-/
def ResoluteABCRule (V C : Type*) [DecidableEq V] [DecidableEq C] (k : ℕ) :=
  (inst : ABCInstance V C k) → Finset C

/--
Convert a resolute ABCRule to a ResoluteABCRule.
-/
noncomputable def ABCRule.toResolute (f : ABCRule V C k) (hres : f.IsResolute) :
    ResoluteABCRule V C k :=
  fun inst => f.resolute_committee inst hres

/--
Convert a ResoluteABCRule to an ABCRule.
Requires a proof that the resolute rule is extensional.
-/
def ResoluteABCRule.toABCRule (f : ResoluteABCRule V C k)
    (hext : ∀ inst inst' : ABCInstance V C k,
      inst.voters = inst'.voters →
      inst.candidates = inst'.candidates →
      (∀ v ∈ inst.voters, inst.approves v = inst'.approves v) →
      f inst = f inst') : ABCRule V C k where
  apply inst := {f inst}
  extensional := fun inst inst' hv hc ha => by simp [hext inst inst' hv hc ha]

/--
A ResoluteABCRule converted to ABCRule is resolute.
-/
lemma ResoluteABCRule.toABCRule_isResolute (f : ResoluteABCRule V C k)
    (hext : ∀ inst inst' : ABCInstance V C k,
      inst.voters = inst'.voters →
      inst.candidates = inst'.candidates →
      (∀ v ∈ inst.voters, inst.approves v = inst'.approves v) →
      f inst = f inst') :
    (f.toABCRule hext).IsResolute := by
  intro inst
  simp [ResoluteABCRule.toABCRule]

-- ============================================================================
-- EXTENSIONALITY FOR ABC RULES
-- ============================================================================

/--
For a resolute rule, if two instances have the same voters, candidates, and voter approvals,
then the extracted committees are equal.
-/
lemma ABCRule.resolute_ballot_ext (f : ABCRule V C k)
    (inst inst' : ABCInstance V C k)
    (hres : f.IsResolute)
    (hv : inst.voters = inst'.voters)
    (hc : inst.candidates = inst'.candidates)
    (ha : ∀ v ∈ inst.voters, inst.approves v = inst'.approves v) :
    f.resolute_committee inst hres = f.resolute_committee inst' hres := by
  have heq : f inst = f inst' := f.extensional inst inst' hv hc ha
  -- Both committees are the unique element of f inst = f inst'
  have h1 : f.resolute_committee inst hres ∈ f inst :=
    f.resolute_committee_mem inst hres
  have h2 : f.resolute_committee inst' hres ∈ f inst' :=
    f.resolute_committee_mem inst' hres
  rw [heq] at h1
  exact f.resolute_unique inst' hres _ _ h1 h2

-- ============================================================================
-- KEY LEMMA: COMMITTEE MEMBERSHIP WHEN m = k+1
-- ============================================================================

/--
When there are exactly k+1 candidates and committees have size k,
a committee either contains a given candidate c, or equals C \ {c}.

This is because C \ {c} is the unique size-k subset not containing c.
-/
lemma committee_contains_or_complement {C : Type*} [DecidableEq C]
    (candidates : Finset C) (c : C) (hc : c ∈ candidates)
    (W : Finset C) (hW_sub : W ⊆ candidates) (hW_card : W.card = candidates.card - 1) :
    c ∈ W ∨ W = candidates \ {c} := by
  by_cases hcW : c ∈ W
  · left; exact hcW
  · right
    -- W doesn't contain c, so W ⊆ candidates \ {c}
    have hW_sub' : W ⊆ candidates \ {c} := by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact hW_sub hx
      · intro heq; rw [heq] at hx; exact hcW hx
    -- Both have the same cardinality
    have hcard_comp : (candidates \ {c}).card = candidates.card - 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hc), Finset.card_singleton]
    -- Same cardinality + subset = equality
    rw [← hcard_comp] at hW_card
    exact Finset.eq_of_subset_of_card_le hW_sub' (le_of_eq hW_card.symm)

/--
Contrapositive: If W ≠ C \ {c} and W is a size-k subset of C with |C| = k+1, then c ∈ W.
-/
lemma committee_ne_complement_has_c {C : Type*} [DecidableEq C]
    (candidates : Finset C) (c : C) (hc : c ∈ candidates)
    (W : Finset C) (hW_sub : W ⊆ candidates) (hW_card : W.card = candidates.card - 1)
    (hW_ne : W ≠ candidates \ {c}) :
    c ∈ W := by
  cases committee_contains_or_complement candidates c hc W hW_sub hW_card with
  | inl h => exact h
  | inr h => exact absurd h hW_ne

end ABCInstance
