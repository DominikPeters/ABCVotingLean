import ABCVoting.ABCRule

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- INSTANCE VARIANTS (BALLOT MANIPULATION)
-- ============================================================================

/--
Two instances are i-variants if they differ only in voter i's approval ballot.
All other aspects (voters, candidates, k, other ballots) are identical.

Since both instances have the same k (type parameter), we don't need to check k equality.
-/
def is_i_variant (inst inst' : ABCInstance V C k) (i : V) : Prop :=
  inst.voters = inst'.voters ∧
  inst.candidates = inst'.candidates ∧
  (∀ v ∈ inst.voters, v ≠ i → inst.approves v = inst'.approves v)

/--
is_i_variant is reflexive.
-/
lemma is_i_variant_refl (inst : ABCInstance V C k) (i : V) :
    inst.is_i_variant inst i := by
  refine ⟨rfl, rfl, fun _ _ _ => rfl⟩

/--
is_i_variant is symmetric.
-/
lemma is_i_variant_symm (inst inst' : ABCInstance V C k) (i : V)
    (h : inst.is_i_variant inst' i) : inst'.is_i_variant inst i := by
  obtain ⟨hv, hc, ha⟩ := h
  refine ⟨hv.symm, hc.symm, ?_⟩
  intro v hv' hne
  rw [← hv] at hv'
  exact (ha v hv' hne).symm

-- ============================================================================
-- CONSTRUCTING MODIFIED INSTANCES
-- ============================================================================

/--
Construct an instance where voter i's approval is changed to A'.
This requires A' to be a valid ballot (nonempty, proper subset of candidates).
-/
def modify_approval (inst : ABCInstance V C k) (i : V) (A' : Finset C)
    (hi : i ∈ inst.voters)
    (hA'_sub : A' ⊆ inst.candidates)
    (hA'_nonempty : A'.Nonempty)
    (hA'_proper : A' ⊂ inst.candidates) :
    ABCInstance V C k where
  voters := inst.voters
  candidates := inst.candidates
  approves := fun v => if v = i then A' else inst.approves v
  approves_subset := by
    intro v hv
    by_cases h : v = i
    · simp [h, hA'_sub]
    · simp [h, inst.approves_subset v hv]
  voters_nonempty := inst.voters_nonempty
  k_pos := inst.k_pos
  k_le_m := inst.k_le_m

/--
The modified instance is an i-variant of the original.
-/
lemma modify_approval_is_variant (inst : ABCInstance V C k) (i : V) (A' : Finset C)
    (hi : i ∈ inst.voters) (hA'_sub : A' ⊆ inst.candidates)
    (hA'_nonempty : A'.Nonempty) (hA'_proper : A' ⊂ inst.candidates) :
    inst.is_i_variant (inst.modify_approval i A' hi hA'_sub hA'_nonempty hA'_proper) i := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  simp [modify_approval, hne]

/--
In the modified instance, voter i approves exactly A'.
-/
lemma modify_approval_voter (inst : ABCInstance V C k) (i : V) (A' : Finset C)
    (hi : i ∈ inst.voters) (hA'_sub : A' ⊆ inst.candidates)
    (hA'_nonempty : A'.Nonempty) (hA'_proper : A' ⊂ inst.candidates) :
    (inst.modify_approval i A' hi hA'_sub hA'_nonempty hA'_proper).approves i = A' := by
  simp [modify_approval]

/--
In the modified instance, other voters' approvals are unchanged.
-/
lemma modify_approval_other (inst : ABCInstance V C k) (i : V) (A' : Finset C)
    (hi : i ∈ inst.voters) (hA'_sub : A' ⊆ inst.candidates)
    (hA'_nonempty : A'.Nonempty) (hA'_proper : A' ⊂ inst.candidates)
    (v : V) (hne : v ≠ i) :
    (inst.modify_approval i A' hi hA'_sub hA'_nonempty hA'_proper).approves v = inst.approves v := by
  simp [modify_approval, hne]

-- ============================================================================
-- RESOLUTE STRATEGYPROOFNESS
-- ============================================================================

/--
Resolute strategyproofness (Peters' version):

A resolute rule is strategyproof if no voter can benefit by reporting a
strict subset of their true approval ballot.

The benefit is measured by comparing the approved candidates in the outcome:
a manipulation is successful if the new committee contains a strict superset
of the approved candidates compared to the truthful outcome.

Formally: If inst' is obtained from inst by voter i reporting A' ⊂ A_i (strict subset),
then we cannot have f(inst') ∩ A_i ⊃ f(inst) ∩ A_i.
-/
def ABCRule.SatisfiesResoluteStrategyproofness (f : ABCRule V C k) : Prop :=
  ∀ (inst inst' : ABCInstance V C k) (i : V),
    i ∈ inst.voters →
    inst.is_i_variant inst' i →
    inst'.approves i ⊂ inst.approves i →  -- strict subset
    ∀ (hres : f.IsResolute),
      ¬((f.resolute_committee inst' hres) ∩ inst.approves i ⊃
        (f.resolute_committee inst hres) ∩ inst.approves i)

/--
Alternative formulation: the intersection cannot strictly grow.
Equivalent to saying the manipulation doesn't give strictly more approved candidates.
-/
lemma ABCRule.strategyproof_not_strict_superset (f : ABCRule V C k)
    (hsp : f.SatisfiesResoluteStrategyproofness)
    (inst inst' : ABCInstance V C k) (i : V)
    (hi : i ∈ inst.voters)
    (hvar : inst.is_i_variant inst' i)
    (hsub : inst'.approves i ⊂ inst.approves i)
    (hres : f.IsResolute) :
    ¬((f.resolute_committee inst' hres) ∩ inst.approves i ⊃
      (f.resolute_committee inst hres) ∩ inst.approves i) :=
  hsp inst inst' i hi hvar hsub hres

-- ============================================================================
-- STRATEGYPROOFNESS CONSEQUENCES
-- ============================================================================

/--
If voter i reports a subset and would gain a strict superset of approved
candidates in the committee, strategyproofness is violated.
-/
lemma ABCRule.sp_violation (f : ABCRule V C k)
    (inst inst' : ABCInstance V C k) (i : V)
    (hi : i ∈ inst.voters)
    (hvar : inst.is_i_variant inst' i)
    (hsub : inst'.approves i ⊂ inst.approves i)
    (hres : f.IsResolute)
    (hgain : (f.resolute_committee inst' hres) ∩ inst.approves i ⊃
             (f.resolute_committee inst hres) ∩ inst.approves i) :
    ¬f.SatisfiesResoluteStrategyproofness :=
  fun hsp => hsp inst inst' i hi hvar hsub hres hgain

/--
Contrapositive: If a rule is strategyproof and voter i reports a subset,
then the intersection with true approval cannot strictly grow.

Note: This is an alternative way to state the consequence of strategyproofness.
The statement says the intersection is not a strict superset, which is equivalent
to saying it's either a subset or incomparable.
-/
lemma ABCRule.sp_no_strict_improvement (f : ABCRule V C k)
    (hsp : f.SatisfiesResoluteStrategyproofness)
    (inst inst' : ABCInstance V C k) (i : V)
    (hi : i ∈ inst.voters)
    (hvar : inst.is_i_variant inst' i)
    (hsub : inst'.approves i ⊂ inst.approves i)
    (hres : f.IsResolute) :
    ¬((f.resolute_committee inst' hres) ∩ inst.approves i ⊃
      (f.resolute_committee inst hres) ∩ inst.approves i) :=
  hsp inst inst' i hi hvar hsub hres

-- ============================================================================
-- CHAIN LEMMA FOR STRATEGYPROOFNESS PROOFS
-- ============================================================================

/--
Key property: If a committee C excludes some candidate c, and we transition
via strategyproofness, then the new committee also cannot be C \ {c} ∪ {c} = C ∪ {c}
if that would be a strict improvement for the manipulator.

This is used in the base case proof where we track what committees are possible
after a sequence of ballot manipulations.
-/
lemma ABCRule.sp_chain_constraint (f : ABCRule V C k)
    (hsp : f.SatisfiesResoluteStrategyproofness)
    (inst inst' : ABCInstance V C k) (i : V)
    (hi : i ∈ inst.voters)
    (hvar : inst.is_i_variant inst' i)
    (hsub : inst'.approves i ⊂ inst.approves i)
    (hres : f.IsResolute)
    (W : Finset C)
    (hW : f.resolute_committee inst hres = W) :
    -- The manipulated outcome cannot give i strictly more approved candidates
    ¬((f.resolute_committee inst' hres) ∩ inst.approves i ⊃ W ∩ inst.approves i) := by
  rw [← hW]
  exact hsp inst inst' i hi hvar hsub hres

-- ============================================================================
-- KEY LEMMA FOR SINGLETON APPROVERS: COMMITTEE PERSISTENCE
-- ============================================================================

/--
Key lemma for Lemma 3 (Singleton Approvers), strict subset version:

If voter i's true approval set A_i has size k (the committee size), and the
current committee W is NOT equal to A_i, then after voter i manipulates by
reporting a STRICT subset of A_i, the resulting committee W' is still NOT
equal to A_i.

This is because:
- If W ≠ A_i but W has size k, then W ∩ A_i has size < k (at most k-1)
- If W' = A_i, then W' ∩ A_i = A_i has size k
- This would be a strict improvement (k > k-1), violating SP
-/
lemma ABCRule.sp_preserves_committee_ne_strict (f : ABCRule V C k)
    (hsp : f.SatisfiesResoluteStrategyproofness)
    (hwf : f.IsWellFormed)
    (inst inst' : ABCInstance V C k) (i : V)
    (hi : i ∈ inst.voters)
    (hvar : inst.is_i_variant inst' i)
    (hsub : inst'.approves i ⊂ inst.approves i) -- strict subset
    (hres : f.IsResolute)
    -- The true approval set has size k (equals committee size)
    (h_size : (inst.approves i).card = k)
    -- Current committee is NOT equal to i's approval set
    (hW_ne : f.resolute_committee inst hres ≠ inst.approves i) :
    -- After manipulation, committee is still NOT equal to i's approval set
    f.resolute_committee inst' hres ≠ inst.approves i := by
  intro hcontra
  -- Suppose f(inst') = inst.approves i = A_i
  -- Then f(inst') ∩ A_i = A_i (size k)

  have h1 : f.resolute_committee inst' hres ∩ inst.approves i = inst.approves i := by
    rw [hcontra]
    exact Finset.inter_self _

  -- Since f(inst) ≠ A_i and both have size k, their intersection is a strict subset of A_i
  have h_W_size : (f.resolute_committee inst hres).card = k :=
    (hwf inst).2 _ (f.resolute_committee_mem inst hres) |>.1

  have h2 : f.resolute_committee inst hres ∩ inst.approves i ⊂ inst.approves i := by
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · exact Finset.inter_subset_right
    · intro heq
      -- If intersection equals A_i, then A_i ⊆ f(inst)
      have hsub_W : inst.approves i ⊆ f.resolute_committee inst hres := by
        intro x hx
        have := Finset.ext_iff.mp heq x
        simp only [Finset.mem_inter] at this
        exact (this.mpr hx).1
      -- Both have size k, so subset implies equality
      have h_card_le : (f.resolute_committee inst hres).card ≤ (inst.approves i).card := by
        rw [h_W_size, h_size]
      have h_eq : inst.approves i = f.resolute_committee inst hres :=
        Finset.subset_iff_eq_of_card_le h_card_le |>.mp hsub_W
      exact hW_ne h_eq.symm

  -- Now h1 and h2 give us that f(inst') ∩ A_i ⊃ f(inst) ∩ A_i
  have h3 : f.resolute_committee inst' hres ∩ inst.approves i ⊃
            f.resolute_committee inst hres ∩ inst.approves i := by
    rw [h1]
    exact h2

  -- But this contradicts strategyproofness
  exact hsp inst inst' i hi hvar hsub hres h3

end ABCInstance
