import ABCVoting.ABCRule

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k k' : ℕ}

-- ============================================================================
-- COMPATIBLE INSTANCES (same election, different committee size)
-- ============================================================================

/--
Two ABCInstances are compatible if they represent the same election
(same voters, candidates, and approval function) but possibly with different
target committee sizes k.
-/
def Compatible (inst : ABCInstance V C k) (inst' : ABCInstance V C k') : Prop :=
  inst.voters = inst'.voters ∧
  inst.candidates = inst'.candidates ∧
  ∀ v, inst.approves v = inst'.approves v

lemma Compatible.voters_eq {inst : ABCInstance V C k} {inst' : ABCInstance V C k'}
    (h : inst.Compatible inst') : inst.voters = inst'.voters := h.1

lemma Compatible.candidates_eq {inst : ABCInstance V C k} {inst' : ABCInstance V C k'}
    (h : inst.Compatible inst') : inst.candidates = inst'.candidates := h.2.1

lemma Compatible.approves_eq {inst : ABCInstance V C k} {inst' : ABCInstance V C k'}
    (h : inst.Compatible inst') (v : V) : inst.approves v = inst'.approves v := h.2.2 v

@[refl]
lemma Compatible.refl (inst : ABCInstance V C k) : inst.Compatible inst :=
  ⟨rfl, rfl, fun _ => rfl⟩

@[symm]
lemma Compatible.symm {inst : ABCInstance V C k} {inst' : ABCInstance V C k'}
    (h : inst.Compatible inst') : inst'.Compatible inst :=
  ⟨h.1.symm, h.2.1.symm, fun v => (h.2.2 v).symm⟩

-- ============================================================================
-- COMMITTEE MONOTONICITY
-- ============================================================================

/--
Committee Monotonicity (Upward): When increasing committee size from k to k+1,
every winning committee W has a superset W' that wins with the larger size.

This captures the intuition that candidates already selected should not be dropped
when we are allowed to select more candidates.
-/
def ABCRule.CommitteeMonotonicityUp (f : ABCRule V C k) (f' : ABCRule V C (k + 1)) : Prop :=
  ∀ (inst : ABCInstance V C k) (inst' : ABCInstance V C (k + 1)),
    inst.Compatible inst' →
    ∀ W ∈ f inst, ∃ W' ∈ f' inst', W ⊆ W'

/--
Committee Monotonicity (Downward): When decreasing committee size from k+1 to k,
every winning committee W has a subset W' that wins with the smaller size.

This is the converse direction: for each size-(k+1) winning committee,
some size-k subset of it should also be a winner.
-/
def ABCRule.CommitteeMonotonicityDown (f : ABCRule V C k) (f' : ABCRule V C (k + 1)) : Prop :=
  ∀ (inst : ABCInstance V C k) (inst' : ABCInstance V C (k + 1)),
    inst.Compatible inst' →
    ∀ W ∈ f' inst', ∃ W' ∈ f inst, W' ⊆ W

/--
Committee Monotonicity: Both upward and downward monotonicity hold.

From Elkind, Faliszewski, Skowron, Slinko "Properties of Multiwinner Voting Rules":
For each election E = (C, V), for each k ∈ [m-1]:
(1) if W ∈ R(E,k) then there exists W' ∈ R(E,k+1) such that W ⊆ W'
(2) if W ∈ R(E,k+1) then there exists W' ∈ R(E,k) such that W' ⊆ W
-/
def ABCRule.CommitteeMonotonicity (f : ABCRule V C k) (f' : ABCRule V C (k + 1)) : Prop :=
  f.CommitteeMonotonicityUp f' ∧ f.CommitteeMonotonicityDown f'

end ABCInstance
