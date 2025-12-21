import ABCVoting.Basic

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- WEAK COHESIVENESS
-- ============================================================================

/--
A group S is weakly (β, T)-cohesive if:
1. S is |T|-large: |S| * k ≥ |T| * n
2. Every voter in S approves at least β candidates from T

In the general PB model, this corresponds to |S|/n ≥ cost(T)/b and u_i(T) ≥ β.
In our unit-cost ABC setting, cost(T) = |T| and b = k.

Note: Unlike the FJR definition which takes l as a separate parameter,
here we set l = |T|.card, which is the natural choice for weak cohesiveness.
-/
def is_weakly_cohesive (inst : ABCInstance V C k) (S : Finset V) (T : Finset C) (β : ℕ) : Prop :=
  S ⊆ inst.voters ∧
  T ⊆ inst.candidates ∧
  S.Nonempty ∧
  β ≥ 1 ∧
  inst.is_l_large S T.card ∧
  ∀ i ∈ S, (inst.approves i ∩ T).card ≥ β

/--
A weakly cohesive witness relative to a current committee W and active voters.
This records a valid (β, S, T) triple that can be used in a GCR step.
-/
structure WeaklyCohesiveWitness (V C : Type*) [DecidableEq V] [DecidableEq C]
    {k : ℕ} (inst : ABCInstance V C k) (W : Finset C) (active : Finset V) where
  S : Finset V
  T : Finset C
  β : ℕ
  S_active : S ⊆ active
  T_candidates : T ⊆ inst.candidates
  T_nonempty : T.Nonempty
  S_nonempty : S.Nonempty
  β_pos : β ≥ 1
  S_large : inst.is_l_large S T.card
  S_approves : ∀ i ∈ S, (inst.approves i ∩ T).card ≥ β

-- ============================================================================
-- GCR STEP STRUCTURE
-- ============================================================================

/--
A single step of the Greedy Cohesive Rule.

Each step records:
- The group S of voters being deactivated
- The set T of candidates being added to the committee
- The β value (minimum approval count for voters in S)
- Properties ensuring this is a valid step

The step satisfies:
1. S consists of active voters
2. T is a subset of the candidates
3. S is weakly (β, T)-cohesive
4. β is maximal among all valid (β', S', T') triples
-/
structure GCRStep (V C : Type*) [DecidableEq V] [DecidableEq C]
    {k : ℕ} (inst : ABCInstance V C k) where
  -- State before this step
  committee_before : Finset C
  active_before : Finset V

  -- The chosen (β, S, T) triple
  S : Finset V
  T : Finset C
  β : ℕ

  -- ===== Validity properties =====

  -- S consists of active voters
  S_active : S ⊆ active_before

  -- T is in candidates
  T_candidates : T ⊆ inst.candidates
  T_nonempty : T.Nonempty

  -- S is nonempty and β is positive
  S_nonempty : S.Nonempty
  β_pos : β ≥ 1

  -- S is |T|-large
  S_large : inst.is_l_large S T.card

  -- Every voter in S approves at least β candidates from T
  S_approves : ∀ i ∈ S, (inst.approves i ∩ T).card ≥ β

  -- ===== Maximality of β =====
  -- β is maximal: no other valid triple has a larger β
  β_maximal : ∀ (w : WeaklyCohesiveWitness V C inst committee_before active_before),
    w.β ≤ β

/--
The committee after a GCR step: adds T to the current committee.
-/
def GCRStep.committee_after {inst : ABCInstance V C k} (step : GCRStep V C inst) : Finset C :=
  step.committee_before ∪ step.T

/--
The active voters after a GCR step: removes S from active voters.
-/
def GCRStep.active_after {inst : ABCInstance V C k} (step : GCRStep V C inst) : Finset V :=
  step.active_before \ step.S

-- ============================================================================
-- GCR WITNESS STRUCTURE
-- ============================================================================

/--
A witness for a complete Greedy Cohesive Rule execution.

This captures the full execution trace of the algorithm:
- A sequence of steps, each adding candidates and deactivating voters
- Proper linking between steps (output of step t is input to step t+1)
- Termination condition: no more valid (β, S, T) triples exist
-/
structure GCRWitness (V C : Type*) [DecidableEq V] [DecidableEq C]
    {k : ℕ} (inst : ABCInstance V C k) where
  -- Number of steps
  num_steps : ℕ

  -- The steps of execution
  steps : Fin num_steps → GCRStep V C inst

  -- ===== Initial conditions =====

  -- First step starts with empty committee and all voters active
  initial_committee : (h : num_steps > 0) →
    (steps ⟨0, h⟩).committee_before = ∅

  initial_active : (h : num_steps > 0) →
    (steps ⟨0, h⟩).active_before = inst.voters

  -- ===== Linking properties =====

  -- Steps are linked: output of step t = input to step t+1
  committee_linked : ∀ t : Fin num_steps, ∀ h : t.val + 1 < num_steps,
    (steps ⟨t.val + 1, h⟩).committee_before = (steps t).committee_after

  active_linked : ∀ t : Fin num_steps, ∀ h : t.val + 1 < num_steps,
    (steps ⟨t.val + 1, h⟩).active_before = (steps t).active_after

  -- ===== Termination =====

  -- Final committee and active voters (after all steps, or initial if no steps)
  final_committee : Finset C
  final_active : Finset V

  final_committee_correct :
    if h : num_steps > 0
    then final_committee = (steps ⟨num_steps - 1, Nat.sub_lt h Nat.one_pos⟩).committee_after
    else final_committee = ∅

  final_active_correct :
    if h : num_steps > 0
    then final_active = (steps ⟨num_steps - 1, Nat.sub_lt h Nat.one_pos⟩).active_after
    else final_active = inst.voters

  -- No more valid triples exist with the final state
  termination : ∀ (_ : WeaklyCohesiveWitness V C inst final_committee final_active), False

-- ============================================================================
-- GCR COMMITTEE DEFINITION
-- ============================================================================

/--
The committee produced by a GCR witness.
-/
def GCRWitness.committee {inst : ABCInstance V C k} (w : GCRWitness V C inst) : Finset C :=
  w.final_committee

/--
A committee is a GCR outcome if there exists a valid GCR witness producing it.
-/
def is_gcr_outcome (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∃ w : GCRWitness V C inst, w.committee = W

-- ============================================================================
-- BASIC LEMMAS
-- ============================================================================

/--
Active voters are always a subset of all voters.
-/
lemma GCRStep.active_after_subset {inst : ABCInstance V C k} (step : GCRStep V C inst)
    (h_before : step.active_before ⊆ inst.voters) :
    step.active_after ⊆ inst.voters := by
  unfold active_after
  exact sdiff_subset.trans h_before

/--
The committee after a step is a subset of candidates.
-/
lemma GCRStep.committee_after_subset {inst : ABCInstance V C k} (step : GCRStep V C inst)
    (h_before : step.committee_before ⊆ inst.candidates) :
    step.committee_after ⊆ inst.candidates := by
  unfold committee_after
  exact union_subset h_before step.T_candidates

/--
T is contained in committee_after.
-/
lemma GCRStep.T_subset_committee_after {inst : ABCInstance V C k} (step : GCRStep V C inst) :
    step.T ⊆ step.committee_after := by
  unfold committee_after
  exact subset_union_right

/--
The committee before is contained in committee_after.
-/
lemma GCRStep.committee_before_subset_after {inst : ABCInstance V C k} (step : GCRStep V C inst) :
    step.committee_before ⊆ step.committee_after := by
  unfold committee_after
  exact subset_union_left

/--
The committee at step t (before the step is taken).
-/
def GCRWitness.committee_at {inst : ABCInstance V C k}
    (w : GCRWitness V C inst) (t : Fin w.num_steps) : Finset C :=
  (w.steps t).committee_before

/--
The active voters at step t (before the step is taken).
-/
def GCRWitness.active_at {inst : ABCInstance V C k}
    (w : GCRWitness V C inst) (t : Fin w.num_steps) : Finset V :=
  (w.steps t).active_before

/--
The committee grows monotonically: committee at step s ⊆ committee at step t for s ≤ t.
-/
lemma GCRWitness.committee_mono {inst : ABCInstance V C k}
    (w : GCRWitness V C inst) (s t : Fin w.num_steps) (hst : s ≤ t) :
    w.committee_at s ⊆ w.committee_at t := by
  classical
  cases t with
  | mk t_val t_lt =>
    revert s
    induction t_val with
  | zero =>
      intro s hst
      have hsval : (s : ℕ) ≤ 0 := (Fin.le_def).1 hst
      have hsval0 : (s : ℕ) = 0 := Nat.le_zero.mp hsval
      let t0 : Fin w.num_steps := ⟨0, t_lt⟩
      have hs0 : s = t0 := by
        apply Fin.ext
        simpa using hsval0
      simpa [hs0, t0]
  | succ t_val ih =>
      intro s hst
      have hst' : s < ⟨t_val + 1, t_lt⟩ ∨ s = ⟨t_val + 1, t_lt⟩ :=
        lt_or_eq_of_le hst
      cases hst' with
      | inr hs_eq =>
          simpa [hs_eq]
      | inl hs_lt =>
          have hs_val_lt : (s : ℕ) < t_val + 1 := (Fin.lt_def).1 hs_lt
          have hs_val_le : (s : ℕ) ≤ t_val := (Nat.lt_succ_iff).1 hs_val_lt
          let t_prev : Fin w.num_steps := ⟨t_val, Nat.lt_of_succ_lt t_lt⟩
          have hs_le_prev : s ≤ t_prev := (Fin.le_def).2 hs_val_le
          have h_sub :
              w.committee_at s ⊆ w.committee_at t_prev :=
            ih (t_lt := Nat.lt_of_succ_lt t_lt) s hs_le_prev
          have h_before_after :
              w.committee_at t_prev ⊆ (w.steps t_prev).committee_after := by
            simpa [GCRWitness.committee_at] using
              (GCRStep.committee_before_subset_after (w.steps t_prev))
          have h_after_eq :
              (w.steps t_prev).committee_after = w.committee_at ⟨t_val + 1, t_lt⟩ := by
            simpa [GCRWitness.committee_at] using (w.committee_linked t_prev t_lt).symm
          have h_step :
              w.committee_at t_prev ⊆ w.committee_at ⟨t_val + 1, t_lt⟩ := by
            simpa [h_after_eq] using h_before_after
          exact h_sub.trans h_step

/--
The committee at any step is a subset of the final committee.
-/
lemma GCRWitness.committee_at_subset_final {inst : ABCInstance V C k}
    (w : GCRWitness V C inst) (t : Fin w.num_steps) :
    w.committee_at t ⊆ w.final_committee := by
  classical
  by_cases hnum : w.num_steps = 0
  · have : False := by
      have ht : (t : ℕ) < w.num_steps := t.isLt
      simpa [hnum] using ht
    exact (this.elim)
  · have hnum_pos : w.num_steps > 0 := Nat.pos_of_ne_zero hnum
    let t_last : Fin w.num_steps :=
      ⟨w.num_steps - 1, Nat.sub_lt hnum_pos Nat.one_pos⟩
    have ht_le' : (t : ℕ) ≤ w.num_steps - 1 := by
      have ht_lt : (t : ℕ) < w.num_steps := t.isLt
      have h1 : 1 ≤ w.num_steps := (Nat.succ_le_iff).2 hnum_pos
      have h_eq : w.num_steps - 1 + 1 = w.num_steps := Nat.sub_add_cancel h1
      have ht_lt' : (t : ℕ) < w.num_steps - 1 + 1 := by
        simpa [h_eq] using ht_lt
      exact (Nat.lt_succ_iff).1 ht_lt'
    have ht_le : t ≤ t_last := (Fin.le_def).2 ht_le'
    have hmono : w.committee_at t ⊆ w.committee_at t_last :=
      w.committee_mono t t_last ht_le
    have hfinal :
        w.final_committee = (w.steps t_last).committee_after := by
      simpa [hnum_pos] using (w.final_committee_correct)
    have hlast_subset : w.committee_at t_last ⊆ w.final_committee := by
      have h_before_after :
          w.committee_at t_last ⊆ (w.steps t_last).committee_after := by
        simpa [GCRWitness.committee_at] using
          (GCRStep.committee_before_subset_after (w.steps t_last))
      simpa [hfinal] using h_before_after
    exact hmono.trans hlast_subset

/--
T from step t is in the final committee.
-/
lemma GCRWitness.step_T_subset_final {inst : ABCInstance V C k}
    (w : GCRWitness V C inst) (t : Fin w.num_steps) :
    (w.steps t).T ⊆ w.final_committee := by
  classical
  have hT_after : (w.steps t).T ⊆ (w.steps t).committee_after :=
    (w.steps t).T_subset_committee_after
  by_cases hnext : t.val + 1 < w.num_steps
  · have hlink :
        (w.steps t).committee_after = w.committee_at ⟨t.val + 1, hnext⟩ := by
      simpa [GCRWitness.committee_at] using (w.committee_linked t hnext).symm
    have hnext_subset :
        w.committee_at ⟨t.val + 1, hnext⟩ ⊆ w.final_committee :=
      w.committee_at_subset_final ⟨t.val + 1, hnext⟩
    have h_after_subset : (w.steps t).committee_after ⊆ w.final_committee := by
      simpa [hlink] using hnext_subset
    exact hT_after.trans h_after_subset
  · have hnum_pos : w.num_steps > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) t.isLt
    let t_last : Fin w.num_steps :=
      ⟨w.num_steps - 1, Nat.sub_lt hnum_pos Nat.one_pos⟩
    have ht_val : (t : ℕ) = w.num_steps - 1 := by
      have ht_lt : (t : ℕ) < w.num_steps := t.isLt
      have ht_le : (t : ℕ) + 1 ≤ w.num_steps := (Nat.succ_le_iff).2 ht_lt
      have ht_eq : (t : ℕ) + 1 = w.num_steps := le_antisymm ht_le (Nat.le_of_not_lt hnext)
      omega
    have ht_last : t = t_last := by
      apply Fin.ext
      simpa [t_last, ht_val]
    have hfinal :
        w.final_committee = (w.steps t_last).committee_after := by
      simpa [hnum_pos] using (w.final_committee_correct)
    have h_after_subset :
        (w.steps t).committee_after ⊆ w.final_committee := by
      simpa [ht_last, hfinal]
    exact hT_after.trans h_after_subset

end ABCInstance
