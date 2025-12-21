import ABCVoting.Rules.GreedyCohesiveRule.Defs
import ABCVoting.Rules.GreedyCohesiveRule.FJR

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- PARAMETRIZED WITNESS (STARTING FROM AN ARBITRARY STATE)
-- ============================================================================

/--
A witness for a GCR execution starting from a given committee and active set.

This mirrors `GCRWitness` but replaces the fixed initial state (∅, voters)
with explicit parameters `W0` and `active0`.
-/
structure GCRWitnessFrom (V C : Type*) [DecidableEq V] [DecidableEq C]
    {k : ℕ} (inst : ABCInstance V C k) (W0 : Finset C) (active0 : Finset V) where
  num_steps : ℕ
  steps : Fin num_steps → GCRStep V C inst

  initial_committee : (h : num_steps > 0) →
    (steps ⟨0, h⟩).committee_before = W0

  initial_active : (h : num_steps > 0) →
    (steps ⟨0, h⟩).active_before = active0

  committee_linked : ∀ t : Fin num_steps, ∀ h : t.val + 1 < num_steps,
    (steps ⟨t.val + 1, h⟩).committee_before = (steps t).committee_after

  active_linked : ∀ t : Fin num_steps, ∀ h : t.val + 1 < num_steps,
    (steps ⟨t.val + 1, h⟩).active_before = (steps t).active_after

  final_committee : Finset C
  final_active : Finset V

  final_committee_correct :
    if h : num_steps > 0
    then final_committee = (steps ⟨num_steps - 1, Nat.sub_lt h Nat.one_pos⟩).committee_after
    else final_committee = W0

  final_active_correct :
    if h : num_steps > 0
    then final_active = (steps ⟨num_steps - 1, Nat.sub_lt h Nat.one_pos⟩).active_after
    else final_active = active0

  termination : ∀ (_ : WeaklyCohesiveWitness V C inst final_committee final_active), False

namespace GCRWitnessFrom

/--
Prepend a step to a witness from the successor state.
-/
noncomputable def cons {inst : ABCInstance V C k} (step : GCRStep V C inst)
    (w : GCRWitnessFrom V C inst step.committee_after step.active_after) :
    GCRWitnessFrom V C inst step.committee_before step.active_before where
  num_steps := w.num_steps + 1
  steps := fun i => Fin.cases step (fun j => w.steps j) i
  initial_committee := by
    intro h
    simp [Fin.cases]
  initial_active := by
    intro h
    simp [Fin.cases]
  committee_linked := by
    intro t ht
    cases t with
    | mk t_val t_lt =>
      cases t_val with
    | zero =>
        have hpos : w.num_steps > 0 := by
          have : 1 < w.num_steps + 1 := by simpa using ht
          exact Nat.lt_of_succ_lt_succ this
        have h0 : (w.steps ⟨0, hpos⟩).committee_before = step.committee_after :=
          (w.initial_committee hpos)
        simpa [Fin.cases] using h0
    | succ t_val =>
        have ht' : t_val + 1 < w.num_steps := by
          have : t_val.succ + 1 < w.num_steps + 1 := by simpa using ht
          exact Nat.lt_of_succ_lt_succ this
        have hlink : (w.steps ⟨t_val + 1, ht'⟩).committee_before =
            (w.steps ⟨t_val, Nat.lt_of_succ_lt ht'⟩).committee_after :=
          w.committee_linked ⟨t_val, Nat.lt_of_succ_lt ht'⟩ ht'
        simpa [Fin.cases] using hlink
  active_linked := by
    intro t ht
    cases t with
    | mk t_val t_lt =>
      cases t_val with
    | zero =>
        have hpos : w.num_steps > 0 := by
          have : 1 < w.num_steps + 1 := by simpa using ht
          exact Nat.lt_of_succ_lt_succ this
        have h0 : (w.steps ⟨0, hpos⟩).active_before = step.active_after :=
          (w.initial_active hpos)
        simpa [Fin.cases] using h0
    | succ t_val =>
        have ht' : t_val + 1 < w.num_steps := by
          have : t_val.succ + 1 < w.num_steps + 1 := by simpa using ht
          exact Nat.lt_of_succ_lt_succ this
        have hlink : (w.steps ⟨t_val + 1, ht'⟩).active_before =
            (w.steps ⟨t_val, Nat.lt_of_succ_lt ht'⟩).active_after :=
          w.active_linked ⟨t_val, Nat.lt_of_succ_lt ht'⟩ ht'
        simpa [Fin.cases] using hlink
  final_committee := w.final_committee
  final_active := w.final_active
  final_committee_correct := by
    classical
    have hpos : w.num_steps + 1 > 0 := Nat.succ_pos _
    by_cases hzero : w.num_steps = 0
    · have hw : w.final_committee = step.committee_after := by
        simpa [hzero] using (w.final_committee_correct)
      simpa [hpos, hzero, Fin.cases] using hw
    · have hpos' : w.num_steps > 0 := Nat.pos_of_ne_zero hzero
      have hw :
          w.final_committee =
            (w.steps ⟨w.num_steps - 1, Nat.sub_lt hpos' Nat.one_pos⟩).committee_after := by
        simpa [hpos'] using (w.final_committee_correct)
      have hidx :
          (⟨w.num_steps, by simpa using Nat.lt_succ_self w.num_steps⟩ : Fin (w.num_steps + 1)) =
            (⟨w.num_steps - 1, Nat.sub_lt hpos' Nat.one_pos⟩ : Fin w.num_steps).succ := by
        apply Fin.ext
        simp [Nat.sub_add_cancel (Nat.succ_le_iff.2 hpos')]
      have hcases :
          (Fin.cases step (fun j => w.steps j)
              ⟨w.num_steps, by simpa using Nat.lt_succ_self w.num_steps⟩) =
            w.steps ⟨w.num_steps - 1, Nat.sub_lt hpos' Nat.one_pos⟩ := by
        simpa [hidx, Fin.cases_succ]
      simpa [hpos, Nat.add_sub_cancel_right, hcases] using hw
  final_active_correct := by
    classical
    have hpos : w.num_steps + 1 > 0 := Nat.succ_pos _
    by_cases hzero : w.num_steps = 0
    · have hw : w.final_active = step.active_after := by
        simpa [hzero] using (w.final_active_correct)
      simpa [hpos, hzero, Fin.cases] using hw
    · have hpos' : w.num_steps > 0 := Nat.pos_of_ne_zero hzero
      have hw :
          w.final_active =
            (w.steps ⟨w.num_steps - 1, Nat.sub_lt hpos' Nat.one_pos⟩).active_after := by
        simpa [hpos'] using (w.final_active_correct)
      have hidx :
          (⟨w.num_steps, by simpa using Nat.lt_succ_self w.num_steps⟩ : Fin (w.num_steps + 1)) =
            (⟨w.num_steps - 1, Nat.sub_lt hpos' Nat.one_pos⟩ : Fin w.num_steps).succ := by
        apply Fin.ext
        simp [Nat.sub_add_cancel (Nat.succ_le_iff.2 hpos')]
      have hcases :
          (Fin.cases step (fun j => w.steps j)
              ⟨w.num_steps, by simpa using Nat.lt_succ_self w.num_steps⟩) =
            w.steps ⟨w.num_steps - 1, Nat.sub_lt hpos' Nat.one_pos⟩ := by
        simpa [hidx, Fin.cases_succ]
      simpa [hpos, Nat.add_sub_cancel_right, hcases] using hw
  termination := w.termination

end GCRWitnessFrom

-- ============================================================================
-- MAXIMAL WITNESS SELECTION
-- ============================================================================

/--
Any weakly cohesive witness has β bounded by the number of candidates.
-/
lemma witness_beta_le_candidates {inst : ABCInstance V C k} {W : Finset C} {active : Finset V}
    (w : WeaklyCohesiveWitness V C inst W active) :
    w.β ≤ inst.candidates.card := by
  classical
  obtain ⟨i, hi⟩ := w.S_nonempty
  have hβ : w.β ≤ (inst.approves i ∩ w.T).card := w.S_approves i hi
  have hsubset : inst.approves i ∩ w.T ⊆ w.T := by
    intro c hc
    exact (Finset.mem_inter.mp hc).2
  have hT : w.T.card ≤ inst.candidates.card := by
    exact card_le_card w.T_candidates
  have hβT : w.β ≤ w.T.card := le_trans hβ (card_le_card hsubset)
  exact le_trans hβT hT

/--
If any witness exists, there is one with maximal β.
-/
lemma exists_max_witness {inst : ABCInstance V C k} (W : Finset C) (active : Finset V)
    (hexists : ∃ (_ : WeaklyCohesiveWitness V C inst W active), True) :
    ∃ w : WeaklyCohesiveWitness V C inst W active,
      ∀ w' : WeaklyCohesiveWitness V C inst W active, w'.β ≤ w.β := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ w : WeaklyCohesiveWitness V C inst W active, w.β ≥ n
  have hP1 : P 1 := by
    rcases hexists with ⟨w, _⟩
    exact ⟨w, w.β_pos⟩
  have hQ : ∃ n, ¬ P (n + 1) := by
    refine ⟨inst.candidates.card, ?_⟩
    intro hP
    rcases hP with ⟨w, hβ⟩
    have hbound : w.β ≤ inst.candidates.card := witness_beta_le_candidates w
    omega
  let n0 := Nat.find hQ
  have hQn0 : ¬ P (n0 + 1) := Nat.find_spec hQ
  have hn0_pos : 0 < n0 := by
    by_contra hn0
    have hn0' : n0 = 0 := Nat.eq_zero_of_not_pos hn0
    have : ¬ P 1 := by simpa [hn0'] using hQn0
    exact this hP1
  have hPn0 : P n0 := by
    have hpred : n0 - 1 < n0 := by omega
    have hnotQ : ¬ (¬ P n0) := by
      have := Nat.find_min hQ hpred
      simpa [P, Nat.sub_add_cancel (Nat.succ_le_iff.2 hn0_pos)] using this
    exact not_not.mp hnotQ
  rcases hPn0 with ⟨wmax, hwmax⟩
  refine ⟨wmax, ?_⟩
  intro w'
  have hle : w'.β ≤ n0 := by
    have hnot : ¬ w'.β ≥ n0 + 1 := by
      intro hge
      exact hQn0 ⟨w', hge⟩
    have hlt : w'.β < n0 + 1 := lt_of_not_ge hnot
    exact (Nat.lt_succ_iff).1 hlt
  exact le_trans hle hwmax

-- ============================================================================
-- EXISTENCE OF GCR OUTCOME
-- ============================================================================

/--
Active sets strictly shrink when removing a nonempty subset.
-/
lemma active_after_card_lt {active S : Finset V} (hS : S ⊆ active) (hS_nonempty : S.Nonempty) :
    (active \ S).card < active.card := by
  classical
  have hcard : (active \ S).card = active.card - S.card :=
    card_sdiff_of_subset hS
  have hS_card : 0 < S.card := Finset.card_pos.mpr hS_nonempty
  have hS_le : S.card ≤ active.card := card_le_card hS
  omega

private def zeroWitness {inst : ABCInstance V C k} (W : Finset C) (active : Finset V)
    (term : ∀ (_ : WeaklyCohesiveWitness V C inst W active), False) :
    GCRWitnessFrom V C inst W active :=
  { num_steps := 0
    steps := fun i => (Fin.elim0 i)
    initial_committee := by intro h; cases h
    initial_active := by intro h; cases h
    committee_linked := by intro t h; exact (Fin.elim0 t)
    active_linked := by intro t h; exact (Fin.elim0 t)
    final_committee := W
    final_active := active
    final_committee_correct := by simp
    final_active_correct := by simp
    termination := term }

theorem exists_gcr_witness_from {inst : ABCInstance V C k} :
    ∀ W active, W ⊆ inst.candidates → active ⊆ inst.voters →
      ∃ (_ : GCRWitnessFrom V C inst W active), True := by
  classical
  intro W active hW hactive
  refine (Nat.rec
    (motive := fun n =>
      ∀ W active, active.card ≤ n →
        W ⊆ inst.candidates → active ⊆ inst.voters →
        ∃ w : GCRWitnessFrom V C inst W active, True)
    ?base ?step (active.card)) W active (le_rfl) hW hactive
  · intro W active hcard hW hactive
    have hactive_empty : active = ∅ := by
      apply Finset.card_eq_zero.mp
      exact Nat.le_zero.mp hcard
    have hterm : ∀ w : WeaklyCohesiveWitness V C inst W active, False := by
      intro w
      have hS_empty : w.S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have : x ∈ active := w.S_active hx
        simpa [hactive_empty] using this
      exact w.S_nonempty.ne_empty hS_empty
    exact ⟨zeroWitness W active hterm, trivial⟩
  · intro n ih W active hcard hW hactive
    by_cases hexists : ∃ w : WeaklyCohesiveWitness V C inst W active, True
    · rcases exists_max_witness W active hexists with ⟨wmax, hmax⟩
      let step : GCRStep V C inst := {
        committee_before := W
        active_before := active
        S := wmax.S
        T := wmax.T
        β := wmax.β
        S_active := wmax.S_active
        T_candidates := wmax.T_candidates
        T_nonempty := wmax.T_nonempty
        S_nonempty := wmax.S_nonempty
        β_pos := wmax.β_pos
        S_large := wmax.S_large
        S_approves := wmax.S_approves
        β_maximal := hmax
      }
      have hW' : step.committee_after ⊆ inst.candidates := by
        exact GCRStep.committee_after_subset step hW
      have hactive' : step.active_after ⊆ inst.voters := by
        exact GCRStep.active_after_subset step hactive
      have hcard_lt : step.active_after.card < active.card := by
        dsimp [GCRStep.active_after, step]
        exact active_after_card_lt (active := active) (S := wmax.S)
          wmax.S_active wmax.S_nonempty
      have hcard' : step.active_after.card ≤ n := by
        have hcard_le : active.card ≤ n + 1 := hcard
        omega
      rcases ih _ _ hcard' hW' hactive' with ⟨w', _⟩
      refine ⟨GCRWitnessFrom.cons step w', trivial⟩
    · have hterm : ∀ w : WeaklyCohesiveWitness V C inst W active, False := by
        intro w
        exact (hexists ⟨w, trivial⟩)
      exact ⟨zeroWitness W active hterm, trivial⟩

/--
Convert a witness from the initial state to a standard `GCRWitness`.
-/
def GCRWitnessFrom.toGCRWitness {inst : ABCInstance V C k}
    (w : GCRWitnessFrom V C inst ∅ inst.voters) : GCRWitness V C inst :=
  { num_steps := w.num_steps
    steps := w.steps
    initial_committee := w.initial_committee
    initial_active := w.initial_active
    committee_linked := w.committee_linked
    active_linked := w.active_linked
    final_committee := w.final_committee
    final_active := w.final_active
    final_committee_correct := by
      simpa using w.final_committee_correct
    final_active_correct := by
      simpa using w.final_active_correct
    termination := w.termination }

/--
There exists a GCR outcome for any instance.
-/
theorem exists_gcr_outcome (inst : ABCInstance V C k) :
    ∃ W, is_gcr_outcome inst W := by
  classical
  rcases exists_gcr_witness_from (inst := inst) ∅ inst.voters (by simp) (by simp) with ⟨w, _⟩
  refine ⟨w.final_committee, ?_⟩
  refine ⟨w.toGCRWitness, ?_⟩
  rfl

/--
There exists a committee satisfying FJR for any instance.
-/
theorem exists_fjr_committee (inst : ABCInstance V C k) :
    ∃ W, inst.is_fjr W := by
  rcases exists_gcr_outcome inst with ⟨W, hW⟩
  exact ⟨W, gcr_outcome_satisfies_fjr inst W hW⟩

end ABCInstance
