/-
# Sequential Phragmén Satisfies Priceability

This file proves that Sequential Phragmén outcomes are priceable.
The price system is derived directly from the load distribution.

## Key Insight

In Sequential Phragmén, when candidate c is elected in round t with s-value s_t:
- Each supporter i's load increases from x_i to s_t
- The "payment" from voter i for candidate c is: s_t - x_i

This naturally yields a price system where:
- Total payment for c = Σ_{i ∈ N(c)} (s_t - x_i) = |N(c)| · s_t - Σ x_i = 1 (by s-formula)
- Total spending by voter i = final_load_i

## References
- Peters, Pierczyński, Skowron. "Proportional Participatory Budgeting with Cardinal Utilities"
- Brill, Freeman, Janson, Lackner. "Phragmén's Voting Methods and Justified Representation"
-/

import ABCVoting.Rules.SeqPhragmen.Defs
import ABCVoting.Axioms.Priceability

open Finset BigOperators

set_option linter.style.openClassical false

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- PRICE SYSTEM CONSTRUCTION
-- ============================================================================

/--
If c is in the committee, there exists a round where c was selected.
-/
lemma SeqPhragmenWitness.exists_round_of_mem_committee {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (c : C) (hc : c ∈ w.committee) :
    ∃ t : Fin w.num_rounds, (w.rounds t).selected = c := by
  simp only [committee, Finset.mem_image] at hc
  obtain ⟨t, _, ht⟩ := hc
  exact ⟨t, ht⟩

/--
Given a SeqPhragmenWitness and a candidate c in the committee, find the round
in which c was selected.
-/
noncomputable def SeqPhragmenWitness.round_of {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (c : C) (hc : c ∈ w.committee) : Fin w.num_rounds :=
  Classical.choose (w.exists_round_of_mem_committee c hc)

/--
The round selected for c indeed has c as its selected candidate.
-/
lemma SeqPhragmenWitness.round_of_spec {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (c : C) (hc : c ∈ w.committee) :
    (w.rounds (w.round_of c hc)).selected = c :=
  Classical.choose_spec (w.exists_round_of_mem_committee c hc)

/--
The price system derived from a Sequential Phragmén witness.

For each voter i and candidate c:
- If c was elected and i is a supporter of c:
  p_i(c) = s_t - start_loads_t(i)  (the load increase)
- Otherwise: p_i(c) = 0
-/
noncomputable def SeqPhragmenWitness.price_system {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) : PriceSystem V C :=
  fun i c =>
    if hc : c ∈ w.committee then
      if c ∈ inst.approves i then
        let t := w.round_of c hc
        (w.rounds t).selected_s - (w.rounds t).start_loads i
      else 0
    else 0

/--
The budget for the price system: maximum s-value across all rounds.
-/
noncomputable def SeqPhragmenWitness.budget {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) : ℝ :=
  if h : w.num_rounds > 0 then
    (Finset.univ : Finset (Fin w.num_rounds)).sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
      (fun t => (w.rounds t).selected_s)
  else 0

-- ============================================================================
-- HELPER LEMMAS ABOUT LOADS
-- ============================================================================

/--
Loads at round 0 are 0.
-/
lemma SeqPhragmenWitness.loads_zero_at_start {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (h : w.num_rounds > 0) (i : V) :
    (w.rounds ⟨0, h⟩).start_loads i = 0 := by
  have := w.initial_loads h
  exact congrFun this i

/--
For voters, end_loads equals either start_loads or selected_s.
-/
lemma SeqPhragmenWitness.end_loads_cases {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (t : Fin w.num_rounds) (i : V) (hi : i ∈ inst.voters) :
    (w.rounds t).end_loads i = (w.rounds t).selected_s ∨
    (w.rounds t).end_loads i = (w.rounds t).start_loads i := by
  have hevol := (w.rounds t).loads_evolution i hi
  by_cases h : (w.rounds t).selected ∈ inst.approves i
  · left; simp [hevol, h]
  · right; simp [hevol, h]

/--
All start_loads are non-negative for voters.
-/
lemma SeqPhragmenWitness.start_loads_nonneg {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (t : Fin w.num_rounds) (i : V) (hi : i ∈ inst.voters) :
    0 ≤ (w.rounds t).start_loads i := by
  -- Induction on the natural number value
  have h : ∀ n : ℕ, (hn : n < w.num_rounds) → 0 ≤ (w.rounds ⟨n, hn⟩).start_loads i := by
    intro n
    induction n with
    | zero =>
      intro h0
      rw [w.loads_zero_at_start (Nat.zero_lt_of_lt h0)]
    | succ m ih =>
      intro hm
      have hm' : m < w.num_rounds := Nat.lt_of_succ_lt hm
      have hlink := w.loads_linked ⟨m, hm'⟩ hm
      have hstart : (w.rounds ⟨m + 1, hm⟩).start_loads i = (w.rounds ⟨m, hm'⟩).end_loads i := by
        exact congrFun hlink.symm i
      rw [hstart]
      cases w.end_loads_cases ⟨m, hm'⟩ i hi with
      | inl h => rw [h]; exact (w.rounds ⟨m, hm'⟩).selected_s_nonneg
      | inr h => rw [h]; exact ih hm'
  exact h t.val t.isLt

/--
For supporters, start_loads ≤ selected_s.
-/
lemma SeqPhragmenWitness.supporter_load_le_s {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (t : Fin w.num_rounds) (i : V)
    (hi : i ∈ inst.supporters (w.rounds t).selected) :
    (w.rounds t).start_loads i ≤ (w.rounds t).selected_s :=
  (w.rounds t).supporter_loads_le_s i hi

-- ============================================================================
-- PRICE SYSTEM PROPERTIES
-- ============================================================================

/--
The price system has non-negative values.
-/
lemma SeqPhragmenWitness.price_nonneg {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) :
    w.price_system.nonneg inst := by
  intro i hi c
  unfold price_system
  split_ifs with hc happr
  · -- c in committee and i approves c
    let t := w.round_of c hc
    have hsel := w.round_of_spec c hc
    have hsup : i ∈ inst.supporters (w.rounds t).selected := by
      simp only [supporters, Finset.mem_filter]
      exact ⟨hi, hsel ▸ happr⟩
    have hle := w.supporter_load_le_s t i hsup
    have hcast : ((w.rounds t).start_loads i : ℝ) ≤ ((w.rounds t).selected_s : ℝ) := by
      exact_mod_cast hle
    linarith
  · -- c in committee but i doesn't approve c
    rfl
  · -- c not in committee
    rfl

/--
Voters only pay for candidates they approve (C1).
-/
lemma SeqPhragmenWitness.price_pays_only_approved {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) :
    w.price_system.pays_only_approved inst := by
  intro i _ c hc
  unfold price_system
  simp only [hc, ite_false, dite_eq_ite, ite_self]

/--
Non-elected candidates receive 0 payment (C4).
-/
lemma SeqPhragmenWitness.price_non_elected_unpaid {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) :
    w.price_system.non_elected_unpaid inst w.committee := by
  intro c hc
  simp only [Finset.mem_sdiff] at hc
  unfold PriceSystem.total_payment price_system
  simp only [hc.2, dite_false]
  exact Finset.sum_const_zero

/--
Total payment to an elected candidate equals 1 (C3).
-/
lemma SeqPhragmenWitness.price_elected_paid_one {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) :
    w.price_system.elected_paid_one inst w.committee := by
  intro c hc
  let t := w.round_of c hc
  have hsel := w.round_of_spec c hc
  unfold PriceSystem.total_payment price_system
  -- Simplify using hc
  simp only [hc, dite_true]
  -- Split the sum into supporters and non-supporters
  rw [← Finset.sum_filter_add_sum_filter_not inst.voters (c ∈ inst.approves ·)]
  -- Non-supporters contribute 0
  have hzero : ∑ x ∈ inst.voters.filter (c ∉ inst.approves ·),
      (if c ∈ inst.approves x then
        ↑(w.rounds (w.round_of c hc)).selected_s - ↑((w.rounds (w.round_of c hc)).start_loads x)
       else 0 : ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter] at hi
    simp [hi.2]
  rw [hzero, add_zero]
  -- Supporters contribute s - load
  have hsup_eq : inst.voters.filter (c ∈ inst.approves ·) = inst.supporters c := by
    ext i
    simp only [supporters, Finset.mem_filter]
  rw [hsup_eq]
  -- Simplify the sum over supporters
  have hsum : ∑ i ∈ inst.supporters c,
      (if c ∈ inst.approves i then
        ↑(w.rounds t).selected_s - ↑((w.rounds t).start_loads i)
       else 0 : ℝ) =
      ∑ i ∈ inst.supporters c, (((w.rounds t).selected_s : ℝ) - ((w.rounds t).start_loads i : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [supporters, Finset.mem_filter] at hi
    simp [hi.2]
  rw [hsum]
  -- Now use the s-formula
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul']
  -- The s-formula says: selected_s * |supporters| = 1 + Σ loads
  have hformula := (w.rounds t).s_formula
  -- We need to relate supporters of c to supporters of selected
  have hsup_c : inst.supporters c = inst.supporters (w.rounds t).selected := by
    rw [hsel]
  rw [hsup_c]
  -- Cast the formula to ℝ
  have hcast : ((w.rounds t).selected_s : ℝ) *
               (inst.supporters (w.rounds t).selected).card =
               1 + ∑ i ∈ inst.supporters (w.rounds t).selected, ↑((w.rounds t).start_loads i) := by
    have h := hformula
    simp only [s_value_num] at h
    have : ((w.rounds t).selected_s : ℝ) * (inst.supporters (w.rounds t).selected).card =
           ((w.rounds t).selected_s * (inst.supporters (w.rounds t).selected).card : ℚ) := by
      push_cast; ring
    rw [this]
    have : (1 : ℝ) + ∑ i ∈ inst.supporters (w.rounds t).selected, ↑((w.rounds t).start_loads i) =
           ((1 + ∑ i ∈ inst.supporters (w.rounds t).selected, (w.rounds t).start_loads i) : ℚ) := by
      push_cast; ring
    rw [this]
    exact_mod_cast h
  linarith

/--
The budget is non-negative.
-/
lemma SeqPhragmenWitness.budget_nonneg {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) : 0 ≤ w.budget := by
  unfold budget
  split_ifs with h
  · have hnonempty : (Finset.univ : Finset (Fin w.num_rounds)).Nonempty := by
      exact Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩
    have hmem : ⟨0, h⟩ ∈ (Finset.univ : Finset (Fin w.num_rounds)) := Finset.mem_univ _
    have hle := Finset.le_sup' (fun t => ((w.rounds t).selected_s : ℝ)) hmem
    have hs_nonneg : (0 : ℝ) ≤ (w.rounds ⟨0, h⟩).selected_s := by
      exact_mod_cast (w.rounds ⟨0, h⟩).selected_s_nonneg
    linarith
  · rfl

/--
All voter loads are bounded by the maximum s-value.
-/
lemma SeqPhragmenWitness.end_loads_le_max_s {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (h : w.num_rounds > 0) (t : Fin w.num_rounds) (i : V)
    (hi : i ∈ inst.voters) :
    ((w.rounds t).end_loads i : ℝ) ≤
    Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
      (fun s => ((w.rounds s).selected_s : ℝ)) := by
  have hevol := (w.rounds t).loads_evolution i hi
  by_cases hsup : (w.rounds t).selected ∈ inst.approves i
  · -- Voter is supporter: end_loads = selected_s ≤ max
    simp only [hevol, hsup, ↓reduceIte]
    exact Finset.le_sup' (fun s => ((w.rounds s).selected_s : ℝ)) (Finset.mem_univ t)
  · -- Voter is not supporter: end_loads = start_loads
    simp only [hevol, hsup, ↓reduceIte]
    -- start_loads is bounded by some s-value from an earlier round
    -- We prove this by strong induction on t.val
    have hbnd : ∀ n : ℕ, (hn : n < w.num_rounds) →
        ((w.rounds ⟨n, hn⟩).start_loads i : ℝ) ≤
        Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
          (fun s => ((w.rounds s).selected_s : ℝ)) := by
      intro n
      induction n with
      | zero =>
        intro hn
        rw [w.loads_zero_at_start h]
        simp only [Rat.cast_zero]
        have hs_nonneg : (0 : ℝ) ≤ (w.rounds ⟨0, h⟩).selected_s := by
          exact_mod_cast (w.rounds ⟨0, h⟩).selected_s_nonneg
        have hle := Finset.le_sup' (fun s => ((w.rounds s).selected_s : ℝ)) (Finset.mem_univ (⟨0, h⟩ : Fin w.num_rounds))
        linarith
      | succ m ih =>
        intro hm
        have hm' : m < w.num_rounds := Nat.lt_of_succ_lt hm
        have hlink := w.loads_linked ⟨m, hm'⟩ hm
        have hstart : (w.rounds ⟨m + 1, hm⟩).start_loads i = (w.rounds ⟨m, hm'⟩).end_loads i := by
          exact congrFun hlink.symm i
        rw [hstart]
        have hevol' := (w.rounds ⟨m, hm'⟩).loads_evolution i hi
        by_cases hsup' : (w.rounds ⟨m, hm'⟩).selected ∈ inst.approves i
        · simp only [hevol', hsup', ↓reduceIte]
          exact Finset.le_sup' (fun s => ((w.rounds s).selected_s : ℝ)) (Finset.mem_univ ⟨m, hm'⟩)
        · simp only [hevol', hsup', ↓reduceIte]
          exact ih hm'
    exact hbnd t.val t.isLt

/--
Final loads are bounded by the budget (maximum s-value).
-/
lemma SeqPhragmenWitness.final_loads_le_budget {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (i : V) (hi : i ∈ inst.voters) :
    (w.final_loads i : ℝ) ≤ w.budget := by
  unfold budget
  split_ifs with h
  · -- There are rounds
    have hfinal := w.final_loads_correct
    simp only [h, ↓reduceDIte] at hfinal
    rw [hfinal]
    -- End loads of last round are bounded by max s-value
    exact w.end_loads_le_max_s h ⟨w.num_rounds - 1, Nat.sub_lt h Nat.one_pos⟩ i hi
  · -- No rounds, final_loads = 0, budget = 0
    have hfinal := w.final_loads_correct
    simp only [h, ↓reduceDIte] at hfinal
    simp only [hfinal, Rat.cast_zero, le_refl]

/--
The budget equals the s-value of the last round (when there are rounds).
This follows from s-values being non-decreasing.
-/
lemma SeqPhragmenWitness.budget_eq_last_s {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (h : w.num_rounds > 0) :
    w.budget = (w.rounds ⟨w.num_rounds - 1, Nat.sub_lt h Nat.one_pos⟩).selected_s := by
  unfold budget
  simp only [h, ↓reduceDIte]
  let last : Fin w.num_rounds := ⟨w.num_rounds - 1, Nat.sub_lt h Nat.one_pos⟩
  -- The sup' of s-values equals the last one since they're non-decreasing
  apply le_antisymm
  · -- sup' ≤ last s-value
    apply Finset.sup'_le
    intro t _
    by_cases ht : t.val < w.num_rounds - 1
    · -- t < last: use non-decreasing property
      have hmono := w.s_values_nondecreasing t last ht
      exact_mod_cast hmono
    · -- t = last
      have heq : t.val = last.val := by
        simp only [last]
        omega
      have : t = last := Fin.ext heq
      rw [this]
  · -- last s-value ≤ sup'
    exact Finset.le_sup' (fun t => ((w.rounds t).selected_s : ℝ)) (Finset.mem_univ last)

/--
The payment at round t equals end_loads - start_loads.
-/
lemma SeqPhragmenWitness.payment_eq_load_diff {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (t : Fin w.num_rounds) (i : V) (hi : i ∈ inst.voters) :
    (if (w.rounds t).selected ∈ inst.approves i then
      ((w.rounds t).selected_s : ℝ) - (w.rounds t).start_loads i
    else 0) =
    (w.rounds t).end_loads i - (w.rounds t).start_loads i := by
  have hevol := (w.rounds t).loads_evolution i hi
  by_cases hsup : (w.rounds t).selected ∈ inst.approves i
  · simp only [hevol, hsup, ↓reduceIte]
  · simp only [hevol, hsup, ↓reduceIte]; ring

/--
With 0 rounds, the committee is empty.
-/
lemma SeqPhragmenWitness.committee_empty_of_no_rounds {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (h : w.num_rounds = 0) :
    w.committee = ∅ := by
  simp only [committee]
  have : (Finset.univ : Finset (Fin w.num_rounds)) = ∅ := by
    rw [Finset.univ_eq_empty_iff]
    rw [h]
    exact Fin.isEmpty
  simp only [this, Finset.image_empty]

/--
The sum over candidates of prices equals the sum over rounds.
-/
lemma SeqPhragmenWitness.sum_prices_eq_sum_rounds {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (i : V) :
    (∑ c ∈ inst.candidates,
      if hc : c ∈ w.committee then
        if c ∈ inst.approves i then
          ((w.rounds (w.round_of c hc)).selected_s : ℝ) -
          (w.rounds (w.round_of c hc)).start_loads i
        else 0
      else 0) =
    ∑ t : Fin w.num_rounds,
      (if (w.rounds t).selected ∈ inst.approves i then
        ((w.rounds t).selected_s : ℝ) - (w.rounds t).start_loads i
      else 0) := by
  -- The committee = image of selected over rounds
  -- Non-committee candidates contribute 0
  -- Reindex using the bijection between committee and rounds
  rw [← Finset.sum_filter_add_sum_filter_not inst.candidates (· ∈ w.committee)]
  -- Non-committee candidates contribute 0
  have hzero : ∑ c ∈ inst.candidates.filter (· ∉ w.committee),
      (if hc : c ∈ w.committee then
        if c ∈ inst.approves i then
          ((w.rounds (w.round_of c hc)).selected_s : ℝ) -
          (w.rounds (w.round_of c hc)).start_loads i
        else 0
      else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    simp only [Finset.mem_filter] at hc
    simp [hc.2]
  rw [hzero, add_zero]
  -- Now sum over committee members
  have hcomm_eq : inst.candidates.filter (· ∈ w.committee) = w.committee := by
    ext c
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun hc => w.committee_subset hc
  rw [hcomm_eq]
  -- Rewrite committee as image
  conv_lhs =>
    simp only [committee]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t _
    have hc : (w.rounds t).selected ∈ w.committee := by
      simp only [committee, Finset.mem_image]
      exact ⟨t, Finset.mem_univ t, rfl⟩
    -- Need to prove membership in expanded form
    have hc' : (w.rounds t).selected ∈ Finset.image (fun t => (w.rounds t).selected) Finset.univ := by
      simp only [Finset.mem_image]
      exact ⟨t, Finset.mem_univ t, rfl⟩
    rw [dif_pos hc']
    by_cases happr : (w.rounds t).selected ∈ inst.approves i
    · simp only [happr, ite_true]
      -- round_of selected = t by distinctness
      have hspec := w.round_of_spec (w.rounds t).selected hc
      have : w.round_of (w.rounds t).selected hc = t := by
        by_contra hne
        exact w.selected_distinct _ _ hne hspec
      rw [this]
    · simp only [happr, ite_false]
  · intro s _ t _ hst
    by_contra hne
    exact w.selected_distinct s t hne hst

/--
The sum of (end_loads - start_loads) over all rounds telescopes to final - initial.
-/
lemma SeqPhragmenWitness.sum_load_diffs_telescope {inst : ABCInstance V C k}
  (w : SeqPhragmenWitness V C inst) (i : V) (_hi : i ∈ inst.voters) (h : w.num_rounds > 0) :
    ∑ t : Fin w.num_rounds,
      (((w.rounds t).end_loads i : ℝ) - (w.rounds t).start_loads i) =
    (w.rounds ⟨w.num_rounds - 1, Nat.sub_lt h Nat.one_pos⟩).end_loads i := by
  -- Use Finset.sum_range_sub directly
  -- Define f(n) = cumulative load after round n-1, with f(0) = 0
  let f : ℕ → ℝ := fun n =>
    if hn : n > 0 ∧ n ≤ w.num_rounds then (w.rounds ⟨n - 1, by omega⟩).end_loads i
    else if n = 0 then 0
    else (w.rounds ⟨w.num_rounds - 1, Nat.sub_lt h Nat.one_pos⟩).end_loads i

  -- Prove f(0) = 0
  have hf0 : f 0 = 0 := by simp [f]

  -- Prove f(n) for valid n
  have hfn : ∀ n, (hn : 0 < n) → (hle : n ≤ w.num_rounds) → f n = (w.rounds ⟨n - 1, Nat.sub_one_lt_of_le hn hle⟩).end_loads i := by
    intro n hn hle
    simp only [f, hn, hle, and_self, ↓reduceDIte]

  -- Key: each term equals f(t+1) - f(t)
  have hterm : ∀ t : Fin w.num_rounds,
      (((w.rounds t).end_loads i : ℝ) - (w.rounds t).start_loads i) = f (t.val + 1) - f t.val := by
    intro t
    have ht1_pos : 0 < t.val + 1 := Nat.succ_pos _
    have ht1_le : t.val + 1 ≤ w.num_rounds := t.isLt
    rw [hfn (t.val + 1) ht1_pos ht1_le]
    simp only [Nat.add_sub_cancel]
    by_cases ht0 : t.val = 0
    · -- t = 0: f(0) = 0, start_loads(0) = 0
      have heq : t = ⟨0, h⟩ := Fin.ext ht0
      subst heq
      have hstart0 : (w.rounds ⟨0, h⟩).start_loads i = 0 := w.loads_zero_at_start h i
      simp [hf0, hstart0]
    · -- t > 0: f(t) = end_loads(t-1), start_loads(t) = end_loads(t-1) by linking
      have ht_pos : 0 < t.val := Nat.pos_of_ne_zero ht0
      have ht_le : t.val ≤ w.num_rounds := le_of_lt t.isLt
      rw [hfn t.val ht_pos ht_le]
      -- start_loads(t) = end_loads(t-1) by linking
      have hpred : t.val - 1 < w.num_rounds := by omega
      have hlink := w.loads_linked ⟨t.val - 1, hpred⟩ (by omega : t.val - 1 + 1 < w.num_rounds)
      have hstart : (w.rounds t).start_loads i = (w.rounds ⟨t.val - 1, hpred⟩).end_loads i := by
        have ht_eq : t = ⟨t.val - 1 + 1, by
          have := t.isLt
          have : t.val - 1 + 1 = t.val := Nat.sub_add_cancel (Nat.succ_le_of_lt ht_pos)
          have hlt : t.val - 1 + 1 < w.num_rounds := by simpa [this] using t.isLt
          exact hlt
        ⟩ := by
          apply Fin.ext
          simp [Nat.sub_add_cancel (Nat.succ_le_of_lt ht_pos)]
        conv_lhs => rw [ht_eq]
        exact congrFun hlink.symm i
      rw [hstart]

  -- Rewrite the sum using hterm
  have hsum_eq : ∑ t : Fin w.num_rounds, (((w.rounds t).end_loads i : ℝ) - (w.rounds t).start_loads i) =
      ∑ t : Fin w.num_rounds, (f (t.val + 1) - f t.val) := by
    apply Finset.sum_congr rfl
    intro t _
    exact hterm t
  rw [hsum_eq]

  -- Now use Finset.sum_range_sub
  rw [Fin.sum_univ_eq_sum_range (fun t => f (t + 1) - f t) w.num_rounds]
  rw [Finset.sum_range_sub f w.num_rounds]

  -- Simplify f(num_rounds) - f(0)
  have hne : 0 < w.num_rounds := h
  rw [hfn w.num_rounds hne (le_refl _), hf0, sub_zero]

/--
Elements present in `already_selected` at the start of a round were selected in a
previous round, hence they belong to the committee.
-/
lemma SeqPhragmenWitness.already_selected_subset_committee {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) :
    ∀ t : Fin w.num_rounds, (w.rounds t).already_selected ⊆ w.committee := by
  classical
  intro t
  -- Strong induction on the round index.
  have h : ∀ n (hn : n < w.num_rounds),
      (w.rounds ⟨n, hn⟩).already_selected ⊆ w.committee := by
    intro n
    induction n with
    | zero =>
      intro hn c hc
      have hpos : w.num_rounds > 0 := hn
      have hinit : (w.rounds ⟨0, hn⟩).already_selected = ∅ := by
        simpa using w.initial_already_selected hpos
      simpa [hinit] using hc
    | succ n ih =>
      intro hn c hc
      let tpred : Fin w.num_rounds := ⟨n, Nat.lt_of_succ_lt hn⟩
      have hlink := w.already_selected_linked tpred hn
      have hmem : c = (w.rounds tpred).selected ∨ c ∈ (w.rounds tpred).already_selected := by
        simpa [hlink, tpred, Finset.mem_union, Finset.mem_singleton] using hc
      rcases hmem with hsel | hprev
      · subst hsel
        have : (w.rounds tpred).selected ∈ w.committee := by
          simp [SeqPhragmenWitness.committee]
        simpa using this
      · have hsubset := ih (Nat.lt_of_succ_lt hn)
        exact hsubset hprev
  exact h t.val t.isLt

/--
Spending by voter i equals their final load.
The proof uses that each payment equals end_loads - start_loads,
and by loads_linked these telescope to final_load - 0.
-/
lemma SeqPhragmenWitness.spending_eq_final_load {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) (i : V) (hi : i ∈ inst.voters) :
    w.price_system.spending inst i = w.final_loads i := by
  unfold PriceSystem.spending price_system
  by_cases h : w.num_rounds > 0
  · rw [w.sum_prices_eq_sum_rounds i]
    -- Rewrite each term as end - start using payment_eq_load_diff
    conv_lhs =>
      congr
      · skip
      · ext t
        rw [w.payment_eq_load_diff t i hi]
    -- Now use telescoping
    rw [w.sum_load_diffs_telescope i hi h]
    -- final_loads = end_loads of last round
    have hfinal := w.final_loads_correct
    simp only [h, ↓reduceDIte] at hfinal
    rw [hfinal]
  · -- No rounds: spending = 0, final_load = 0
    simp only [not_lt, Nat.le_zero] at h
    have hfinal := w.final_loads_correct
    simp only [h, not_lt_zero', ↓reduceDIte] at hfinal
    have hcomm_empty := w.committee_empty_of_no_rounds h
    have : ∀ c, c ∉ w.committee := by simp [hcomm_empty]
    simp only [this, dite_false, Finset.sum_const_zero, hfinal, Rat.cast_zero]

/--
Voters stay within budget (C2).
-/
lemma SeqPhragmenWitness.price_within_budget {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) :
    w.price_system.within_budget inst w.budget := by
  intro i hi
  calc w.price_system.spending inst i
      = w.final_loads i := w.spending_eq_final_load i hi
    _ ≤ w.budget := w.final_loads_le_budget i hi

/--
Exhaustiveness: no group can afford a non-elected candidate (C5).

The key insight is:
1. For c ∉ committee, c was never selected
2. In the last round, minimality gives: s_last * |N_c| ≤ 1 + Σ start_loads_i
3. Since loads are non-decreasing: Σ start_loads_i ≤ Σ final_loads_i
4. Since budget = s_last and spending = final_load:
   budget * |N_c| ≤ 1 + Σ spending_i
   Σ (budget - spending_i) ≤ 1
-/
lemma SeqPhragmenWitness.price_exhaustive {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) :
    w.price_system.exhaustive inst w.committee w.budget := by
  classical
  intro c hc
  rcases Finset.mem_sdiff.mp hc with ⟨hcand, hnot_comm⟩
  by_cases hpos : w.num_rounds > 0
  · -- There is at least one round; use the last round's minimality.
    let last : Fin w.num_rounds := ⟨w.num_rounds - 1, Nat.sub_lt hpos Nat.one_pos⟩
    by_cases hsup : (inst.supporters c).Nonempty
    · -- Non-empty supporter set: apply minimality inequality.
      have hnot_already : c ∉ (w.rounds last).already_selected := by
        intro hmem
        have hsubset := (w.already_selected_subset_committee last) hmem
        exact hnot_comm hsubset
      have hmin := (w.rounds last).selected_minimal c
        (by exact Finset.mem_sdiff.mpr ⟨hcand, hnot_already⟩) hsup
      have hminR : ((w.rounds last).selected_s : ℝ) * (inst.supporters c).card ≤
          (inst.s_value_num (w.rounds last).start_loads c : ℝ) := by
        exact_mod_cast hmin
      have hnum : (inst.s_value_num (w.rounds last).start_loads c : ℝ) =
          (1 : ℝ) + ∑ i ∈ inst.supporters c, ((w.rounds last).start_loads i : ℝ) := by
        simp [s_value_num]
      have hminR' : ((w.rounds last).selected_s : ℝ) * (inst.supporters c).card ≤
          1 + ∑ i ∈ inst.supporters c, ((w.rounds last).start_loads i : ℝ) := by
        simpa [hnum] using hminR
      have hfinal_fun : w.final_loads = (w.rounds last).end_loads := by
        have h := w.final_loads_correct
        simpa [hpos] using h
      have hstart_le_final :
          ∑ i ∈ inst.supporters c, ((w.rounds last).start_loads i : ℝ) ≤
            ∑ i ∈ inst.supporters c, (w.final_loads i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi_voters : i ∈ inst.voters := (Finset.mem_filter.mp hi).1
        have hleQ := (w.rounds last).loads_nondecreasing i hi_voters
        have hleR : ((w.rounds last).start_loads i : ℝ) ≤ ((w.rounds last).end_loads i : ℝ) :=
          by exact_mod_cast hleQ
        have hfinal_i : (w.final_loads i : ℝ) = ((w.rounds last).end_loads i : ℝ) := by
          have := congrArg (fun f => f i) hfinal_fun
          simpa using this
        simpa [hfinal_i] using hleR
      have hmin_final : ((w.rounds last).selected_s : ℝ) * (inst.supporters c).card ≤
          1 + ∑ i ∈ inst.supporters c, (w.final_loads i : ℝ) := by
        linarith
      have hbudget : w.budget = ((w.rounds last).selected_s : ℝ) := w.budget_eq_last_s hpos
      have hsum_unspent :
          ∑ i ∈ inst.supporters c, w.price_system.unspent inst w.budget i =
            ((w.rounds last).selected_s : ℝ) * (inst.supporters c).card -
              ∑ i ∈ inst.supporters c, (w.final_loads i : ℝ) := by
        calc
          ∑ i ∈ inst.supporters c, w.price_system.unspent inst w.budget i
              = ∑ i ∈ inst.supporters c, (w.budget - w.price_system.spending inst i) := by
                  simp [PriceSystem.unspent]
          _ = ∑ i ∈ inst.supporters c, (w.budget - w.final_loads i) := by
                apply Finset.sum_congr rfl
                intro i hi
                have hi_voters : i ∈ inst.voters := (Finset.mem_filter.mp hi).1
                simp [w.spending_eq_final_load i hi_voters]
          _ = w.budget * (inst.supporters c).card -
                ∑ i ∈ inst.supporters c, (w.final_loads i : ℝ) := by
                simp [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]
          _ = ((w.rounds last).selected_s : ℝ) * (inst.supporters c).card -
                ∑ i ∈ inst.supporters c, (w.final_loads i : ℝ) := by
                simp [hbudget]
      calc
        ∑ i ∈ inst.supporters c, w.price_system.unspent inst w.budget i
            = ((w.rounds last).selected_s : ℝ) * (inst.supporters c).card -
                ∑ i ∈ inst.supporters c, (w.final_loads i : ℝ) := hsum_unspent
        _ ≤ 1 := by
            have := hmin_final
            linarith
    · -- No supporters: sum is 0.
      have hsup_empty : inst.supporters c = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsup
      simp [hsup_empty, PriceSystem.unspent]
  · -- No rounds: budget and loads are 0.
    simp only [not_lt, Nat.le_zero] at hpos
    have hbudget : w.budget = 0 := by
      unfold SeqPhragmenWitness.budget
      simp [hpos]
    have hfinal_fun : w.final_loads = fun _ => 0 := by
      have h := w.final_loads_correct
      simpa [hpos] using h
    calc
      ∑ i ∈ inst.supporters c, w.price_system.unspent inst w.budget i
          = ∑ i ∈ inst.supporters c, (0 - 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hi_voters : i ∈ inst.voters := (Finset.mem_filter.mp hi).1
              have hspend := w.spending_eq_final_load i hi_voters
              have hfinal_i : w.final_loads i = 0 := by
                have := congrArg (fun f => f i) hfinal_fun
                simpa using this
              simp [PriceSystem.unspent, hbudget, hspend, hfinal_i]
      _ = 0 := by simp
      _ ≤ (1 : ℝ) := by norm_num

-- ============================================================================
-- MAIN THEOREM
-- ============================================================================

/--
Every Sequential Phragmén outcome is priceable.
-/
theorem seq_phragmen_outcome_is_priceable {inst : ABCInstance V C k}
    (w : SeqPhragmenWitness V C inst) :
    inst.is_priceable w.committee := by
  use w.budget, w.price_system
  constructor
  · exact w.budget_nonneg
  · constructor
    · constructor
      · exact w.price_nonneg
      · constructor
        · exact w.price_pays_only_approved
        · constructor
          · exact w.price_within_budget
          · constructor
            · exact w.price_elected_paid_one
            · exact w.price_non_elected_unpaid
    · exact w.price_exhaustive

/--
The Sequential Phragmén rule satisfies priceability.
-/
theorem seq_phragmen_satisfies_priceability :
    ∀ (inst : ABCInstance V C k) (W : Finset C),
      is_seq_phragmen_outcome inst W → inst.is_priceable W := by
  intro inst W ⟨w, hw⟩
  rw [← hw]
  exact seq_phragmen_outcome_is_priceable w

end ABCInstance
