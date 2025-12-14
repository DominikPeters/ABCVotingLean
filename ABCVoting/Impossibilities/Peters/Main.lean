import ABCVoting.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.Peters.BaseCase
import ABCVoting.Impossibilities.Peters.InductionN
import ABCVoting.Impossibilities.Peters.InductionM
import ABCVoting.Impossibilities.Peters.InductionK
import ABCVoting.Impossibilities.Peters.RestrictToPlentiful

open Finset BigOperators ABCInstance

/-!
# Peters' Impossibility Theorem

This file states and proves the main impossibility theorem from Peters' paper
"Proportionality and Strategyproofness in Multiwinner Elections":

**Theorem:** For k ≥ 3, n divisible by k, and m ≥ k+1, there exists no resolute
ABC rule that satisfies weak efficiency, proportionality, and strategyproofness.

The proof combines:
1. **Base case** (k=3, n=3, m=4): Direct impossibility via strategyproofness chain
2. **Induction on m**: Reduce number of candidates using dummy candidate + weak efficiency
3. **Induction on n**: Reduce number of voters by copying profiles
4. **Induction on k**: Reduce committee size using dummy voter/candidate
-/

namespace Peters

-- ============================================================================
-- MAIN IMPOSSIBILITY THEOREM
-- ============================================================================

/--
Peters' impossibility theorem, stated with strategyproofness restricted to plentiful instances.

This matches Peters' convention of implicitly restricting the domain of the rule to profiles with
at least `k` approved candidates in total.
-/
theorem peters_impossibility_onPlentiful
    (n m k : ℕ)
    (hk : k ≥ 3)
    (hn_div : k ∣ n)
    (hn_pos : 0 < n)
    (hm : m ≥ k + 1)
    (f : ABCRule (Fin n) (Fin m) k)
    (hwf : IsWellFormedOnPlentiful f)
    (hres : f.IsResolute)
    (heff : f.SatisfiesWeakEfficiency)
    (hprop : f.SatisfiesProportionality)
    (hsp : Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f) :
    False := by
  -- Step 1: Reduce the number of candidates to `k+1` using repeated applications of
  -- `InductionM.induction_m` (which now preserves well-formedness on plentiful instances).
  let P : ℕ → Prop := fun x =>
    ∃ (g : ABCRule (Fin n) (Fin (x + 1)) k),
      IsWellFormedOnPlentiful g ∧
      g.IsResolute ∧
      g.SatisfiesWeakEfficiency ∧
      g.SatisfiesProportionality ∧
      Peters.SatisfiesResoluteStrategyproofnessOnPlentiful g

  have P_start : P (m - 1) := by
    have hm_pos : 1 ≤ m := by linarith
    have hsub : (m - 1) + 1 = m := Nat.sub_add_cancel hm_pos
    dsimp [P]
    -- Build the witness at candidate type (m-1)+1 via rewriting
    have hgoal : ∃ (g : ABCRule (Fin n) (Fin ((m - 1) + 1)) k),
        IsWellFormedOnPlentiful g ∧
        g.IsResolute ∧
        g.SatisfiesWeakEfficiency ∧
        g.SatisfiesProportionality ∧
        Peters.SatisfiesResoluteStrategyproofnessOnPlentiful g :=
      hsub.symm ▸ (⟨f, hwf, hres, heff, hprop, hsp⟩)
    exact hgoal

  have stepP : ∀ x, k ≤ x → P (x + 1) → P x := by
    intro x hx hx1
    rcases hx1 with ⟨g, gwf, gres, geff, gprop, gsp⟩
    have hx' : k ≤ x + 1 := Nat.le_succ_of_le hx
    obtain ⟨g', gwf', gres', geff', gprop', gsp'⟩ :=
      InductionM.induction_m n (x + 1) k hk hx' g gwf gres geff gprop gsp
    exact ⟨g', gwf', gres', geff', gprop', gsp'⟩

  have hk_le_m1 : k ≤ m - 1 := by
    have hk_lt_m : k < m := lt_of_lt_of_le (by linarith) hm
    exact Nat.le_pred_of_lt hk_lt_m
  let d₁ := (m - 1) - k
  have h_m1_eq : m - 1 = k + d₁ := (Nat.add_sub_of_le hk_le_m1).symm

  have P_k : P k := by
    have P_k_plus_d : P (k + d₁) := by simpa [h_m1_eq] using P_start
    -- descend d₁ times using `stepP`
    have descend : ∀ d, P (k + d) → P k := by
      intro d
      induction d with
      | zero =>
        intro h; simpa using h
      | succ d ih =>
        intro h
        have hk_le : k ≤ k + d := by linarith
        have hprev : P (k + d) := stepP (k + d) hk_le h
        exact ih hprev
    exact descend d₁ P_k_plus_d

  rcases P_k with ⟨f1, f1wf, f1res, f1eff, f1prop, f1sp⟩

  -- Step 2: Reduce the number of voters to `k` using `InductionN`.
  obtain ⟨q, hn_eq⟩ := hn_div
  have hn_eq' : n = q * k := by simpa [Nat.mul_comm] using hn_eq
  subst hn_eq'
  have hk_pos : 0 < k := by linarith
  have hq_pos : 0 < q := by
    have hmul : 0 < k * q := by simpa [Nat.mul_comm] using hn_pos
    have hq_zero_or_pos := Nat.eq_zero_or_pos q
    rcases hq_zero_or_pos with hq0 | hqpos
    · have : k * q = 0 := by simpa [hq0]
      linarith
    · exact hqpos
  have hq_one : 1 ≤ q := Nat.succ_le_of_lt hq_pos

  obtain ⟨f2, f2wf, f2res, f2eff, f2prop, f2sp⟩ :=
    InductionN.induction_n k q hk hq_one
      (by simpa [InductionN.Cand] using f1)
      (by simpa [InductionN.Cand] using f1wf)
      (by simpa [InductionN.Cand] using f1res)
      (by simpa [InductionN.Cand] using f1eff)
      (by simpa [InductionN.Cand] using f1prop)
      (by simpa [InductionN.Cand] using f1sp)

  -- Step 3: Reduce the committee size to `3` using `InductionK`.
  let R : ℕ → Prop := fun t =>
    ∃ (g : ABCRule (Fin t) (Fin (t + 1)) t),
      IsWellFormedOnPlentiful g ∧
      g.IsResolute ∧
      g.SatisfiesWeakEfficiency ∧
      g.SatisfiesProportionality ∧
      Peters.SatisfiesResoluteStrategyproofnessOnPlentiful g

  have Rk : R k := by
    simpa using ⟨f2, f2wf, f2res, f2eff, f2prop, f2sp⟩

  have stepR : ∀ t, 3 ≤ t → R t → R (t - 1) := by
    intro t ht hRt
    rcases hRt with ⟨g, gwf, gres, geff, gprop, gsp⟩
    have ht_pos : 1 ≤ t := by linarith
    have h2 : 2 ≤ t - 1 :=
      by
        have ht' : 2 < t := lt_of_lt_of_le (by decide) ht
        exact Nat.le_pred_of_lt ht'
    obtain ⟨g', g'wf, g'res, g'eff, g'prop, g'sp⟩ :=
      InductionK.induction_k (k := t - 1) h2
        (by
          have hsub : (t - 1) + 1 = t := Nat.sub_add_cancel ht_pos
          have hsub2 : (t - 1) + 2 = t + 1 := by linarith
          simpa [hsub, hsub2] using g)
        (by
          have hsub : (t - 1) + 1 = t := Nat.sub_add_cancel ht_pos
          have hsub2 : (t - 1) + 2 = t + 1 := by linarith
          convert gwf using 1 <;> simp [hsub, hsub2])
        (by
          have hsub : (t - 1) + 1 = t := Nat.sub_add_cancel ht_pos
          have hsub2 : (t - 1) + 2 = t + 1 := by linarith
          convert gres using 1 <;> simp [hsub, hsub2])
        (by
          have hsub : (t - 1) + 1 = t := Nat.sub_add_cancel ht_pos
          have hsub2 : (t - 1) + 2 = t + 1 := by linarith
          convert geff using 1 <;> simp [hsub, hsub2])
        (by
          have hsub : (t - 1) + 1 = t := Nat.sub_add_cancel ht_pos
          have hsub2 : (t - 1) + 2 = t + 1 := by linarith
          convert gprop using 1 <;> simp [hsub, hsub2])
        (by
          have hsub : (t - 1) + 1 = t := Nat.sub_add_cancel ht_pos
          have hsub2 : (t - 1) + 2 = t + 1 := by linarith
          convert gsp using 1 <;> simp [hsub, hsub2])
    exact ⟨g', g'wf, g'res, g'eff, g'prop, g'sp⟩

  let d₂ := k - 3
  have R3 : R 3 := by
    have R_start : R (3 + d₂) := by
      have hks : 3 + d₂ = k := Nat.add_sub_of_le hk
      simpa [hks] using Rk
    -- descend d₂ times
    have descendR : ∀ d, R (3 + d) → R 3 := by
      intro d
      induction d with
      | zero =>
          intro h; simpa using h
      | succ d ih =>
          intro h
          have ht : 3 ≤ 3 + d.succ := by linarith
          have hprev : R (3 + d) := stepR (3 + d.succ) ht h
          exact ih hprev
    exact descendR d₂ R_start

  rcases R3 with ⟨f3, f3wf, f3res, f3eff, f3prop, f3sp⟩

  -- Step 4: Apply the base case (k = 3, n = 3, m = 4).
  exact BaseCase.base_case_impossible f3 f3wf f3res f3prop f3sp

/--
**Peters' Impossibility Theorem**

For k ≥ 3, n divisible by k, and m ≥ k+1, there exists no resolute ABC rule
that simultaneously satisfies:
- Weak efficiency (don't elect unapproved candidates)
- Proportionality (on party-lists, singleton parties with ≥ n/k support get their candidate)
- Strategyproofness (no voter benefits from reporting a subset of true approvals)

**Proof strategy:**
1. Assume such a rule f exists for parameters (n, m, k)
2. Use Lemma 6 (induction on m) to reduce to m = k+1
3. Use Lemma 5 (induction on n) to reduce to n = k
4. Use Lemma 7 (induction on k) repeatedly to reduce to k = 3
5. Apply the base case (Lemma 4) for k=3, n=3, m=4 to get contradiction
-/
theorem peters_impossibility
    (n m k : ℕ)
    (hk : k ≥ 3)
    (hn_div : k ∣ n)
    (hn_pos : 0 < n)
    (hm : m ≥ k + 1)
    (f : ABCRule (Fin n) (Fin m) k)
    (hwf : f.IsWellFormed)
    (hres : f.IsResolute)
    (heff : f.SatisfiesWeakEfficiency)
    (hprop : f.SatisfiesProportionality)
    (hsp : f.SatisfiesResoluteStrategyproofness) :
    False := by
  -- Unrestricted axioms imply their plentiful-restricted versions.
  have hwf' := Peters.well_formed_onPlentiful_of_well_formed f hwf
  have hsp' := Peters.strategyproof_onPlentiful_of_strategyproof f hsp
  exact peters_impossibility_onPlentiful n m k hk hn_div hn_pos hm f hwf' hres heff hprop hsp'

/--
Alternative statement: The conjunction of axioms is unsatisfiable.
-/
theorem no_proportional_strategyproof_rule
    (n m k : ℕ)
    (hk : k ≥ 3)
    (hn_div : k ∣ n)
    (hn_pos : 0 < n)
    (hm : m ≥ k + 1) :
    ¬∃ (f : ABCRule (Fin n) (Fin m) k),
      f.IsWellFormed ∧
      f.IsResolute ∧
      f.SatisfiesWeakEfficiency ∧
      f.SatisfiesProportionality ∧
      f.SatisfiesResoluteStrategyproofness := by
  intro ⟨f, hwf, hres, heff, hprop, hsp⟩
  exact peters_impossibility n m k hk hn_div hn_pos hm f hwf hres heff hprop hsp

-- ============================================================================
-- SPECIAL CASES
-- ============================================================================

/--
Special case: k=3, n=3, m=4 (the base case parameters).
-/
theorem impossibility_3_3_4 :
    ¬∃ (f : ABCRule (Fin 3) (Fin 4) 3),
      f.IsWellFormed ∧
      f.IsResolute ∧
      f.SatisfiesWeakEfficiency ∧
      f.SatisfiesProportionality ∧
      f.SatisfiesResoluteStrategyproofness := by
  exact no_proportional_strategyproof_rule 3 4 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/--
Special case: k=3, n=6, m=4 (twice as many voters).
-/
theorem impossibility_6_4_3 :
    ¬∃ (f : ABCRule (Fin 6) (Fin 4) 3),
      f.IsWellFormed ∧
      f.IsResolute ∧
      f.SatisfiesWeakEfficiency ∧
      f.SatisfiesProportionality ∧
      f.SatisfiesResoluteStrategyproofness := by
  exact no_proportional_strategyproof_rule 6 4 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/--
Special case: k=4, n=4, m=5.
-/
theorem impossibility_4_5_4 :
    ¬∃ (f : ABCRule (Fin 4) (Fin 5) 4),
      f.IsWellFormed ∧
      f.IsResolute ∧
      f.SatisfiesWeakEfficiency ∧
      f.SatisfiesProportionality ∧
      f.SatisfiesResoluteStrategyproofness := by
  exact no_proportional_strategyproof_rule 4 5 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Peters
