import ABCVoting.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.KluivingDeVriesVrijbergenBoixelEndriss.BaseCase
import ABCVoting.Impossibilities.KluivingDeVriesVrijbergenBoixelEndriss.InductionN
import ABCVoting.Impossibilities.KluivingDeVriesVrijbergenBoixelEndriss.InductionM
import ABCVoting.Impossibilities.KluivingDeVriesVrijbergenBoixelEndriss.InductionK

open Finset BigOperators ABCInstance

/-!
# Kluiving et al. Impossibility Theorem

This file states and proves the main impossibility theorem from Kluiving et al. (ECAI 2020):

NOTE: The formalized version uses a weaker efficiency axiom than in the paper (and thus the
result is stronger), but the proof of the paper in fact only uses the weaker axiom. The
weaker axiom ("dominating candidate efficiency") says that if candidate a dominates
candidate b (everyone who approves b also approves a, and at least one voter approves a
but not b), then every winning committee containing b must also contain a.

**Theorem:** For k ≥ 3, n divisible by k, and m ≥ k+1, there exists no ABC rule that satisfies
minimal proportionality, dominating candidate efficiency, and cautious strategyproofness.

The proof combines:
1. **Base case** (k=3, n=3, m=4): Direct impossibility via cautious strategyproofness
2. **Induction on m**: Reduce number of candidates using dummy candidate + DCE
3. **Induction on n**: Reduce number of voters by copying profiles
4. **Induction on k**: Reduce committee size using dummy voter/candidate
-/

namespace KluivingDeVriesVrijbergenBoixelEndriss

-- ============================================================================
-- MAIN IMPOSSIBILITY THEOREM
-- ============================================================================

/--
Kluiving et al.'s impossibility theorem.

For k ≥ 3, n divisible by k, and m ≥ k+1, there exists no ABC rule
that simultaneously satisfies:
- Dominating candidate efficiency
- Minimal proportionality
- Cautious strategyproofness
-/
theorem kluiving_impossibility
    (n m k : ℕ)
    (hk : k ≥ 3)
    (hn_div : k ∣ n)
    (hn_pos : 0 < n)
    (hm : m ≥ k + 1)
    (f : ABCRule (Fin n) (Fin m) k)
    (hwf : f.IsWellFormed)
    (heff : f.SatisfiesDominatingCandidateEfficiency)
    (hprop : f.SatisfiesMinimalProportionality)
    (hsp : f.SatisfiesCautiousStrategyproofness) :
    False := by
  -- Step 1: Reduce the number of candidates to `k+1` using repeated applications of
  -- `InductionM.induction_m`.
  let P : ℕ → Prop := fun x =>
    ∃ (g : ABCRule (Fin n) (Fin (x + 1)) k),
      g.IsWellFormed ∧
      g.SatisfiesDominatingCandidateEfficiency ∧
      g.SatisfiesMinimalProportionality ∧
      g.SatisfiesCautiousStrategyproofness

  have P_start : P (m - 1) := by
    have hm_pos : 1 ≤ m := by linarith
    have hsub : (m - 1) + 1 = m := Nat.sub_add_cancel hm_pos
    dsimp [P]
    have hgoal : ∃ (g : ABCRule (Fin n) (Fin ((m - 1) + 1)) k),
        g.IsWellFormed ∧
        g.SatisfiesDominatingCandidateEfficiency ∧
        g.SatisfiesMinimalProportionality ∧
        g.SatisfiesCautiousStrategyproofness :=
      hsub.symm ▸ (⟨f, hwf, heff, hprop, hsp⟩)
    exact hgoal

  have stepP : ∀ x, k ≤ x → P (x + 1) → P x := by
    intro x hx hx1
    rcases hx1 with ⟨g, gwf, geff, gprop, gsp⟩
    have hx' : k ≤ x + 1 := Nat.le_succ_of_le hx
    obtain ⟨g', gwf', geff', gprop', gsp'⟩ :=
      KluivingDeVriesVrijbergenBoixelEndriss.InductionM.induction_m n (x + 1) k hk hx' g gwf geff gprop gsp
    exact ⟨g', gwf', geff', gprop', gsp'⟩

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

  rcases P_k with ⟨f1, f1wf, f1eff, f1prop, f1sp⟩

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

  obtain ⟨f2, f2wf, f2eff, f2prop, f2sp⟩ :=
    KluivingDeVriesVrijbergenBoixelEndriss.InductionN.induction_n k q hk hq_one
      (by simpa [KluivingDeVriesVrijbergenBoixelEndriss.InductionN.Cand] using f1)
      (by simpa [KluivingDeVriesVrijbergenBoixelEndriss.InductionN.Cand] using f1wf)
      (by simpa [KluivingDeVriesVrijbergenBoixelEndriss.InductionN.Cand] using f1eff)
      (by simpa [KluivingDeVriesVrijbergenBoixelEndriss.InductionN.Cand] using f1prop)
      (by simpa [KluivingDeVriesVrijbergenBoixelEndriss.InductionN.Cand] using f1sp)

  -- Step 3: Reduce the committee size to `3` using `InductionK`.
  let R : ℕ → Prop := fun t =>
    ∃ (g : ABCRule (Fin t) (Fin (t + 1)) t),
      g.IsWellFormed ∧
      g.SatisfiesDominatingCandidateEfficiency ∧
      g.SatisfiesMinimalProportionality ∧
      g.SatisfiesCautiousStrategyproofness

  have Rk : R k := by
    simpa using ⟨f2, f2wf, f2eff, f2prop, f2sp⟩

  have stepR : ∀ t, 4 ≤ t → R t → R (t - 1) := by
    intro t ht hRt
    rcases hRt with ⟨g, gwf, geff, gprop, gsp⟩
    have ht_pos : 1 ≤ t := by linarith
    have h2 : 3 ≤ t - 1 := by
      have ht' : 3 < t := lt_of_lt_of_le (by decide) ht
      exact Nat.le_pred_of_lt ht'
    obtain ⟨g', g'wf, g'eff, g'prop, g'sp⟩ :=
      KluivingDeVriesVrijbergenBoixelEndriss.InductionK.induction_k (k := t - 1) h2
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
          convert geff using 1 <;> simp [hsub, hsub2])
        (by
          have hsub : (t - 1) + 1 = t := Nat.sub_add_cancel ht_pos
          have hsub2 : (t - 1) + 2 = t + 1 := by linarith
          convert gprop using 1 <;> simp [hsub, hsub2])
        (by
          have hsub : (t - 1) + 1 = t := Nat.sub_add_cancel ht_pos
          have hsub2 : (t - 1) + 2 = t + 1 := by linarith
          convert gsp using 1 <;> simp [hsub, hsub2])
    exact ⟨g', g'wf, g'eff, g'prop, g'sp⟩

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
          have ht : 4 ≤ 3 + d.succ := by linarith
          have hprev : R (3 + d) := stepR (3 + d.succ) ht h
          exact ih hprev
    exact descendR d₂ R_start

  rcases R3 with ⟨f3, f3wf, f3eff, f3prop, f3sp⟩

  -- Step 4: Apply the base case (k = 3, n = 3, m = 4).
  exact KluivingDeVriesVrijbergenBoixelEndriss.BaseCase.base_case_impossible f3 f3wf f3eff f3prop f3sp

/--
Alternative statement: the conjunction of axioms is unsatisfiable.
-/
theorem no_minimally_proportional_cautious_rule
    (n m k : ℕ)
    (hk : k ≥ 3)
    (hn_div : k ∣ n)
    (hn_pos : 0 < n)
    (hm : m ≥ k + 1) :
    ¬∃ (f : ABCRule (Fin n) (Fin m) k),
      f.IsWellFormed ∧
      f.SatisfiesDominatingCandidateEfficiency ∧
      f.SatisfiesMinimalProportionality ∧
      f.SatisfiesCautiousStrategyproofness := by
  intro ⟨f, hwf, heff, hprop, hsp⟩
  exact kluiving_impossibility n m k hk hn_div hn_pos hm f hwf heff hprop hsp

-- ============================================================================
-- SPECIAL CASES
-- ============================================================================

/--
Special case: k=3, n=3, m=4 (the base case parameters).
-/
theorem impossibility_3_3_4 :
    ¬∃ (f : ABCRule (Fin 3) (Fin 4) 3),
      f.IsWellFormed ∧
      f.SatisfiesDominatingCandidateEfficiency ∧
      f.SatisfiesMinimalProportionality ∧
      f.SatisfiesCautiousStrategyproofness := by
  exact no_minimally_proportional_cautious_rule 3 4 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/--
Special case: k=3, n=6, m=4 (twice as many voters).
-/
theorem impossibility_6_4_3 :
    ¬∃ (f : ABCRule (Fin 6) (Fin 4) 3),
      f.IsWellFormed ∧
      f.SatisfiesDominatingCandidateEfficiency ∧
      f.SatisfiesMinimalProportionality ∧
      f.SatisfiesCautiousStrategyproofness := by
  exact no_minimally_proportional_cautious_rule 6 4 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/--
Special case: k=4, n=4, m=5.
-/
theorem impossibility_4_5_4 :
    ¬∃ (f : ABCRule (Fin 4) (Fin 5) 4),
      f.IsWellFormed ∧
      f.SatisfiesDominatingCandidateEfficiency ∧
      f.SatisfiesMinimalProportionality ∧
      f.SatisfiesCautiousStrategyproofness := by
  exact no_minimally_proportional_cautious_rule 4 5 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end KluivingDeVriesVrijbergenBoixelEndriss
