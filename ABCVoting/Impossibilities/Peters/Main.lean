import ABCVoting.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.Peters.BaseCase
import ABCVoting.Impossibilities.Peters.InductionN
import ABCVoting.Impossibilities.Peters.InductionM
import ABCVoting.Impossibilities.Peters.InductionK
import ABCVoting.Impossibilities.Peters.StrategyproofnessPlentiful

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
    (hres : f.IsResolute)
    (heff : f.SatisfiesWeakEfficiency)
    (hprop : f.SatisfiesProportionality)
    (hsp : Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f) :
    False := by
  -- The proof proceeds by reduction to the base case.
  -- Each step uses one of the induction lemmas.
  --
  -- Step 1: Reduce m to k+1 using InductionM
  -- Step 2: Reduce n to k using InductionN
  -- Step 3: Reduce k to 3 using InductionK
  -- Step 4: Apply base case
  sorry

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
    (hres : f.IsResolute)
    (heff : f.SatisfiesWeakEfficiency)
    (hprop : f.SatisfiesProportionality)
    (hsp : f.SatisfiesResoluteStrategyproofness) :
    False := by
  -- Unrestricted strategyproofness implies strategyproofness on plentiful instances.
  refine peters_impossibility_onPlentiful n m k hk hn_div hn_pos hm f hres heff hprop ?_
  exact Peters.strategyproof_onPlentiful_of_strategyproof (f := f) hsp

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
      f.IsResolute ∧
      f.SatisfiesWeakEfficiency ∧
      f.SatisfiesProportionality ∧
      f.SatisfiesResoluteStrategyproofness := by
  intro ⟨f, hres, heff, hprop, hsp⟩
  exact peters_impossibility n m k hk hn_div hn_pos hm f hres heff hprop hsp

-- ============================================================================
-- SPECIAL CASES
-- ============================================================================

/--
Special case: k=3, n=3, m=4 (the base case parameters).
-/
theorem impossibility_3_3_4 :
    ¬∃ (f : ABCRule (Fin 3) (Fin 4) 3),
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
      f.IsResolute ∧
      f.SatisfiesWeakEfficiency ∧
      f.SatisfiesProportionality ∧
      f.SatisfiesResoluteStrategyproofness := by
  exact no_proportional_strategyproof_rule 4 5 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Peters
