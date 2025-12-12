import ABCVoting.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness

open Finset BigOperators ABCInstance

/-!
# Induction on Number of Voters (Lemma 5 from Peters)

This file proves that if there exists a rule satisfying the axioms for qk voters,
then there also exists such a rule for k voters.

The construction works by "copying" each voter q times. Given an instance with
k voters, we create an instance with qk voters where each original voter is
replicated q times, then apply the large rule.
-/

namespace Peters.InductionN

variable {C : Type*} [DecidableEq C] {kc : ℕ}

-- ============================================================================
-- VOTER EXPANSION
-- ============================================================================

/--
Given an instance with k voters, create an instance with qk voters by
replicating each voter's ballot q times.

The mapping is: new voter i maps to original voter (i mod k).
-/
def expand_voters (k q : ℕ) (hk : 0 < k) (hq : 0 < q)
    (inst : ABCInstance (Fin k) C kc) :
    ABCInstance (Fin (q * k)) C kc where
  voters := Finset.univ.filter fun i => (⟨i.val % k, Nat.mod_lt i.val hk⟩ : Fin k) ∈ inst.voters
  candidates := inst.candidates
  approves := fun i => inst.approves ⟨i.val % k, Nat.mod_lt i.val hk⟩
  approves_subset := by
    intro v hv
    have hmapped :
        (⟨v.val % k, Nat.mod_lt v.val hk⟩ : Fin k) ∈ inst.voters := by
      simpa [Finset.mem_filter] using (Finset.mem_filter.1 hv).2
    exact inst.approves_subset _ hmapped
  voters_nonempty := by
    classical
    rcases inst.voters_nonempty with ⟨v0, hv0⟩
    have hq1 : 1 ≤ q := Nat.succ_le_iff.2 hq
    have hk_le : k ≤ q * k := by
      simpa [Nat.one_mul] using Nat.mul_le_mul_right k hq1
    let i0 : Fin (q * k) := ⟨v0.val, lt_of_lt_of_le v0.isLt hk_le⟩
    refine ⟨i0, ?_⟩
    have hmapped : (⟨i0.val % k, Nat.mod_lt i0.val hk⟩ : Fin k) = v0 := by
      apply Fin.ext
      simpa [i0, Nat.mod_eq_of_lt v0.isLt]
    show i0 ∈
        Finset.univ.filter fun i =>
          (⟨i.val % k, Nat.mod_lt i.val hk⟩ : Fin k) ∈ inst.voters
    simp [Finset.mem_filter, hmapped, hv0]
  k_pos := inst.k_pos
  k_le_m := inst.k_le_m

/--
The expanded instance has the same candidates.
-/
lemma expand_voters_candidates (k q : ℕ) (hk : 0 < k) (hq : 0 < q)
    (inst : ABCInstance (Fin k) C kc) :
    (expand_voters k q hk hq inst).candidates = inst.candidates := rfl

-- ============================================================================
-- INDUCED RULE
-- ============================================================================

/--
Given a rule for qk voters, induce a rule for k voters by expanding
the profile and applying the large rule.
-/
def induced_rule (kv q : ℕ) (hkv : 0 < kv) (hq : 0 < q) {kc : ℕ}
    (f : ABCRule (Fin (q * kv)) C kc) :
    ABCRule (Fin kv) C kc :=
  { apply := fun inst => f.apply (expand_voters kv q hkv hq inst)
    extensional := by
      intro inst inst' hv hc ha
      -- Extensionality follows from extensionality of f on the expanded instances.
      -- TODO: provide detailed proof.
      sorry }

-- ============================================================================
-- AXIOM PRESERVATION
-- ============================================================================

/--
If f is resolute, so is the induced rule.
-/
lemma induced_rule_resolute (kv q : ℕ) (hkv : 0 < kv) (hq : 0 < q) {kc : ℕ}
    (f : ABCRule (Fin (q * kv)) C kc) (hres : f.IsResolute) :
    (induced_rule kv q hkv hq f).IsResolute := by
  classical
  -- TODO: adapt proof to new ABCRule structure
  sorry

/--
If f satisfies weak efficiency, so does the induced rule.
-/
lemma induced_rule_weak_efficiency (kv q : ℕ) (hkv : 0 < kv) (hq : 0 < q) {kc : ℕ}
    (f : ABCRule (Fin (q * kv)) C kc)
    (heff : f.SatisfiesWeakEfficiency) :
    (induced_rule kv q hkv hq f).SatisfiesWeakEfficiency := by
  classical
  -- TODO: adapt proof to new ABCRule structure
  sorry

/--
If f satisfies proportionality, so does the induced rule (when m = k+1).

Key insight: A singleton party of size ≥ 1 in the k-voter instance becomes
a singleton party of size ≥ q in the qk-voter instance, which still satisfies
the proportionality threshold since q ≥ qk/k.
-/
lemma induced_rule_proportionality (kv q : ℕ) (hkv : 0 < kv) (hq : 0 < q) {kc : ℕ}
    (f : ABCRule (Fin (q * kv)) C kc)
    (hprop : f.SatisfiesProportionality) :
    (induced_rule kv q hkv hq f).SatisfiesProportionality := by
  classical
  -- TODO: adapt proof to new ABCRule structure
  sorry

/--
If f satisfies strategyproofness, so does the induced rule.

Key insight: A manipulation by voter i in the k-voter instance corresponds
to q manipulations in the qk-voter instance (one for each copy of i).
By strategyproofness, each manipulation cannot improve the outcome,
so the combined effect also cannot improve.
-/
lemma induced_rule_strategyproof (kv q : ℕ) (hkv : 0 < kv) (hq : 0 < q) {kc : ℕ}
    (f : ABCRule (Fin (q * kv)) C kc)
    (hsp : f.SatisfiesResoluteStrategyproofness) :
    (induced_rule kv q hkv hq f).SatisfiesResoluteStrategyproofness := by
  classical
  -- TODO: adapt proof to new ABCRule structure
  sorry

-- ============================================================================
-- MAIN INDUCTION LEMMA
-- ============================================================================

/--
Lemma 5 (Peters): For m = k+1, if there exists a rule satisfying the axioms
for qk voters, then there exists such a rule for k voters.
-/
theorem induction_n (kv q : ℕ) (hkv : 3 ≤ kv) (hq : 1 ≤ q) {kc : ℕ}
    (f : ABCRule (Fin (q * kv)) C kc)
    (hres : f.IsResolute)
    (heff : f.SatisfiesWeakEfficiency)
    (hprop : f.SatisfiesProportionality)
    (hsp : f.SatisfiesResoluteStrategyproofness) :
    ∃ (f' : ABCRule (Fin kv) C kc),
      f'.IsResolute ∧
      f'.SatisfiesWeakEfficiency ∧
      f'.SatisfiesProportionality ∧
      f'.SatisfiesResoluteStrategyproofness := by
  have hkv_pos : 0 < kv := Nat.lt_of_lt_of_le (by norm_num : 0 < 3) hkv
  have hq_pos : 0 < q := hq
  refine ⟨induced_rule kv q hkv_pos hq_pos f, ?_, ?_, ?_, ?_⟩
  · exact induced_rule_resolute kv q hkv_pos hq_pos f hres
  · exact induced_rule_weak_efficiency kv q hkv_pos hq_pos f heff
  · exact induced_rule_proportionality kv q hkv_pos hq_pos f hprop
  · exact induced_rule_strategyproof kv q hkv_pos hq_pos f hsp

end Peters.InductionN
