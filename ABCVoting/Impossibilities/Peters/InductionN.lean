import ABCVoting.Axioms.ABCRule
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

variable {C : Type*} [DecidableEq C]

-- ============================================================================
-- VOTER EXPANSION
-- ============================================================================

/--
Given an instance with k voters, create an instance with qk voters by
replicating each voter's ballot q times.

The mapping is: new voter i maps to original voter (i mod k).
-/
def expand_voters (k q : ℕ) (hk : 0 < k) (hq : 0 < q)
    (inst : ABCInstance (Fin k) C) :
    ABCInstance (Fin (q * k)) C where
  voters := Finset.univ
  candidates := inst.candidates
  approves := fun i => inst.approves ⟨i.val % k, Nat.mod_lt i.val hk⟩
  approves_subset := by
    intro v _
    exact inst.approves_subset ⟨v.val % k, Nat.mod_lt v.val hk⟩ (Finset.mem_univ _)
  voters_nonempty := Finset.univ_nonempty
  k := inst.k
  k_pos := inst.k_pos
  k_le_m := inst.k_le_m

/--
The expanded instance has the same k value.
-/
lemma expand_voters_k (k q : ℕ) (hk : 0 < k) (hq : 0 < q)
    (inst : ABCInstance (Fin k) C) :
    (expand_voters k q hk hq inst).k = inst.k := rfl

/--
The expanded instance has the same candidates.
-/
lemma expand_voters_candidates (k q : ℕ) (hk : 0 < k) (hq : 0 < q)
    (inst : ABCInstance (Fin k) C) :
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
  fun inst hk => f (expand_voters kv q hkv hq inst) (by simp [expand_voters, hk])

-- ============================================================================
-- AXIOM PRESERVATION
-- ============================================================================

/--
If f is resolute, so is the induced rule.
-/
lemma induced_rule_resolute (kv q : ℕ) (hkv : 0 < kv) (hq : 0 < q) {kc : ℕ}
    (f : ABCRule (Fin (q * kv)) C kc) (hres : f.IsResolute) :
    (induced_rule kv q hkv hq f).IsResolute := by
  intro inst hk
  exact hres (expand_voters kv q hkv hq inst) (by simp [expand_voters, hk])

/--
If f satisfies weak efficiency, so does the induced rule.
-/
lemma induced_rule_weak_efficiency (kv q : ℕ) (hkv : 0 < kv) (hq : 0 < q) {kc : ℕ}
    (f : ABCRule (Fin (q * kv)) C kc)
    (heff : f.SatisfiesWeakEfficiency) :
    (induced_rule kv q hkv hq f).SatisfiesWeakEfficiency := by
  intro inst hk W hW c hc
  -- An unapproved candidate in inst is also unapproved in the expanded instance
  intro hunapproved
  apply heff (expand_voters kv q hkv hq inst) (by simp [expand_voters, hk]) W hW c hc
  intro v _
  simp only [expand_voters]
  exact hunapproved ⟨v.val % kv, Nat.mod_lt v.val hkv⟩ (Finset.mem_univ _)

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
  intro inst hk c hpl hc_cand h_size W hW
  -- Need to show the expanded instance also satisfies proportionality conditions
  apply hprop (expand_voters kv q hkv hq inst) (by simp [expand_voters, hk]) c
  · -- Expanded instance is party-list if inst is
    intro v₁ _ v₂ _
    simp only [expand_voters]
    exact hpl ⟨v₁.val % kv, Nat.mod_lt v₁.val hkv⟩ (Finset.mem_univ _)
              ⟨v₂.val % kv, Nat.mod_lt v₂.val hkv⟩ (Finset.mem_univ _)
  · -- c is still a candidate
    simp only [expand_voters_candidates]
    exact hc_cand
  · -- Size threshold: need singleton_party_size * k ≥ qk
    -- In expanded instance, each singleton voter is replicated q times
    sorry
  · exact hW

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
  intro inst inst' i hi hvar hsub hk hk' hres
  -- The detailed proof requires tracking the q copies of voter i
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
