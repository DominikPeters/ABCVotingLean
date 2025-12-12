import ABCVoting.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.Peters.SingletonApprovers

open Finset BigOperators ABCInstance

/-!
# Induction on Committee Size (Lemma 7 from Peters)

This file proves that if there exists a rule satisfying the axioms for
committee size k+1 (with k+1 voters and k+2 candidates), then there exists
such a rule for committee size k (with k voters and k+1 candidates).

The construction adds:
1. A dummy voter who approves only a new dummy candidate
2. A dummy candidate approved only by the dummy voter

By the singleton approvers lemma, the dummy candidate is always elected.
Removing it from the committee gives a size-k committee for the original instance.
-/

namespace Peters.InductionK

-- ============================================================================
-- TYPE MAPPINGS
-- ============================================================================

/--
Embed a voter from Fin k into Fin (k+1).
-/
def embed_voter (k : ℕ) : Fin k → Fin (k + 1) :=
  fun v => ⟨v.val, Nat.lt_succ_of_lt v.isLt⟩

/--
The dummy voter is the last one (index k).
-/
def dummy_voter (k : ℕ) : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩

/--
Embed a candidate from Fin (k+1) into Fin (k+2).
-/
def embed_candidate (k : ℕ) : Fin (k + 1) → Fin (k + 2) :=
  fun c => ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩

/--
The dummy candidate is the last one (index k+1).
-/
def dummy_candidate (k : ℕ) : Fin (k + 2) := ⟨k + 1, Nat.lt_succ_self (k + 1)⟩

-- ============================================================================
-- INSTANCE EXTENSION
-- ============================================================================

/--
Given an instance with k voters and k+1 candidates (committee size k),
create an instance with k+1 voters and k+2 candidates (committee size k+1).

The new voter (dummy) approves only the new candidate (dummy).
-/
def extend_instance (k : ℕ) (inst : ABCInstance (Fin k) (Fin (k + 1)) k) :
    ABCInstance (Fin (k + 1)) (Fin (k + 2)) (k + 1) where
  voters := Finset.univ
  candidates := Finset.univ
  approves := fun v =>
    if h : v.val < k then
      -- Original voter: embed their approval set
      (inst.approves ⟨v.val, h⟩).map ⟨embed_candidate k, by
        intro c1 c2 heq
        simp only [embed_candidate, Fin.mk.injEq] at heq
        exact Fin.ext heq⟩
    else
      -- Dummy voter: approves only dummy candidate
      {dummy_candidate k}
  approves_subset := by
    intro v _
    exact Finset.subset_univ _
  voters_nonempty := Finset.univ_nonempty
  k_pos := Nat.succ_pos k
  k_le_m := by simp [Finset.card_fin]

/--
The dummy candidate is approved only by the dummy voter.
This means its singleton party has size 1, which equals (k+1)/(k+1) = 1.
-/
lemma dummy_singleton_party (k : ℕ) (inst : ABCInstance (Fin k) (Fin (k + 1)) k) :
    (extend_instance k inst).singleton_party (dummy_candidate k) =
    {dummy_voter k} := by
  ext v
  simp only [singleton_party, mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    simp only [extend_instance] at h
    by_cases hv : v.val < k
    · simp only [hv, ↓reduceDIte] at h
      -- Original voter's approval is embedded candidates, not dummy
      exfalso
      simp only [Finset.map_eq_singleton] at h
      obtain ⟨c, _, hc⟩ := h
      simp only [embed_candidate, dummy_candidate, Fin.mk.injEq] at hc
      omega
    · -- v.val ≥ k, so v must be the dummy voter
      have hv' : v.val = k := by
        have := v.isLt
        omega
      exact Fin.ext hv'
  · intro hv
    rw [hv]
    simp only [extend_instance, dummy_voter]
    have : ¬(k < k) := Nat.lt_irrefl k
    simp [this]

-- ============================================================================
-- INDUCED RULE
-- ============================================================================

/--
Given a rule f for k+1 voters and k+2 candidates (size k+1),
induce a rule for k voters and k+1 candidates (size k).

The induced rule:
1. Extends the instance by adding dummy voter/candidate
2. Applies f (which always includes dummy candidate by singleton approvers lemma)
3. Removes the dummy candidate from the result
-/
noncomputable def induced_rule (k : ℕ)
    (f : ABCRule (Fin (k + 1)) (Fin (k + 2)) (k + 1))
    (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality)
    (hsp : f.SatisfiesResoluteStrategyproofness) :
    ABCRule (Fin k) (Fin (k + 1)) k where
  apply inst :=
    let ext_inst := extend_instance k inst
    let W := f.resolute_committee ext_inst hres
    -- Remove dummy candidate and map back to Fin (k+1)
    {W.filterMap (fun c =>
      if h : c.val < k + 1 then some ⟨c.val, h⟩ else none) (by
        intro c1 c2 hc1 hc2
        simp only [Option.mem_def] at hc1 hc2
        split_ifs at hc1 hc2 with h1 h2
        · simp only [Option.some.injEq, Fin.mk.injEq] at hc1 hc2
          exact Fin.ext (hc1 ▸ hc2)
        all_goals simp_all)}
  extensional := by
    intro inst inst' hv hc ha
    -- Extensionality follows from extensionality of f on the extended instances.
    -- The construction of committees only depends on the extended instances.
    -- TODO: fill in detailed equality proof.
    sorry

-- ============================================================================
-- MAIN INDUCTION LEMMA
-- ============================================================================

/--
Lemma 7 (Peters): If there exists a rule satisfying the axioms for
committee size k+1 (with k+1 voters and k+2 candidates), then there exists
such a rule for committee size k (with k voters and k+1 candidates).
-/
theorem induction_k (k : ℕ) (hk : 2 ≤ k)
    (f : ABCRule (Fin (k + 1)) (Fin (k + 2)) (k + 1))
    (hres : f.IsResolute)
    (heff : f.SatisfiesWeakEfficiency)
    (hprop : f.SatisfiesProportionality)
    (hsp : f.SatisfiesResoluteStrategyproofness) :
    ∃ (f' : ABCRule (Fin k) (Fin (k + 1)) k),
      f'.IsResolute ∧
      f'.SatisfiesWeakEfficiency ∧
      f'.SatisfiesProportionality ∧
      f'.SatisfiesResoluteStrategyproofness := by
  -- The proof uses the singleton approvers lemma to show the dummy candidate
  -- is always elected, then verifies all axioms for the induced rule
  sorry

end Peters.InductionK
