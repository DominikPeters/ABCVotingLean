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
    by_cases hv : v.val < k
    · simp [extend_instance, hv] at h
      -- Original voter's approval is embedded candidates, not dummy
      exfalso
      have hmem :
          dummy_candidate k ∈
            (inst.approves ⟨v.val, hv⟩).map
              ⟨embed_candidate k, by
                intro c1 c2 heq
                simp only [embed_candidate, Fin.mk.injEq] at heq
                exact Fin.ext heq⟩ := by
        have : dummy_candidate k ∈ ({dummy_candidate k} : Finset (Fin (k + 2))) :=
          Finset.mem_singleton_self _
        simpa [h] using this
      rcases (Finset.mem_map.1 hmem) with ⟨c, _, hc⟩
      have hcVal : (embed_candidate k c).val = k + 1 := by
        simpa [dummy_candidate] using congrArg Fin.val hc
      have hcVal' : c.val = k + 1 := by
        simpa [embed_candidate] using hcVal
      exact (Nat.ne_of_lt c.isLt) hcVal'
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
        intro c1 c2 b hb1 hb2
        have hb1' :
            (if h : c1.val < k + 1 then some ⟨c1.val, h⟩ else none) = some b := by
          simpa [Option.mem_def] using hb1
        have hb2' :
            (if h : c2.val < k + 1 then some ⟨c2.val, h⟩ else none) = some b := by
          simpa [Option.mem_def] using hb2
        by_cases h1 : c1.val < k + 1
        · have hb1'' : (⟨c1.val, h1⟩ : Fin (k + 1)) = b := by
            simpa [h1] using hb1'
          by_cases h2 : c2.val < k + 1
          · have hb2'' : (⟨c2.val, h2⟩ : Fin (k + 1)) = b := by
              simpa [h2] using hb2'
            have : c1.val = c2.val := by
              have := congrArg Fin.val (hb1''.trans hb2''.symm)
              simpa using this
            exact Fin.ext this
          · have : (none : Option (Fin (k + 1))) = some b := by
              simpa [h2] using hb2'
            cases this
        · have : (none : Option (Fin (k + 1))) = some b := by
            simpa [h1] using hb1'
          cases this)}
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
