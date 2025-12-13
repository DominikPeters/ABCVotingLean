import ABCVoting.Basic
import ABCVoting.ABCRule
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- PAV (PROPORTIONAL APPROVAL VOTING) DEFINITIONS
-- ============================================================================

/--
Harmonic number: 1 + 1/2 + ... + 1/n
This represents the total "satisfaction" gain from having n approved candidates.
-/
def harmonic (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (1 : ℚ) / (i + 1)

/--
PAV score for a specific committee W: the sum of harmonic numbers of
approved candidates for each voter.

Formally: score(W) = ∑_{i ∈ voters} H(|W ∩ approves_i|)
where H is the harmonic number function.
-/
def pav_score (inst : ABCInstance V C k) (W : Finset C) : ℚ :=
  ∑ i ∈ inst.voters, harmonic (W ∩ inst.approves i).card

/--
A committee W is a PAV winner if:
1. It is a subset of candidates
2. It has size k
3. It maximizes the PAV score among all size-k subsets of candidates
-/
def is_pav_winner (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  W ⊆ inst.candidates ∧
  W.card = k ∧
  ∀ W' : Finset C, W' ⊆ inst.candidates → W'.card = k → inst.pav_score W' ≤ inst.pav_score W

-- ============================================================================
-- PAV SCORE PROPERTIES
-- ============================================================================

/--
The PAV score of a committee only depends on its intersection with candidates,
because voters only approve candidates from inst.candidates.
-/
lemma pav_score_inter_candidates (inst : ABCInstance V C k) (W : Finset C) :
    inst.pav_score W = inst.pav_score (W ∩ inst.candidates) := by
  unfold pav_score
  apply Finset.sum_congr rfl
  intro v hv
  -- For v ∈ voters, we have approves v ⊆ candidates
  have h_sub := inst.approves_subset v hv
  -- Prove the sets are equal: W ∩ approves v = W ∩ candidates ∩ approves v
  have h_eq : W ∩ inst.approves v = W ∩ inst.candidates ∩ inst.approves v := by
    ext c
    simp only [mem_inter]
    exact ⟨fun ⟨hcW, hca⟩ => ⟨⟨hcW, h_sub hca⟩, hca⟩, fun ⟨⟨hcW, _⟩, hca⟩ => ⟨hcW, hca⟩⟩
  simp only [h_eq]

-- ============================================================================
-- PAV AS AN ABC RULE
-- ============================================================================

/--
Helper lemma: PAV score depends only on voters and their approval ballots.
-/
lemma pav_score_extensional (inst inst' : ABCInstance V C k) (W : Finset C)
    (hv : inst.voters = inst'.voters)
    (ha : ∀ v ∈ inst.voters, inst.approves v = inst'.approves v) :
    inst.pav_score W = inst'.pav_score W := by
  unfold pav_score
  rw [hv]
  apply Finset.sum_congr rfl
  intro v hv_mem
  -- For v in voters, approves v is the same in both instances
  have hv_mem' : v ∈ inst.voters := hv ▸ hv_mem
  simp only [ha v hv_mem']

/--
PAV as an ABC voting rule.

Returns all committees of size k that maximize the PAV score.
This is an irresolute rule (may return multiple committees).
-/
noncomputable def PAV : ABCRule V C k where
  apply inst := inst.candidates.powersetCard k |>.filter (fun W =>
    ∀ W' ∈ inst.candidates.powersetCard k, inst.pav_score W' ≤ inst.pav_score W)
  extensional := by
    intro inst inst' hv hc ha
    ext W
    simp only [mem_filter, mem_powersetCard]
    constructor
    · intro ⟨⟨hW_sub, hW_card⟩, hW_max⟩
      refine ⟨⟨hc ▸ hW_sub, hW_card⟩, ?_⟩
      intro W' ⟨hW'_sub, hW'_card⟩
      rw [← pav_score_extensional inst inst' W' hv ha]
      rw [← pav_score_extensional inst inst' W hv ha]
      exact hW_max W' ⟨hc.symm ▸ hW'_sub, hW'_card⟩
    · intro ⟨⟨hW_sub, hW_card⟩, hW_max⟩
      refine ⟨⟨hc.symm ▸ hW_sub, hW_card⟩, ?_⟩
      intro W' ⟨hW'_sub, hW'_card⟩
      rw [pav_score_extensional inst inst' W' hv ha]
      rw [pav_score_extensional inst inst' W hv ha]
      exact hW_max W' ⟨hc ▸ hW'_sub, hW'_card⟩

/--
A committee is in PAV's output if and only if it is a PAV winner.
-/
lemma mem_PAV_iff (inst : ABCInstance V C k) (W : Finset C) :
    W ∈ PAV inst ↔ inst.is_pav_winner W := by
  unfold PAV is_pav_winner
  simp only [mem_filter, mem_powersetCard]
  constructor
  · intro ⟨⟨hW_sub, hW_card⟩, hW_max⟩
    refine ⟨hW_sub, hW_card, fun W' hW'_sub hW'_card => hW_max W' ⟨hW'_sub, hW'_card⟩⟩
  · intro ⟨hW_sub, hW_card, hW_max⟩
    refine ⟨⟨hW_sub, hW_card⟩, fun W' ⟨hW'_sub, hW'_card⟩ => hW_max W' hW'_sub hW'_card⟩

-- ============================================================================
-- HARMONIC FUNCTION LEMMAS
-- ============================================================================

/--
Each term in the harmonic sum is positive.
-/
lemma harmonic_term_pos (i : ℕ) : (0 : ℚ) < 1 / (i + 1) := by
  exact one_div_pos.mpr (by exact_mod_cast Nat.succ_pos i)

/--
Harmonic is weakly monotone: if m ≤ n then H(m) ≤ H(n).
-/
lemma harmonic_mono {m n : ℕ} (h : m ≤ n) : harmonic m ≤ harmonic n := by
  unfold harmonic
  gcongr

/--
Harmonic is strictly monotone: if m < n then H(m) < H(n).
-/
lemma harmonic_strict_mono {m n : ℕ} (h : m < n) : harmonic m < harmonic n := by
  unfold harmonic
  exact Finset.sum_lt_sum_of_subset (Finset.range_mono (le_of_lt h)) (Finset.mem_range.mpr h)
    (Finset.notMem_range_self) (harmonic_term_pos m) (fun j _ _ => le_of_lt (harmonic_term_pos j))

/--
Key identity: harmonic(n+1) - harmonic(n) = 1/(n+1)
-/
lemma harmonic_succ_sub (n : ℕ) : harmonic (n + 1) - harmonic n = 1 / (n + 1) := by
  simp only [harmonic, Finset.sum_range_succ, add_sub_cancel_left]

end ABCInstance
