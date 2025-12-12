import ABCVoting.Basic
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
1. It has size k
2. It maximizes the PAV score among all committees of size k
-/
def is_pav_winner (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  W.card = k ∧
  ∀ W' : Finset C, W'.card = k → inst.pav_score W' ≤ inst.pav_score W

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
