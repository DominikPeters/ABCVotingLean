import ABCVoting.Axioms.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness

open Finset BigOperators ABCInstance

/-!
# Base Case: k=3, n=3, m=4 Impossibility

This file proves the base case of Peters' impossibility theorem:
There is no resolute ABC rule for 3 voters, 4 candidates, and committee size 3
that satisfies weak efficiency, proportionality, and strategyproofness.

The proof constructs 15 specific profiles and shows that strategyproofness
leads to a contradiction.
-/

namespace Peters.BaseCase

-- ============================================================================
-- TYPE DEFINITIONS FOR BASE CASE
-- ============================================================================

/-- Voters: 0, 1, 2 -/
abbrev V := Fin 3

/-- Candidates: a=0, b=1, c=2, d=3 -/
abbrev C := Fin 4

/-- Notation for candidates -/
def a : C := 0
def b : C := 1
def c : C := 2
def d : C := 3

/-- Committee size -/
def k : ℕ := 3

-- ============================================================================
-- BALLOT AND PROFILE HELPERS
-- ============================================================================

/-- A ballot (approval set) -/
abbrev Ballot := Finset C

/-- Construct a ballot from a list of candidates -/
def ballot (cs : List C) : Ballot := cs.toFinset

/-- A profile assigns each voter a ballot -/
abbrev Profile := V → Ballot

/-- The standard instance with all voters and all candidates -/
def mk_instance (P : Profile) : ABCInstance V C where
  voters := Finset.univ
  candidates := Finset.univ
  approves := P
  approves_subset := by intro v _; exact Finset.subset_univ _
  voters_nonempty := by simp [Finset.univ_nonempty]
  k := k
  k_pos := by norm_num [k]
  k_le_m := by simp [k, Finset.card_fin]

-- ============================================================================
-- PROFILE DEFINITIONS
-- ============================================================================

/-!
We define the 15 profiles from Peters' proof.
Using notation: {a,b} = ballot [a, b], etc.

The profiles form a chain where each transition is a manipulation
(one voter reporting a subset of their true ballot).
-/

/-- P₁ = (ab, c, d): Voter 0 approves {a,b}, voter 1 approves {c}, voter 2 approves {d} -/
def P1 : Profile
  | 0 => ballot [a, b]
  | 1 => ballot [c]
  | 2 => ballot [d]

/-- P₁.₅ = (ab, ac, d) -/
def P1_5 : Profile
  | 0 => ballot [a, b]
  | 1 => ballot [a, c]
  | 2 => ballot [d]

/-- P₂ = (b, ac, d) -/
def P2 : Profile
  | 0 => ballot [b]
  | 1 => ballot [a, c]
  | 2 => ballot [d]

/-- P₂.₅ = (b, ac, cd) -/
def P2_5 : Profile
  | 0 => ballot [b]
  | 1 => ballot [a, c]
  | 2 => ballot [c, d]

/-- P₃ = (b, a, cd) -/
def P3 : Profile
  | 0 => ballot [b]
  | 1 => ballot [a]
  | 2 => ballot [c, d]

/-- P₃.₅ = (b, ad, cd) -/
def P3_5 : Profile
  | 0 => ballot [b]
  | 1 => ballot [a, d]
  | 2 => ballot [c, d]

/-- P₄ = (b, ad, c) -/
def P4 : Profile
  | 0 => ballot [b]
  | 1 => ballot [a, d]
  | 2 => ballot [c]

/-- P₄.₅ = (b, ad, ac) -/
def P4_5 : Profile
  | 0 => ballot [b]
  | 1 => ballot [a, d]
  | 2 => ballot [a, c]

/-- P₅ = (b, d, ac) -/
def P5 : Profile
  | 0 => ballot [b]
  | 1 => ballot [d]
  | 2 => ballot [a, c]

/-- P₅.₅ = (b, cd, ac) -/
def P5_5 : Profile
  | 0 => ballot [b]
  | 1 => ballot [c, d]
  | 2 => ballot [a, c]

/-- P₆ = (b, cd, a) -/
def P6 : Profile
  | 0 => ballot [b]
  | 1 => ballot [c, d]
  | 2 => ballot [a]

/-- P₆.₅ = (b, cd, ad) -/
def P6_5 : Profile
  | 0 => ballot [b]
  | 1 => ballot [c, d]
  | 2 => ballot [a, d]

/-- P₇ = (b, c, ad) -/
def P7 : Profile
  | 0 => ballot [b]
  | 1 => ballot [c]
  | 2 => ballot [a, d]

/-- P₇.₅ = (ab, c, ad) -/
def P7_5 : Profile
  | 0 => ballot [a, b]
  | 1 => ballot [c]
  | 2 => ballot [a, d]

-- ============================================================================
-- COMMITTEE DEFINITIONS
-- ============================================================================

/-- Committee acd = {a, c, d} -/
def acd : Finset C := ballot [a, c, d]

/-- Committee bcd = {b, c, d} -/
def bcd : Finset C := ballot [b, c, d]

/-- Committee abd = {a, b, d} -/
def abd : Finset C := ballot [a, b, d]

/-- Committee abc = {a, b, c} -/
def abc : Finset C := ballot [a, b, c]

-- ============================================================================
-- HELPER LEMMAS FOR PROFILES
-- ============================================================================

/-- P1 is a party-list profile where voters 1 and 2 are singleton parties -/
lemma P1_party_list_at_1 : (mk_instance P1).singleton_party_size c = 1 := by
  simp [singleton_party_size, mk_instance, P1, ballot, c]
  decide

lemma P1_party_list_at_2 : (mk_instance P1).singleton_party_size d = 1 := by
  simp [singleton_party_size, mk_instance, P1, ballot, d]
  decide

/-- In P1, voters 1 and 2 have singleton ballots with support ≥ n/k = 1 -/
lemma P1_c_threshold : (mk_instance P1).singleton_party_size c * k ≥ (mk_instance P1).voters.card := by
  simp [mk_instance, k, P1_party_list_at_1]
  decide

lemma P1_d_threshold : (mk_instance P1).singleton_party_size d * k ≥ (mk_instance P1).voters.card := by
  simp [mk_instance, k, P1_party_list_at_2]
  decide

-- ============================================================================
-- INSTANCE VARIANT LEMMAS
-- ============================================================================

/-- P1_5 is a 1-variant of P1 (voter 1 changed from {c} to {a,c}) -/
lemma P1_5_variant_of_P1 : (mk_instance P1).is_i_variant (mk_instance P1_5) 1 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v <;> simp_all [mk_instance, P1, P1_5]

/-- {c} ⊂ {a,c} for the transition P1 → P1_5 -/
lemma P1_to_P1_5_subset : (mk_instance P1).approves 1 ⊂ (mk_instance P1_5).approves 1 := by
  simp [mk_instance, P1, P1_5, ballot, a, c]
  decide

/-- P2 is a 0-variant of P1_5 (voter 0 changed from {a,b} to {b}) -/
lemma P2_variant_of_P1_5 : (mk_instance P1_5).is_i_variant (mk_instance P2) 0 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro v _ hne
  fin_cases v <;> simp_all [mk_instance, P1_5, P2]

/-- {b} ⊂ {a,b} for the transition P1_5 → P2 -/
lemma P1_5_to_P2_subset : (mk_instance P2).approves 0 ⊂ (mk_instance P1_5).approves 0 := by
  simp [mk_instance, P1_5, P2, ballot, a, b]
  decide

-- More variant lemmas would be defined similarly for each transition...

-- ============================================================================
-- MAIN IMPOSSIBILITY THEOREM (BASE CASE)
-- ============================================================================

/--
Base case impossibility: There is no resolute ABC rule for k=3, n=3, m=4
that satisfies weak efficiency, proportionality, and strategyproofness.

The proof follows Peters' paper:
1. Consider P₁ = (ab, c, d). By proportionality, c ∈ f(P₁) and d ∈ f(P₁).
2. Since |f(P₁)| = 3 and c,d ∈ f(P₁), we have f(P₁) ∈ {acd, bcd}.
3. WLOG assume f(P₁) = acd (by symmetry of a and b).
4. Use strategyproofness to derive constraints on f at other profiles.
5. Eventually derive a contradiction.
-/
theorem base_case_impossibility :
    ¬∃ (f : ABCRule V C k),
      f.IsResolute ∧
      f.SatisfiesWeakEfficiency ∧
      f.SatisfiesProportionality ∧
      f.SatisfiesResoluteStrategyproofness := by
  intro ⟨f, hres, heff, hprop, hsp⟩

  -- Proof that k = k (trivial)
  have hk_P1 : (mk_instance P1).k = k := rfl

  -- Let W₁ = f(P₁)
  let W1 := f.resolute_committee (mk_instance P1) hk_P1 hres

  -- By proportionality on P1 (which is party-list for voters 1,2):
  -- c ∈ W₁ and d ∈ W₁

  -- First we need to show P1 is party-list
  have hP1_party : (mk_instance P1).is_party_list := by
    intro v₁ _ v₂ _
    fin_cases v₁ <;> fin_cases v₂ <;> simp [mk_instance, P1, ballot, a, b, c, d]
    all_goals decide

  -- Actually P1 is NOT a party-list profile since voter 0 approves {a,b}.
  -- Peters' proportionality only applies to singleton parties on party-list profiles.
  -- We need to use Lemma 3 (singleton approvers) which is more general.
  -- -- Comment written above was written by Claude. Response from the user: actually, the proportionality axiom
  --    applies to ALL party-list profiles including those with non-singleton parties, it just only guarantees representation for singleton parties.
  --    So we can still use proportionality here.

  -- For now, let's state the key fact and leave the detailed proof as sorry
  -- The full proof requires the singleton approvers lemma and careful case analysis

  sorry

end Peters.BaseCase
