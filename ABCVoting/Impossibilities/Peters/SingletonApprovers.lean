import ABCVoting.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.Peters.RestrictToPlentiful
import Mathlib.Data.Finset.Card

open Finset BigOperators ABCInstance

/-!
# Singleton Approvers Lemma (Lemma 3 from Peters)

This file proves Lemma 3 from Peters' paper:

When m = k+1, if a singleton ballot {c} appears at least n/k times,
and no other voter approves c (i.e., c is exclusively approved by singleton voters),
then c must be elected.

The key insight is that we can transform any such profile into a party-list
profile by having non-{c} voters report C \ {c}. Since f is strategyproof,
the outcome cannot exclude c after this transformation.
-/

namespace Peters.SingletonApprovers

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- EXCLUSIVE SINGLETON CONDITION
-- ============================================================================

/--
A candidate c is exclusively approved by singleton voters if:
1. Some voters approve exactly {c} (the singleton party is nonempty)
2. No other voter approves c (supporters = singleton party)

This is the condition "no other voter approves c" from Lemma 3.
-/
def is_exclusive_singleton (inst : ABCInstance V C k) (c : C) : Prop :=
  (inst.singleton_party c).Nonempty ∧
  inst.supporters c = inst.singleton_party c

/--
When c is exclusive singleton, any voter who approves c must be in the singleton party.
-/
lemma exclusive_singleton_approvers (inst : ABCInstance V C k) (c : C)
    (hexcl : is_exclusive_singleton inst c) (v : V) (hv : v ∈ inst.voters)
    (hc : c ∈ inst.approves v) :
    inst.approves v = {c} := by
  have hsup : v ∈ inst.supporters c := by
    simp only [supporters, mem_filter]
    exact ⟨hv, hc⟩
  rw [hexcl.2] at hsup
  exact (mem_singleton_party_iff inst c v).mp hsup |>.2

-- ============================================================================
-- PARTY-LIST TRANSFORMATION
-- ============================================================================

/--
Transform a profile where c is exclusively approved by singleton voters
into a party-list profile:
- Voters with ballot {c} keep their ballot
- All other voters report C \ {c}

This gives a two-party profile: party {c} and party C \ {c}.
-/
def to_party_list (inst : ABCInstance V C k) (c : C)
    (hc : c ∈ inst.candidates)
    (_hm : inst.candidates.card ≥ 2) -- Need at least 2 candidates for proper ballots
    (_hexcl : is_exclusive_singleton inst c) :
    ABCInstance V C k where
  voters := inst.voters
  candidates := inst.candidates
  approves := fun v =>
    if inst.approves v = {c} then {c}
    else inst.candidates \ {c}
  approves_subset := by
    intro v _
    by_cases h : inst.approves v = {c}
    · simp [h, Finset.singleton_subset_iff, hc]
    · simp [h, Finset.sdiff_subset]
  voters_nonempty := inst.voters_nonempty
  k_pos := inst.k_pos
  k_le_m := inst.k_le_m

/--
The transformed profile is a party-list profile.
There are exactly two parties: {c} and C \ {c}, which are disjoint.
-/
lemma to_party_list_is_party_list (inst : ABCInstance V C k) (c : C)
    (hc : c ∈ inst.candidates)
    (hm : inst.candidates.card ≥ 2)
    (hexcl : is_exclusive_singleton inst c) :
    (to_party_list inst c hc hm hexcl).is_party_list := by
  intro v₁ _ v₂ _
  simp only [to_party_list]
  by_cases h1 : inst.approves v₁ = {c} <;> by_cases h2 : inst.approves v₂ = {c}
  · -- Both in {c} party
    left; simp [h1, h2]
  · -- v₁ in {c}, v₂ in C \ {c}
    right; simp only [h1, h2, ↓reduceIte]
    exact Finset.disjoint_singleton_left.mpr
      (Finset.notMem_sdiff_of_mem_right (mem_singleton_self c))
  · -- v₁ in C \ {c}, v₂ in {c}
    right; simp only [h1, h2, ↓reduceIte]
    exact Finset.disjoint_singleton_right.mpr
      (Finset.notMem_sdiff_of_mem_right (mem_singleton_self c))
  · -- Both in C \ {c} party
    left; simp [h1, h2]

/--
The singleton party for c has the same size in the transformed profile.
-/
lemma to_party_list_singleton_party_size (inst : ABCInstance V C k) (c : C)
    (hc : c ∈ inst.candidates)
    (hm : inst.candidates.card ≥ 2)
    (hexcl : is_exclusive_singleton inst c) :
    (to_party_list inst c hc hm hexcl).singleton_party_size c = inst.singleton_party_size c := by
  simp only [singleton_party_size, to_party_list]
  congr 1
  ext v
  simp only [mem_filter]
  constructor
  · intro ⟨hv, heq⟩
    constructor
    · exact hv
    · by_cases h : inst.approves v = {c}
      · simp [h] at heq; exact h
      · simp [h] at heq
  · intro ⟨hv, heq⟩
    constructor
    · exact hv
    · simp [heq]

-- ============================================================================
-- STRATEGYPROOFNESS CHAIN
-- ============================================================================

/--
The transformation from P to P' (party-list) can be done step by step:
each non-{c} voter changes from their true ballot to C \ {c}.
Since their true ballot doesn't contain c (by exclusive singleton),
their true ballot is a subset of C \ {c}.
-/
lemma original_ballot_subset_complement (inst : ABCInstance V C k) (c : C)
    (hexcl : is_exclusive_singleton inst c) (v : V) (hv : v ∈ inst.voters)
    (hne : inst.approves v ≠ {c}) :
    inst.approves v ⊆ inst.candidates \ {c} := by
  intro x hx
  rw [Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · exact inst.approves_subset v hv hx
  · intro heq
    rw [heq] at hx
    have := exclusive_singleton_approvers inst c hexcl v hv hx
    exact hne this

/--
The non-{c} voters: voters whose ballot is not exactly {c}.
-/
def non_singleton_voters (inst : ABCInstance V C k) (c : C) : Finset V :=
  inst.voters.filter (fun v => inst.approves v ≠ {c})


-- ============================================================================
-- PROFILE SEQUENCE FOR INDUCTION
-- ============================================================================

/--
Given an instance and a set S of non-{c} voters, construct a profile where:
- Voters in S report C \ {c}
- All other voters report their original ballot

When S = ∅, this is the original profile.
When S = non_singleton_voters, this is the party-list profile.
-/
def profile_with_switched (inst : ABCInstance V C k) (c : C)
    (_hc : c ∈ inst.candidates)
    (_hm : inst.candidates.card ≥ 2)
    (S : Finset V) :
    ABCInstance V C k where
  voters := inst.voters
  candidates := inst.candidates
  approves := fun v =>
    if v ∈ S then inst.candidates \ {c}
    else inst.approves v
  approves_subset := by
    intro v hv
    by_cases h : v ∈ S
    · simp [h, Finset.sdiff_subset]
    · simp [h, inst.approves_subset v hv]
  voters_nonempty := inst.voters_nonempty
  k_pos := inst.k_pos
  k_le_m := inst.k_le_m

/--
With S = ∅, we get the original profile.
-/
lemma profile_with_switched_empty (inst : ABCInstance V C k) (c : C)
    (hc : c ∈ inst.candidates) (hm : inst.candidates.card ≥ 2) :
    (profile_with_switched inst c hc hm ∅).approves = inst.approves := by
  ext v
  simp [profile_with_switched]

/--
With S = non_singleton_voters c (assuming exclusive singleton), we get the party-list profile.
For voters, the ballots are equal.
-/
lemma profile_with_switched_all (inst : ABCInstance V C k) (c : C)
    (hc : c ∈ inst.candidates) (hm : inst.candidates.card ≥ 2)
    (hexcl : is_exclusive_singleton inst c) (v : V) (hv : v ∈ inst.voters) :
    (profile_with_switched inst c hc hm (non_singleton_voters inst c)).approves v =
    (to_party_list inst c hc hm hexcl).approves v := by
  simp only [profile_with_switched, to_party_list, non_singleton_voters, mem_filter]
  by_cases h : inst.approves v = {c}
  · simp [h, hv]
  · simp [h, hv]

/--
Adding one voter to S creates an i-variant.
-/
lemma profile_with_switched_variant (inst : ABCInstance V C k) (c : C)
    (hc : c ∈ inst.candidates) (hm : inst.candidates.card ≥ 2)
    (S : Finset V) (i : V) (_hi_notin : i ∉ S) :
    (profile_with_switched inst c hc hm S).is_i_variant
    (profile_with_switched inst c hc hm (insert i S)) i := by
  refine ⟨rfl, rfl, ?_⟩
  intro v _ hne
  simp [profile_with_switched, Finset.mem_insert, hne]

/-- Any ballot of size at least `k` witnesses plentifulness. -/
lemma plentiful_of_ballot_card_ge_k (inst : ABCInstance V C k) (v : V)
    (hv : v ∈ inst.voters) (hcard : (inst.approves v).card ≥ k) :
    inst.plentiful := by
  have hsub : inst.approves v ⊆ inst.approvedCandidates := by
    intro c hc
    have : c ∈ inst.voters.biUnion inst.approves :=
      Finset.mem_biUnion.2 ⟨v, hv, by simpa using hc⟩
    simpa [ABCInstance.approvedCandidates] using this
  have hcard_le : (inst.approves v).card ≤ inst.approvedCandidates.card :=
    Finset.card_le_card hsub
  exact le_trans hcard hcard_le

/--
`profile_with_switched` is plentiful if either `S` is empty (so it is just `inst`,
assumed plentiful) or if `S` is nonempty, since then some voter reports
`inst.candidates \\ {c}`, which has size `k` when `m = k+1`.
-/
lemma profile_with_switched_plentiful (inst : ABCInstance V C k) (c : C)
    (hc : c ∈ inst.candidates) (hm_card : inst.candidates.card = k + 1)
    (hm_ge_2 : inst.candidates.card ≥ 2) (S : Finset V) (hS_sub : S ⊆ inst.voters)
    (hpl : inst.plentiful) :
    (profile_with_switched inst c hc hm_ge_2 S).plentiful := by
  classical
  by_cases hS : S = ∅
  · subst hS
    simpa [profile_with_switched] using hpl
  · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    rcases hne with ⟨v, hv⟩
    have hv_voters : v ∈ inst.voters := hS_sub hv
    have hv_ballot :
        (profile_with_switched inst c hc hm_ge_2 S).approves v = inst.candidates \ {c} := by
      simp [profile_with_switched, hv]
    have hcard_ballot : ((profile_with_switched inst c hc hm_ge_2 S).approves v).card = k := by
      have hc_sub : {c} ⊆ inst.candidates := Finset.singleton_subset_iff.mpr hc
      have h_card_sdiff_eq_k : (inst.candidates \ {c}).card = k := by
        calc
          (inst.candidates \ {c}).card
              = inst.candidates.card - ({c} : Finset C).card := by
                  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hc_sub]
          _ = (k + 1) - 1 := by simp [hm_card, Finset.card_singleton]
          _ = k := by simp
      simpa [hv_ballot, h_card_sdiff_eq_k]
    have hv_in_switched : v ∈ (profile_with_switched inst c hc hm_ge_2 S).voters := by
      simp [profile_with_switched, hv_voters]
    have hcard_ge : ((profile_with_switched inst c hc hm_ge_2 S).approves v).card ≥ k := by
      simpa [hcard_ballot]
    exact plentiful_of_ballot_card_ge_k
      (inst := profile_with_switched inst c hc hm_ge_2 S) (v := v) hv_in_switched hcard_ge
/--
Plentiful strategyproofness analogue of `sp_preserves_committee_ne_strict`.
-/
lemma sp_preserves_committee_ne_strict_on_plentiful (f : ABCRule V C k)
    (hsp : Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f)
    (hwf : IsWellFormedOnPlentiful f)
    (inst inst' : ABCInstance V C k) (i : V)
    (hpl : inst.plentiful) (hpl' : inst'.plentiful)
    (hi : i ∈ inst.voters)
    (hvar : inst.is_i_variant inst' i)
    (hsub : inst'.approves i ⊂ inst.approves i)
    (hres : f.IsResolute)
    (h_size : (inst.approves i).card = k)
    (hW_ne : f.resolute_committee inst hres ≠ inst.approves i) :
    f.resolute_committee inst' hres ≠ inst.approves i := by
  intro hcontra
  have hleft_eq : f.resolute_committee inst' hres ∩ inst.approves i = inst.approves i := by
    rw [hcontra, Finset.inter_self]
  have hW_card : (f.resolute_committee inst hres).card = k :=
    (hwf inst hpl).2 _ (f.resolute_committee_mem inst hres) |>.1
  have hcard_inter_le : (f.resolute_committee inst hres ∩ inst.approves i).card ≤ k := by
    have hsubset :
        f.resolute_committee inst hres ∩ inst.approves i ⊆
        f.resolute_committee inst hres :=
      Finset.inter_subset_left
    exact le_trans (Finset.card_le_card hsubset) (by simpa [hW_card])
  have hcard_inter_lt : (f.resolute_committee inst hres ∩ inst.approves i).card < k := by
    by_contra hnot
    have hcard_ge : k ≤ (f.resolute_committee inst hres ∩ inst.approves i).card :=
      le_of_not_gt hnot
    have hcard_eq : (f.resolute_committee inst hres ∩ inst.approves i).card = k :=
      le_antisymm hcard_inter_le hcard_ge
    have hsubset : f.resolute_committee inst hres ∩ inst.approves i ⊆ inst.approves i :=
      Finset.inter_subset_right
    have hcardA_le : (inst.approves i).card ≤
        (f.resolute_committee inst hres ∩ inst.approves i).card := by
      simpa [h_size, hcard_eq]
    have hEqA :
        f.resolute_committee inst hres ∩ inst.approves i = inst.approves i :=
      Finset.eq_of_subset_of_card_le hsubset hcardA_le
    have hA_subset_W : inst.approves i ⊆ f.resolute_committee inst hres := by
      have hsubleft :
          f.resolute_committee inst hres ∩ inst.approves i ⊆
          f.resolute_committee inst hres :=
        Finset.inter_subset_left
      simpa [hEqA] using hsubleft
    have hW_eq :
        f.resolute_committee inst hres = inst.approves i :=
      (Finset.eq_of_subset_of_card_le hA_subset_W (by simp [hW_card, h_size])).symm
    exact hW_ne hW_eq
  have hgain :
      f.resolute_committee inst' hres ∩ inst.approves i ⊃
        f.resolute_committee inst hres ∩ inst.approves i := by
    have hss :
        f.resolute_committee inst hres ∩ inst.approves i ⊂ inst.approves i := by
      refine Finset.ssubset_iff_subset_ne.mpr ?_
      refine ⟨Finset.inter_subset_right, ?_⟩
      intro hEq
      have hlt' : (inst.approves i).card < (inst.approves i).card := by
        have := hcard_inter_lt
        have hk : (inst.approves i).card = k := h_size
        simpa [hEq, hk] using this
      exact (lt_irrefl _ hlt')
    -- rewrite RHS using hleft_eq to get the strict gain
    simpa [hleft_eq] using hss
  have hno := hsp inst inst' i hpl hpl' hi hvar hsub hres
  exact hno hgain

-- ============================================================================
-- KEY LEMMA: REMOVING ONE VOTER FROM S PRESERVES c IN COMMITTEE
-- ============================================================================

/--
The key induction step: If c is in the committee for profile_with_switched with set S,
and we remove one voter i from S (so i now reports their original ballot instead of C \ {c}),
then c must still be in the committee.

This uses strategyproofness: voter i switching from C \ {c} to their original ballot
(a subset) cannot cause a strict improvement, so c cannot be removed from the committee.

Note: When m = k+1, there are only two possible size-k committees: one containing c
and one not containing c (= C \ {c}). If c ∈ W, then W ∩ (C \ {c}) has size k-1.
If c ∉ W, then W = C \ {c}, so W ∩ (C \ {c}) = W has size k.
So removing c from the committee would give voter i MORE approved candidates
(k instead of k-1), which is a strict improvement - forbidden by SP.
-/
lemma c_in_committee_induction_step
    (inst : ABCInstance V C k) (c : C)
    (hc : c ∈ inst.candidates)
    (hm : inst.candidates.card = k + 1)
    (hm_ge_2 : inst.candidates.card ≥ 2)
    (hexcl : is_exclusive_singleton inst c)
    (f : ABCRule V C k)
    (hwf : IsWellFormedOnPlentiful f)
    (hres : f.IsResolute)
    (hsp : Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f)
    (S : Finset V) (i : V)
    (hi_in_S : i ∈ S)
    (hi_voter : i ∈ inst.voters)
    (hS_sub : S ⊆ inst.voters)
    (hpl : inst.plentiful)
    (hi_non_sing : inst.approves i ≠ {c})
    (hc_in_S : c ∈ f.resolute_committee (profile_with_switched inst c hc hm_ge_2 S) hres) :
    c ∈ f.resolute_committee (profile_with_switched inst c hc hm_ge_2 (S.erase i)) hres := by
  -- Let P_S = profile_with_switched inst c hc hm_ge_2 S
  -- Let P_{S\i} = profile_with_switched inst c hc hm_ge_2 (S.erase i)
  -- We have c ∈ f(P_S) and need to show c ∈ f(P_{S\i})

  let P_S := profile_with_switched inst c hc hm_ge_2 S
  let P_Si := profile_with_switched inst c hc hm_ge_2 (S.erase i)

  have hpl_S : P_S.plentiful :=
    profile_with_switched_plentiful inst c hc hm hm_ge_2 S hS_sub hpl
  have hS_sub_erase : S.erase i ⊆ inst.voters := (Finset.erase_subset i S).trans hS_sub
  have hpl_Si : P_Si.plentiful :=
    profile_with_switched_plentiful inst c hc hm hm_ge_2 (S.erase i) hS_sub_erase hpl

  -- In P_S, voter i reports C \ {c}
  have hi_ballot_S : P_S.approves i = inst.candidates \ {c} := by
    simp only [P_S, profile_with_switched, hi_in_S, ite_true]

  -- In P_{S\i}, voter i reports their original ballot
  have hi_ballot_Si : P_Si.approves i = inst.approves i := by
    simp only [P_Si, profile_with_switched, Finset.notMem_erase, ite_false]

  -- Case split: is voter i's original ballot equal to C \ {c} or not?
  by_cases hi_ballot_eq : inst.approves i = inst.candidates \ {c}
  · -- Case 1: voter i already has ballot C \ {c}, so P_S and P_Si have same approvals
    have h_same_approves : P_S.approves = P_Si.approves := by
      ext v x
      by_cases hvi : v = i
      · simp only [hvi, hi_ballot_S, hi_ballot_Si, hi_ballot_eq]
      · simp only [P_S, P_Si, profile_with_switched]
        have h1 : v ∈ S ↔ v ∈ S.erase i := by simp [Finset.mem_erase, hvi]
        simp only [h1]
    have h_same_committee : f.resolute_committee P_S hres = f.resolute_committee P_Si hres :=
      ABCRule.resolute_ballot_ext f P_S P_Si hres rfl rfl (fun v _ => congrFun h_same_approves v)
    rw [← h_same_committee]
    exact hc_in_S

  · -- Case 2: voter i's original ballot is strictly contained in C \ {c}
    have hi_orig_sub : inst.approves i ⊂ inst.candidates \ {c} := by
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨original_ballot_subset_complement inst c hexcl i hi_voter hi_non_sing, hi_ballot_eq⟩

    -- P_{S\i} is an i-variant of P_S
    have hvar : P_S.is_i_variant P_Si i := by
      refine ⟨rfl, rfl, fun v _ hne => ?_⟩
      simp only [P_S, P_Si, profile_with_switched]
      have h1 : v ∈ S ↔ v ∈ S.erase i := by simp [Finset.mem_erase, hne]
      simp only [h1]

    -- The subset relation in P_S terms
    have hsub : P_Si.approves i ⊂ P_S.approves i := by
      rw [hi_ballot_S, hi_ballot_Si]
      exact hi_orig_sub

    -- The approval size in P_S is k (since it's C \ {c} and |C| = k+1)
    have h_size : (P_S.approves i).card = k := by
      simp only [hi_ballot_S, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hc),
        Finset.card_singleton, hm]; omega

    -- c ∈ f(P_S) means f(P_S) ≠ C \ {c} = P_S.approves i
    have hW_ne : f.resolute_committee P_S hres ≠ P_S.approves i := by
      rw [hi_ballot_S]
      intro heq
      rw [heq] at hc_in_S
      exact Finset.notMem_sdiff_of_mem_right (Finset.mem_singleton_self c) hc_in_S

    -- By sp_preserves_committee_ne_strict, f(P_{S\i}) ≠ P_S.approves i
    have hi_voter_S : i ∈ P_S.voters := hi_voter  -- P_S.voters = inst.voters by definition

    have hW_ne' : f.resolute_committee P_Si hres ≠ P_S.approves i :=
      sp_preserves_committee_ne_strict_on_plentiful (f := f) (hsp := hsp) (hwf := hwf)
        (inst := P_S) (inst' := P_Si) (i := i)
        (hpl := hpl_S) (hpl' := hpl_Si) (hi := hi_voter_S) (hvar := hvar)
        (hsub := hsub) (hres := hres) (h_size := h_size) (hW_ne := hW_ne)

    -- f(P_{S\i}) ≠ C \ {c}, so since m = k+1, we must have c ∈ f(P_{S\i})
    rw [hi_ballot_S] at hW_ne'
    have h_wf := hwf P_Si hpl_Si
    have ⟨hW_card, hW_sub⟩ := h_wf.2 _ (f.resolute_committee_mem _ hres)
    have hW_sub_cands : f.resolute_committee P_Si hres ⊆ inst.candidates := by
      simpa [P_Si, profile_with_switched] using hW_sub
    have hW_card' : (f.resolute_committee P_Si hres).card = inst.candidates.card - 1 := by
      simp only [hW_card, hm]; omega
    exact committee_ne_complement_has_c inst.candidates c hc _ hW_sub_cands hW_card' hW_ne'

-- ============================================================================
-- MAIN LEMMA
-- ============================================================================

/--
Lemma 3 (Peters): Let m = k+1. Let f be strategyproof and proportional.
Suppose that P is a profile in which some singleton ballot {c} appears at
least n/k times, but no other voter approves c. Then c ∈ f(P).

Proof outline:
1. Let P' be the party-list profile where {c} voters keep {c}, others report C \ {c}.
2. P' is a party-list profile with the same singleton party size for c.
3. By proportionality on P', since the {c} party has ≥ n/k members, c ∈ f(P').
4. Now transform P' back to P step by step (each non-{c} voter changes from
   C \ {c} back to their true ballot, which is a subset).
5. By strategyproofness, the committee cannot change from containing c to not
   containing c (since that would be C \ {c}, the only other possible committee
   when m = k+1).
6. Therefore c ∈ f(P).
-/
theorem singleton_approvers_elected {k : ℕ}
    (inst : ABCInstance V C k)
    (c : C)
    (hc : c ∈ inst.candidates)
    (hm : inst.candidates.card = k + 1) -- m = k+1
    (h_size : inst.singleton_party_size c * k ≥ inst.voters.card)
    (hexcl : is_exclusive_singleton inst c)
    (f : ABCRule V C k)
    (hwf : IsWellFormedOnPlentiful f)
    (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality)
    (hsp : Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f)
    (hpl : inst.plentiful) :
    c ∈ f.resolute_committee inst hres := by
  -- Need m ≥ 2 for the party-list transformation
  have hm_ge_2 : inst.candidates.card ≥ 2 := by
    rw [hm]
    have := inst.k_pos
    omega

  -- Define the party-list profile P'
  let P' := to_party_list inst c hc hm_ge_2 hexcl

  -- Step 1: Show c ∈ f(P') by proportionality
  -- P' is party-list
  have hP'_pl : P'.is_party_list := to_party_list_is_party_list inst c hc hm_ge_2 hexcl

  -- c is a candidate in P' (P'.candidates = inst.candidates by definition)
  have hc_cand' : c ∈ P'.candidates := hc

  -- The singleton party size for c in P' equals that in inst
  have h_size' : P'.singleton_party_size c * k ≥ P'.voters.card := by
    rw [to_party_list_singleton_party_size]
    exact h_size

  -- By proportionality, c is in f(P')
  have hc_in_P' : c ∈ f.resolute_committee P' hres := by
    apply hprop P' c hP'_pl hc_cand' h_size'
    exact f.resolute_committee_mem P' hres

  -- Step 2: Transform P' back to inst step by step using SP
  -- For each non-{c} voter, their ballot in inst is a strict subset of C\{c}
  -- By SP, switching from C\{c} to their true ballot cannot strictly improve

  -- The key observation: when m = k+1, the only two possible committees are
  -- the full candidate set minus one candidate. If c is in f(P'), then
  -- f(P') contains c. By SP chain, f(inst) must also contain c.

  -- The non-singleton voters
  let S := non_singleton_voters inst c
  have hS_sub : S ⊆ inst.voters := Finset.filter_subset _ _

  -- Key: profile_with_switched with S = non_singleton_voters gives same committee as P'
  -- (because voters have same ballots)
  have h_same : ∀ v ∈ inst.voters,
      (profile_with_switched inst c hc hm_ge_2 S).approves v = P'.approves v :=
    fun v hv => profile_with_switched_all inst c hc hm_ge_2 hexcl v hv

  have h_committee_eq : f.resolute_committee (profile_with_switched inst c hc hm_ge_2 S) hres =
      f.resolute_committee P' hres := by
    apply ABCRule.resolute_ballot_ext
    · rfl
    · rfl
    · exact h_same

  -- So c ∈ f(profile_with_switched S)
  have hc_in_S : c ∈ f.resolute_committee (profile_with_switched inst c hc hm_ge_2 S) hres := by
    rw [h_committee_eq]
    exact hc_in_P'

  -- Induction: for any subset T ⊆ S, if c ∈ f(profile_with_switched T), then c ∈ f(inst)
  -- We prove this by strong induction on |T|
  have h_induction : ∀ T ⊆ S,
      c ∈ f.resolute_committee (profile_with_switched inst c hc hm_ge_2 T) hres →
      c ∈ f.resolute_committee inst hres := by
    intro T
    induction T using Finset.strongInduction with
    | H T ih =>
      intro hT_sub hc_in_T
      by_cases hT_empty : T = ∅
      · -- Base case: T = ∅, profile_with_switched ∅ = inst
        rw [hT_empty] at hc_in_T
        have h_approves_eq : (profile_with_switched inst c hc hm_ge_2 ∅).approves = inst.approves :=
          profile_with_switched_empty inst c hc hm_ge_2
        have h_comm_eq : f.resolute_committee (profile_with_switched inst c hc hm_ge_2 ∅) hres =
            f.resolute_committee inst hres := by
          apply ABCRule.resolute_ballot_ext
          · rfl
          · rfl
          · intro v _; exact congrFun h_approves_eq v
        rw [h_comm_eq] at hc_in_T
        exact hc_in_T
      · -- Inductive case: T ≠ ∅, pick some i ∈ T
        have ⟨i, hi_in_T⟩ := Finset.nonempty_iff_ne_empty.mpr hT_empty
        -- i is a non-singleton voter (since T ⊆ S = non_singleton_voters)
        have hi_in_S : i ∈ S := hT_sub hi_in_T
        have hi_voter : i ∈ inst.voters := hS_sub hi_in_S
        have hi_non_sing : inst.approves i ≠ {c} := by
          simp only [S, non_singleton_voters, Finset.mem_filter] at hi_in_S
          exact hi_in_S.2
        -- Apply c_in_committee_induction_step to get c ∈ f(profile_with_switched (T.erase i))
        have hT_voters : T ⊆ inst.voters := fun x hx => hS_sub (hT_sub hx)
        have hc_in_erase : c ∈ f.resolute_committee
            (profile_with_switched inst c hc hm_ge_2 (T.erase i)) hres :=
          c_in_committee_induction_step inst c hc hm hm_ge_2 hexcl f hwf hres hsp
            T i hi_in_T hi_voter hT_voters hpl hi_non_sing hc_in_T
        -- Use induction hypothesis on T.erase i
        have h_erase_sub : T.erase i ⊆ S := fun x hx =>
          hT_sub (Finset.mem_of_mem_erase hx)
        have h_erase_ssubset : T.erase i ⊂ T := Finset.erase_ssubset hi_in_T
        exact ih (T.erase i) h_erase_ssubset h_erase_sub hc_in_erase

  -- Apply the induction with T = S
  exact h_induction S (fun x hx => hx) hc_in_S

/--
Corollary: When m = k+1 and c is exclusive singleton with sufficient support,
the committee cannot be C \ {c}.
-/
theorem committee_not_complement {k : ℕ}
    (inst : ABCInstance V C k)
    (c : C)
    (hc : c ∈ inst.candidates)
    (hm : inst.candidates.card = k + 1)
    (h_size : inst.singleton_party_size c * k ≥ inst.voters.card)
    (hexcl : is_exclusive_singleton inst c)
    (f : ABCRule V C k)
    (hwf : IsWellFormedOnPlentiful f)
    (hres : f.IsResolute)
    (hprop : f.SatisfiesProportionality)
    (hsp : Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f)
    (hpl : inst.plentiful) :
    f.resolute_committee inst hres ≠ inst.candidates \ {c} := by
  intro heq
  have hc_in := singleton_approvers_elected inst c hc hm h_size hexcl f hwf hres hprop hsp hpl
  rw [heq] at hc_in
  exact Finset.notMem_sdiff_of_mem_right (mem_singleton_self c) hc_in

end Peters.SingletonApprovers
