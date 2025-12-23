import ABCVoting.ABCRule
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import Mathlib.Data.Finset.Card

open Finset BigOperators ABCInstance

namespace KluivingDeVriesVrijbergenBoixelEndriss.SingletonApprovers

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- EXCLUSIVE SINGLETON CONDITION
-- ============================================================================

/--
A candidate c is exclusively approved by singleton voters if:
1. Some voters approve exactly {c} (the singleton party is nonempty)
2. No other voter approves c (supporters = singleton party)
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

/--
The non-{c} voters: voters whose ballot is not exactly {c}.
-/
def non_singleton_voters (inst : ABCInstance V C k) (c : C) : Finset V :=
  inst.voters.filter (fun v => inst.approves v ≠ {c})

-- ============================================================================
-- PARTY-LIST START PROFILE
-- ============================================================================

/--
Profile where a set S of non-{c} voters have switched back to their original ballots.
All other non-{c} voters report C \ {c}; singleton {c} voters always keep {c}.
-/
def profile_with_switched (inst : ABCInstance V C k) (c : C) (S : Finset V) :
    ABCInstance V C k where
  voters := inst.voters
  candidates := inst.candidates
  approves := fun v =>
    if inst.approves v = {c} then {c}
    else if v ∈ S then inst.approves v else inst.candidates \ {c}
  approves_subset := by
    intro v hv
    by_cases hsing : inst.approves v = {c}
    · have hc' : c ∈ inst.candidates := by
        have hsub : {c} ⊆ inst.candidates := by
          simpa [hsing] using inst.approves_subset v hv
        exact Finset.singleton_subset_iff.mp hsub
      simp [hsing, Finset.singleton_subset_iff, hc']
    · by_cases hS : v ∈ S
      · simp [hsing, hS, inst.approves_subset v hv]
      · simp [hsing, hS, Finset.sdiff_subset]
  voters_nonempty := inst.voters_nonempty
  k_pos := inst.k_pos
  k_le_m := inst.k_le_m

/--
With S = ∅, we get the party-list profile {c} / C \ {c}.
-/
lemma profile_with_switched_empty_is_party_list (inst : ABCInstance V C k) (c : C) :
    (profile_with_switched inst c ∅).is_party_list := by
  intro v₁ _ v₂ _
  simp only [profile_with_switched]
  by_cases h1 : inst.approves v₁ = {c} <;> by_cases h2 : inst.approves v₂ = {c}
  · left; simp [h1, h2]
  · right; simp [h1, h2]
  · right; simp [h1, h2]
  · left; simp [h1, h2]

/--
The singleton party for c has the same size in the switched profile with S = ∅.
-/
lemma profile_with_switched_singleton_party_size (inst : ABCInstance V C k) (c : C) :
    (profile_with_switched inst c ∅).singleton_party_size c =
      inst.singleton_party_size c := by
  simp only [singleton_party_size, profile_with_switched]
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

/--
With S = non_singleton_voters, we recover the original profile.
-/
lemma profile_with_switched_all (inst : ABCInstance V C k) (c : C)
    (v : V) (hv : v ∈ inst.voters) :
    (profile_with_switched inst c (non_singleton_voters inst c)).approves v =
      inst.approves v := by
  simp only [profile_with_switched, non_singleton_voters, mem_filter]
  by_cases h : inst.approves v = {c}
  · simp [h]
  · have : v ∈ inst.voters ∧ inst.approves v ≠ {c} := ⟨hv, h⟩
    simp [h, this]

-- ============================================================================
-- CARDINALITY LEMMAS FOR CANDIDATES \ {c}
-- ============================================================================

lemma inter_complement_card_of_mem (inst : ABCInstance V C k) (c : C) (W : Finset C)
    (hW_sub : W ⊆ inst.candidates) (hW_card : W.card = k) (hcW : c ∈ W) :
    (W ∩ (inst.candidates \ {c})).card = k - 1 := by
  have h_inter : W ∩ (inst.candidates \ {c}) = W.erase c := by
    ext x
    constructor
    · intro hx
      have hxW : x ∈ W := (Finset.mem_inter.mp hx).1
      have hxC : x ∈ inst.candidates \ {c} := (Finset.mem_inter.mp hx).2
      have hxne : x ≠ c := by
        have hxne' : x ∉ ({c} : Finset C) := (Finset.mem_sdiff.mp hxC).2
        intro hxc
        exact hxne' (by simpa [hxc] using Finset.mem_singleton_self c)
      exact Finset.mem_erase.mpr ⟨hxne, hxW⟩
    · intro hx
      have hxW : x ∈ W := (Finset.mem_erase.mp hx).2
      have hxne : x ≠ c := (Finset.mem_erase.mp hx).1
      have hxCand : x ∈ inst.candidates := hW_sub hxW
      have hxC : x ∈ inst.candidates \ {c} := by
        refine Finset.mem_sdiff.mpr ?_
        constructor
        · exact hxCand
        · intro hxmem
          have : x = c := by simpa using hxmem
          exact hxne this
      exact Finset.mem_inter.mpr ⟨hxW, hxC⟩
  have hcard : (W.erase c).card = W.card - 1 := Finset.card_erase_of_mem hcW
  simp [h_inter, hcard, hW_card]

lemma inter_complement_card_of_not_mem (inst : ABCInstance V C k) (c : C) (W : Finset C)
    (hW_sub : W ⊆ inst.candidates) (hW_card : W.card = k) (hcW : c ∉ W) :
    (W ∩ (inst.candidates \ {c})).card = k := by
  have hW_sub' : W ⊆ inst.candidates \ {c} := by
    intro x hx
    have hxCand := hW_sub hx
    refine Finset.mem_sdiff.mpr ?_
    constructor
    · exact hxCand
    · intro hxmem
      have : x = c := by simpa using hxmem
      exact hcW (by simpa [this] using hx)
  have h_inter : W ∩ (inst.candidates \ {c}) = W := by
    exact Finset.inter_eq_left.mpr hW_sub'
  simp [h_inter, hW_card]

-- ============================================================================
-- MAIN LEMMA (Kluiving et al.)
-- ============================================================================

theorem singleton_approvers_elected
    (inst : ABCInstance V C k)
    (c : C)
    (hc : c ∈ inst.candidates)
    (h_size : inst.singleton_party_size c * k ≥ inst.voters.card)
    (_hexcl : is_exclusive_singleton inst c)
    (f : ABCRule V C k)
    (hwf : f.IsWellFormed)
    (hprop : f.SatisfiesMinimalProportionality)
    (hsp : f.SatisfiesCautiousStrategyproofness) :
    ∀ W ∈ f inst, c ∈ W := by
  classical
  -- Base case: party-list profile (S = ∅) satisfies minimal proportionality.
  have h_base : ∀ W ∈ f (profile_with_switched inst c ∅), c ∈ W := by
    have hpl : (profile_with_switched inst c ∅).is_party_list :=
      profile_with_switched_empty_is_party_list inst c
    have h_size' :
        (profile_with_switched inst c ∅).singleton_party_size c * k ≥
          (profile_with_switched inst c ∅).voters.card := by
      simpa [profile_with_switched_singleton_party_size] using h_size
    intro W hW
    exact hprop (profile_with_switched inst c ∅) c hpl hc h_size' W hW

  -- Induction: switch voters back to their true ballots one by one.
  have h_all : ∀ S, S ⊆ non_singleton_voters inst c →
      ∀ W ∈ f (profile_with_switched inst c S), c ∈ W := by
    intro S
    refine Finset.induction_on (s := S) ?base ?step
    · intro hS_sub W hW
      simpa using h_base W hW
    · intro i S hi_notin ih hS_sub W hW
      have hS_sub' : S ⊆ non_singleton_voters inst c := by
        intro v hv
        exact hS_sub (Finset.mem_insert_of_mem hv)
      -- Assume toward contradiction that c ∉ W.
      by_contra hcW
      let instS := profile_with_switched inst c S
      let instS' := profile_with_switched inst c (insert i S)
      have hi_in_Smax : i ∈ non_singleton_voters inst c := hS_sub (Finset.mem_insert_self i S)
      have hi_voter : i ∈ inst.voters :=
        (Finset.mem_filter.mp hi_in_Smax).1
      have hi_non_singleton : inst.approves i ≠ {c} :=
        (Finset.mem_filter.mp hi_in_Smax).2

      have hAi : instS.approves i = inst.candidates \ {c} := by
        simp [instS, profile_with_switched, hi_non_singleton, hi_notin]

      have hAi' : instS'.approves i = inst.approves i := by
        simp [instS', profile_with_switched, hi_non_singleton]

      have hvar : instS.is_i_variant instS' i := by
        refine ⟨rfl, rfl, ?_⟩
        intro v hv hne
        simp [instS, instS', profile_with_switched, hne]

      -- Show that f instS' is strictly better for voter i (A = C \ {c}).
      have h_prefeq : cautious_prefeq (instS.approves i) (f instS') (f instS) := by
        intro W1 hW1 W0 hW0
        have hW0_prop := (hwf instS).2 _ hW0
        have hW1_prop := (hwf instS').2 _ hW1
        have hW0_c : c ∈ W0 := ih hS_sub' W0 hW0
        have hW0_card : W0.card = k := hW0_prop.1
        have hW0_sub : W0 ⊆ inst.candidates := by
          simpa [instS, profile_with_switched] using hW0_prop.2
        have hW1_card : W1.card = k := hW1_prop.1
        have hW1_sub : W1 ⊆ inst.candidates := by
          simpa [instS', profile_with_switched] using hW1_prop.2
        by_cases hW1_c : c ∈ W1
        · have hW0_card' :=
            inter_complement_card_of_mem inst c W0 hW0_sub hW0_card hW0_c
          have hW1_card' :=
            inter_complement_card_of_mem inst c W1 hW1_sub hW1_card hW1_c
          simp [committee_prefeq, hAi, hW1_card', hW0_card']
        · have hW0_card' :=
            inter_complement_card_of_mem inst c W0 hW0_sub hW0_card hW0_c
          have hW1_card' :=
            inter_complement_card_of_not_mem inst c W1 hW1_sub hW1_card hW1_c
          simp [committee_prefeq, hAi, hW1_card', hW0_card']

      have h_not_prefeq : ¬cautious_prefeq (instS.approves i) (f instS) (f instS') := by
        -- Pick any committee from f instS (nonempty by well-formedness).
        obtain ⟨W0, hW0⟩ := (hwf instS).1
        have hW0_c : c ∈ W0 := ih hS_sub' W0 hW0
        have hW0_prop := (hwf instS).2 _ hW0
        have hW0_card : W0.card = k := hW0_prop.1
        have hW0_sub : W0 ⊆ inst.candidates := by
          simpa [instS, profile_with_switched] using hW0_prop.2
        have hW_card : W.card = k := (hwf instS').2 _ hW |>.1
        have hW_sub : W ⊆ inst.candidates := by
          simpa [instS', profile_with_switched] using (hwf instS').2 _ hW |>.2
        have hW0_card' :=
          inter_complement_card_of_mem inst c W0 hW0_sub hW0_card hW0_c
        have hW_card' :=
          inter_complement_card_of_not_mem inst c W hW_sub hW_card hcW
        intro hpref
        have hcomp := hpref W0 hW0 W hW
        have : k ≤ k - 1 := by
          simpa [committee_prefeq, hAi, hW0_card', hW_card'] using hcomp
        have hk : 1 ≤ k := Nat.succ_le_iff.mpr inst.k_pos
        have hlt : k - 1 < k := by
          simpa using (Nat.sub_lt_of_pos_le (a := 1) (b := k) (by decide) hk)
        exact (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt this hlt))
      have hpref : cautious_pref (instS.approves i) (f instS') (f instS) :=
        ⟨h_prefeq, h_not_prefeq⟩
      exact hsp instS instS' i hi_voter hvar hpref

  -- Apply the induction to S = non_singleton_voters.
  have h_all_S :
      ∀ W ∈ f (profile_with_switched inst c (non_singleton_voters inst c)), c ∈ W :=
    h_all (non_singleton_voters inst c) (by intro v hv; exact hv)

  -- Convert back to the original profile.
  have h_approves_eq : ∀ v ∈ inst.voters,
      (profile_with_switched inst c (non_singleton_voters inst c)).approves v =
        inst.approves v := by
    intro v hv
    exact profile_with_switched_all inst c v hv
  have h_ext : f (profile_with_switched inst c (non_singleton_voters inst c)) = f inst :=
    f.extensional _ _ rfl rfl h_approves_eq
  intro W hW
  have hW' : W ∈ f (profile_with_switched inst c (non_singleton_voters inst c)) := by
    simpa [h_ext] using hW
  exact h_all_S W hW'

end KluivingDeVriesVrijbergenBoixelEndriss.SingletonApprovers
