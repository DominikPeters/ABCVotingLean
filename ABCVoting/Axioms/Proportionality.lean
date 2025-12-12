import ABCVoting.ABCRule

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- PARTY-LIST PROFILES
-- ============================================================================

/--
A party-list profile is one where any two voters either have identical approval
sets or disjoint approval sets. This partitions voters into "parties" where
all members of a party approve exactly the same candidates.

Example: (ab, ab, cde, cde, f) is party-list, but (ab, c, c, abc) is not
(since ab and abc overlap but are not equal).
-/
def is_party_list (inst : ABCInstance V C k) : Prop :=
  ∀ v₁ ∈ inst.voters, ∀ v₂ ∈ inst.voters,
    inst.approves v₁ = inst.approves v₂ ∨ Disjoint (inst.approves v₁) (inst.approves v₂)

/--
In a party-list profile, if two voters both approve some candidate c,
then they have identical approval sets.
-/
lemma party_list_same_if_overlap (inst : ABCInstance V C k) (hpl : inst.is_party_list)
    (v₁ v₂ : V) (hv₁ : v₁ ∈ inst.voters) (hv₂ : v₂ ∈ inst.voters) (c : C)
    (hc₁ : c ∈ inst.approves v₁) (hc₂ : c ∈ inst.approves v₂) :
    inst.approves v₁ = inst.approves v₂ := by
  rcases hpl v₁ hv₁ v₂ hv₂ with heq | hdisj
  · exact heq
  · exfalso
    exact Finset.disjoint_iff_ne.mp hdisj c hc₁ c hc₂ rfl

-- ============================================================================
-- SINGLETON PARTY SIZE
-- ============================================================================

/--
The size of the singleton party for candidate c: the number of voters whose
approval set is exactly {c}.

This counts voters who approve ONLY candidate c (singleton ballots).
-/
def singleton_party_size (inst : ABCInstance V C k) (c : C) : ℕ :=
  (inst.voters.filter (fun v => inst.approves v = {c})).card

/--
The voters in the singleton party for c (those whose ballot is exactly {c}).
-/
def singleton_party (inst : ABCInstance V C k) (c : C) : Finset V :=
  inst.voters.filter (fun v => inst.approves v = {c})

/--
singleton_party_size equals the cardinality of singleton_party.
-/
lemma singleton_party_size_eq_card (inst : ABCInstance V C k) (c : C) :
    inst.singleton_party_size c = (inst.singleton_party c).card := rfl

/--
Members of a singleton party approve exactly {c}.
-/
lemma mem_singleton_party_iff (inst : ABCInstance V C k) (c : C) (v : V) :
    v ∈ inst.singleton_party c ↔ v ∈ inst.voters ∧ inst.approves v = {c} := by
  simp [singleton_party]

/--
Members of a singleton party approve c.
-/
lemma singleton_party_approves (inst : ABCInstance V C k) (c : C) (v : V)
    (hv : v ∈ inst.singleton_party c) : c ∈ inst.approves v := by
  rw [mem_singleton_party_iff] at hv
  rw [hv.2]
  exact Finset.mem_singleton_self c

/--
The singleton party for c is a subset of the supporters of c.
-/
lemma singleton_party_subset_supporters (inst : ABCInstance V C k) (c : C) :
    inst.singleton_party c ⊆ inst.supporters c := by
  intro v hv
  rw [mem_singleton_party_iff] at hv
  simp only [supporters, mem_filter]
  exact ⟨hv.1, by rw [hv.2]; exact Finset.mem_singleton_self c⟩

-- ============================================================================
-- PROPORTIONALITY AXIOM (PETERS' VERSION)
-- ============================================================================

/--
Proportionality axiom (Peters' weak version):

On party-list profiles, if a singleton ballot {c} appears at least n/k times
(i.e., singleton_party_size c * k ≥ voters.card), then c must be elected.

This is a very weak proportionality requirement: it only applies to party-list
profiles and only requires representing singleton parties (single-candidate parties)
that have sufficient support.

Note: The party-list condition allows non-singleton parties, but proportionality
only guarantees representation for singleton parties with sufficient support.
-/
def ABCRule.SatisfiesProportionality (f : ABCRule V C k) : Prop :=
  ∀ (inst : ABCInstance V C k) (c : C),
    inst.is_party_list →
    c ∈ inst.candidates →
    inst.singleton_party_size c * k ≥ inst.voters.card →
    ∀ W ∈ f inst, c ∈ W

/--
For a resolute rule satisfying proportionality, on party-list profiles,
sufficiently large singleton parties get their candidate in the committee.
-/
lemma ABCRule.resolute_proportionality (f : ABCRule V C k)
    (hres : f.IsResolute) (hprop : f.SatisfiesProportionality)
    (inst : ABCInstance V C k) (c : C)
    (hpl : inst.is_party_list)
    (hc_cand : c ∈ inst.candidates)
    (h_size : inst.singleton_party_size c * k ≥ inst.voters.card) :
    c ∈ f.resolute_committee inst hres :=
  hprop inst c hpl hc_cand h_size _ (f.resolute_committee_mem inst hres)

-- ============================================================================
-- QUOTA CALCULATIONS
-- ============================================================================

/--
A singleton party of size ≥ n/k satisfies the proportionality threshold.
(Using the integer formulation: size * k ≥ n)

Note: With floor division, size ≥ ⌊n/k⌋ only gives size * k ≥ n - (k-1).
This lemma is only useful when combined with divisibility or ceiling bounds.
-/
lemma singleton_party_threshold_of_ge_quota (inst : ABCInstance V C k) (c : C)
    (h : inst.singleton_party_size c ≥ inst.voters.card / k) :
    inst.singleton_party_size c * k ≥ inst.voters.card - inst.voters.card % k := by
  calc inst.singleton_party_size c * k
      ≥ (inst.voters.card / k) * k := Nat.mul_le_mul_right _ h
    _ = inst.voters.card - inst.voters.card % k := Nat.div_mul_self_eq_mod_sub_self

/--
When k divides n, singleton_party_size c ≥ n/k implies the threshold exactly.
-/
lemma singleton_party_threshold_of_div (inst : ABCInstance V C k) (c : C)
    (hdiv : k ∣ inst.voters.card)
    (h : inst.singleton_party_size c ≥ inst.voters.card / k) :
    inst.singleton_party_size c * k ≥ inst.voters.card := by
  have : inst.voters.card / k * k = inst.voters.card :=
    Nat.div_mul_cancel hdiv
  calc inst.singleton_party_size c * k
      ≥ (inst.voters.card / k) * k := Nat.mul_le_mul_right _ h
    _ = inst.voters.card := this

end ABCInstance
