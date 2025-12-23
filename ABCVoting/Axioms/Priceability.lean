import ABCVoting.ABCRule

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- PRICE SYSTEMS
-- ============================================================================

/--
A price system assigns to each voter i a payment function p_i : C → ℝ.
The payment p_i(c) represents how much voter i pays for candidate c.
-/
def PriceSystem (V C : Type*) := V → C → ℝ

/--
Total payment to candidate c from all voters.
-/
def PriceSystem.total_payment (p : PriceSystem V C) (inst : ABCInstance V C k) (c : C) : ℝ :=
  ∑ i ∈ inst.voters, p i c

/--
Total spending by voter i.
-/
def PriceSystem.spending (p : PriceSystem V C) (inst : ABCInstance V C k) (i : V) : ℝ :=
  ∑ c ∈ inst.candidates, p i c

/--
Unspent budget of voter i.
-/
def PriceSystem.unspent (p : PriceSystem V C) (inst : ABCInstance V C k) (b : ℝ) (i : V) : ℝ :=
  b - p.spending inst i

-- ============================================================================
-- PRICE SYSTEM PROPERTIES (C1-C5)
-- ============================================================================

/--
(C1) Voters pay only for candidates they approve.
p_i(c) = 0 for each i ∈ N and c ∉ A(i)
-/
def PriceSystem.pays_only_approved (p : PriceSystem V C) (inst : ABCInstance V C k) : Prop :=
  ∀ i ∈ inst.voters, ∀ c, c ∉ inst.approves i → p i c = 0

/--
(C2) Voters do not spend more than their allotted budget.
∑_{c ∈ C} p_i(c) ≤ b for each i ∈ N
-/
def PriceSystem.within_budget (p : PriceSystem V C) (inst : ABCInstance V C k) (b : ℝ) : Prop :=
  ∀ i ∈ inst.voters, p.spending inst i ≤ b

/--
(C3) Each elected candidate gets a total payment of 1.
∑_{i ∈ N} p_i(c) = 1 for each c ∈ W
-/
def PriceSystem.elected_paid_one (p : PriceSystem V C) (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∀ c ∈ W, p.total_payment inst c = 1

/--
(C4) Candidates that are not elected receive no payments.
∑_{i ∈ N} p_i(c) = 0 for each c ∈ C \ W
-/
def PriceSystem.non_elected_unpaid (p : PriceSystem V C) (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∀ c ∈ inst.candidates \ W, p.total_payment inst c = 0

/--
(C5) Exhaustiveness: No group of voters who approve a non-elected candidate
can afford to pay for them.
∑_{i ∈ N(c)} (b - ∑_{c' ∈ W} p_i(c')) ≤ 1 for each c ∉ W

Note: The book uses "c' ∈ W" in the inner sum, but the spending is over all candidates.
Since non-elected candidates get 0 total payment (C4), and voters only pay for approved
candidates (C1), effectively only payments to elected approved candidates matter.
We use the general spending for clarity.
-/
def PriceSystem.exhaustive (p : PriceSystem V C) (inst : ABCInstance V C k) (W : Finset C) (b : ℝ) : Prop :=
  ∀ c ∈ inst.candidates \ W,
    ∑ i ∈ inst.supporters c, p.unspent inst b i ≤ 1

/--
Non-negativity: All payments are non-negative.
This is implicit in the book (p_i : C → [0, 1]) but we make it explicit.
-/
def PriceSystem.nonneg (p : PriceSystem V C) (inst : ABCInstance V C k) : Prop :=
  ∀ i ∈ inst.voters, ∀ c, 0 ≤ p i c

/--
Bounded payments: All payments are at most 1.
This is implicit in the book (p_i : C → [0, 1]) but we make it explicit.
-/
def PriceSystem.bounded (p : PriceSystem V C) : Prop :=
  ∀ i c, p i c ≤ 1

-- ============================================================================
-- PRICEABILITY
-- ============================================================================

/--
A price system is valid for committee W with budget b if it satisfies all
the basic well-formedness conditions (C1-C4) plus non-negativity.
-/
def PriceSystem.is_valid (p : PriceSystem V C) (inst : ABCInstance V C k)
    (W : Finset C) (b : ℝ) : Prop :=
  p.nonneg inst ∧
  p.pays_only_approved inst ∧
  p.within_budget inst b ∧
  p.elected_paid_one inst W ∧
  p.non_elected_unpaid inst W

/--
A price system witnesses priceability of W if it satisfies C1-C5 plus non-negativity.
-/
def PriceSystem.witnesses_priceability (p : PriceSystem V C) (inst : ABCInstance V C k)
    (W : Finset C) (b : ℝ) : Prop :=
  p.is_valid inst W b ∧ p.exhaustive inst W b

/--
A set W is priceable if there exists a budget b ≥ 0 and a price system
satisfying conditions (C1)-(C5).

Note: The definition does not depend on the target committee size k;
it is a property of a set, not necessarily a committee.
-/
def is_priceable (inst : ABCInstance V C k) (W : Finset C) : Prop :=
  ∃ (b : ℝ) (p : PriceSystem V C), 0 ≤ b ∧ p.witnesses_priceability inst W b

/--
An ABC rule is priceable if every winning committee it returns is priceable.
-/
def ABCRule.SatisfiesPriceability (f : ABCRule V C k) : Prop :=
  ∀ (inst : ABCInstance V C k), ∀ W ∈ f inst, inst.is_priceable W

-- ============================================================================
-- ALTERNATIVE CHARACTERIZATIONS
-- ============================================================================

/--
Alternative unfolding: A set is priceable iff there exist b and p satisfying
all six conditions explicitly.
-/
lemma is_priceable_iff (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_priceable W ↔
    ∃ (b : ℝ) (p : PriceSystem V C),
      0 ≤ b ∧
      p.nonneg inst ∧
      p.pays_only_approved inst ∧
      p.within_budget inst b ∧
      p.elected_paid_one inst W ∧
      p.non_elected_unpaid inst W ∧
      p.exhaustive inst W b := by
  simp only [is_priceable, PriceSystem.witnesses_priceability, PriceSystem.is_valid]
  constructor
  · rintro ⟨b, p, hb, ⟨hnonneg, happr, hbudget, helect, hnonelect⟩, hexhaust⟩
    exact ⟨b, p, hb, hnonneg, happr, hbudget, helect, hnonelect, hexhaust⟩
  · rintro ⟨b, p, hb, hnonneg, happr, hbudget, helect, hnonelect, hexhaust⟩
    exact ⟨b, p, hb, ⟨hnonneg, happr, hbudget, helect, hnonelect⟩, hexhaust⟩

-- ============================================================================
-- BASIC LEMMAS
-- ============================================================================

/--
If a voter doesn't approve a candidate, they contribute 0 to its total payment.
-/
lemma PriceSystem.payment_zero_of_not_approved (p : PriceSystem V C)
    (inst : ABCInstance V C k) (i : V) (c : C)
    (hi : i ∈ inst.voters) (hc : c ∉ inst.approves i)
    (happr : p.pays_only_approved inst) : p i c = 0 :=
  happr i hi c hc

/--
Total payment to a candidate only comes from its supporters.
-/
lemma PriceSystem.total_payment_eq_supporters (p : PriceSystem V C)
    (inst : ABCInstance V C k) (c : C)
    (happr : p.pays_only_approved inst) :
    p.total_payment inst c = ∑ i ∈ inst.supporters c, p i c := by
  unfold total_payment supporters
  rw [← Finset.sum_filter_add_sum_filter_not inst.voters (c ∈ inst.approves ·)]
  have h : ∑ x ∈ inst.voters.filter (c ∉ inst.approves ·), p x c = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter] at hi
    exact happr i hi.1 c hi.2
  rw [h, add_zero]

end ABCInstance
