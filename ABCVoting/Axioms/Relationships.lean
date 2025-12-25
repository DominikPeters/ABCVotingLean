import ABCVoting.Axioms.JRAxioms
import ABCVoting.Axioms.Core
import ABCVoting.Axioms.Priceability

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

-- ============================================================================
-- IMPLICATIONS BETWEEN AXIOMS
-- ============================================================================

/--
EJR+ implies EJR: If a committee satisfies EJR+ (the stronger condition),
then it automatically satisfies EJR (the weaker condition).

**Proof sketch:**
Suppose W satisfies EJR+ and S is ℓ-cohesive.
- If all common approvals are in W, then any voter in S has ≥ ℓ approved candidates.
- Otherwise, some common approval c is not in W. Since S is ℓ-large and all voters
  in S approve c, EJR+ applies and gives us a voter with ≥ ℓ approved candidates.
-/
theorem ejr_plus_implies_ejr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_ejr_plus W → inst.is_ejr W := by
  intro h_ejr_plus S l h_S_subset hl_pos ⟨h_large, h_common⟩
  -- Either all common approvals are in W, or some is missing
  by_cases h_sub : inst.common_approvals S ⊆ W
  -- Case 1: All common approvals in W → any voter in S has ≥ l in W
  · obtain ⟨i, hi⟩ := l_large_nonempty inst S l hl_pos h_large
    refine ⟨i, hi, h_common.trans (Finset.card_le_card ?_)⟩
    exact fun c hc => Finset.mem_inter.mpr
      ⟨h_sub hc, (mem_common_approvals_iff inst S c).mp hc |>.2 i hi⟩
  -- Case 2: Some common approval c ∉ W → apply EJR+
  · obtain ⟨c, hc_common, hc_not_in_W⟩ := Finset.not_subset.mp h_sub
    have hc := (mem_common_approvals_iff inst S c).mp hc_common
    exact h_ejr_plus S l h_S_subset hl_pos
      ⟨h_large, c, Finset.mem_sdiff.mpr ⟨hc.1, hc_not_in_W⟩, hc.2⟩

/--
EJR implies JR: JR is the special case of EJR with ℓ = 1.
-/
theorem ejr_implies_jr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_ejr W → inst.is_jr W := by
  intro h_ejr S h_S_subset h_cond
  exact h_ejr S 1 h_S_subset (le_refl 1) h_cond

/--
EJR implies PJR: If some voter has utility ≥ ℓ, then the coalition's
coverage is also ≥ ℓ (since that voter's approved candidates are in the union).
-/
theorem ejr_implies_pjr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_ejr W → inst.is_pjr W := by
  intro h_ejr S l h_S_subset hl_pos h_cond
  obtain ⟨i, hi_in_S, hi_util⟩ := h_ejr S l h_S_subset hl_pos h_cond
  -- The voter i's approved candidates in W are a subset of the coalition's coverage
  calc (W ∩ inst.union_approvals S).card
      ≥ (W ∩ inst.approves i).card := by
        apply Finset.card_le_card
        intro c hc
        simp only [mem_inter, union_approvals, mem_biUnion] at hc ⊢
        exact ⟨hc.1, i, hi_in_S, hc.2⟩
    _ ≥ l := hi_util

/--
PJR+ implies PJR: Same structure as EJR+ implies EJR.
-/
theorem pjr_plus_implies_pjr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_pjr_plus W → inst.is_pjr W := by
  intro h_pjr_plus S l h_S_subset hl_pos ⟨h_large, h_common⟩
  by_cases h_sub : inst.common_approvals S ⊆ W
  -- Case 1: All common approvals in W → coalition coverage ≥ l
  · obtain ⟨i, hi⟩ := l_large_nonempty inst S l hl_pos h_large
    have h_common_subset_union : inst.common_approvals S ⊆ inst.union_approvals S := by
      intro c hc
      simp only [union_approvals, mem_biUnion]
      exact ⟨i, hi, (mem_common_approvals_iff inst S c).mp hc |>.2 i hi⟩
    calc (W ∩ inst.union_approvals S).card
        ≥ (inst.common_approvals S).card := by
          apply Finset.card_le_card
          intro c hc
          exact mem_inter.mpr ⟨h_sub hc, h_common_subset_union hc⟩
      _ ≥ l := h_common
  -- Case 2: Some common approval c ∉ W → apply PJR+
  · obtain ⟨c, hc_common, hc_not_in_W⟩ := Finset.not_subset.mp h_sub
    have hc := (mem_common_approvals_iff inst S c).mp hc_common
    exact h_pjr_plus S l h_S_subset hl_pos
      ⟨h_large, c, Finset.mem_sdiff.mpr ⟨hc.1, hc_not_in_W⟩, hc.2⟩

/--
Core implies Disjoint Core: The core is a stronger condition since it considers
all possible alternatives T, while the disjoint core only considers T disjoint from W.
-/
theorem core_implies_disjoint_core (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_in_core W → inst.is_in_disjoint_core W := by
  intro h_core S T l h_S_subset h_T_subset _ hl_pos h_cond
  exact h_core S T l h_S_subset h_T_subset hl_pos h_cond

/--
Core implies Sub-core: If W is in the core, then W is in the sub-core.

The sub-core only prevents deviations where every voter strictly improves
(W ∩ A_i ⊊ T ∩ A_i for all i ∈ S), which is weaker than the core's requirement
that some voter has utility at least as high in W as in T.

Reference: "Auditing for Core Stability in Participatory Budgeting"
by Munagala, Shen, Wang (WINE 2022)
-/
theorem core_implies_sub_core (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_in_core W → inst.is_in_sub_core W := by
  intro h_core S T h_S_subset h_T_subset h_S_nonempty h_size_cond
  by_cases hT_empty : T = ∅
  · -- T is empty: T ∩ A_i = ∅, and nothing is a proper subset of ∅
    obtain ⟨i, hi⟩ := h_S_nonempty
    exact ⟨i, hi, by
      simpa [hT_empty] using (Finset.not_ssubset_empty (W ∩ inst.approves i))⟩
  · -- T is nonempty: use the core with l = T.card
    have hT_card_pos : T.card ≥ 1 :=
      Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hT_empty)
    have h_l_large : inst.is_l_large S T.card := h_size_cond
    obtain ⟨i, hi, h_card_ge⟩ := h_core S T T.card h_S_subset h_T_subset hT_card_pos
      ⟨h_l_large, le_refl _⟩
    -- If |W ∩ A_i| ≥ |T ∩ A_i|, then ¬(W ∩ A_i ⊊ T ∩ A_i)
    exact ⟨i, hi, fun h_ssubset => (Finset.card_lt_card h_ssubset).not_ge h_card_ge⟩

/--
Core implies FJR: If u_i(W) ≥ u_i(T) for some voter, and all voters have u_i(T) ≥ β,
then that voter has u_i(W) ≥ β.
-/
theorem core_implies_fjr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_in_core W → inst.is_fjr W := by
  intro h_core S T l β h_S_subset h_T_subset hl_pos hβ_pos ⟨h_large, h_T_small, h_all_β⟩
  obtain ⟨i, hi_in_S, hi_pref⟩ := h_core S T l h_S_subset h_T_subset hl_pos ⟨h_large, h_T_small⟩
  refine ⟨i, hi_in_S, ?_⟩
  calc (W ∩ inst.approves i).card
      ≥ (T ∩ inst.approves i).card := hi_pref
    _ = (inst.approves i ∩ T).card := by rw [inter_comm]
    _ ≥ β := h_all_β i hi_in_S

/--
FJR implies EJR: EJR is a special case of FJR where T is the common approvals
and β = ℓ. Since every voter in S approves all of common_approvals(S), each has
u_i(T) ≥ ℓ.
-/
theorem fjr_implies_ejr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_fjr W → inst.is_ejr W := by
  intro h_fjr S l h_S_subset hl_pos ⟨h_large, h_common⟩
  -- Take T to be a subset of common_approvals of size exactly l
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq h_common
  have hT_cand : T ⊆ inst.candidates := by
    intro c hc
    exact ((mem_common_approvals_iff inst S c).mp (hT_sub hc)).1
  have hT_all_l : ∀ i ∈ S, (inst.approves i ∩ T).card ≥ l := by
    intro i hi
    have : T ⊆ inst.approves i := by
      intro c hc
      exact ((mem_common_approvals_iff inst S c).mp (hT_sub hc)).2 i hi
    simp only [inter_eq_right.mpr this, hT_card, le_refl]
  exact h_fjr S T l l h_S_subset hT_cand hl_pos hl_pos ⟨h_large, hT_card.le, hT_all_l⟩

/--
FJR implies FPJR: Same argument as EJR implies PJR.
-/
theorem fjr_implies_fpjr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_fjr W → inst.is_fpjr W := by
  intro h_fjr S T l β h_S_subset h_T_subset hl_pos hβ_pos h_cond
  obtain ⟨i, hi_in_S, hi_util⟩ := h_fjr S T l β h_S_subset h_T_subset hl_pos hβ_pos h_cond
  calc (W ∩ inst.union_approvals S).card
      ≥ (W ∩ inst.approves i).card := by
        apply Finset.card_le_card
        intro c hc
        simp only [mem_inter, union_approvals, mem_biUnion] at hc ⊢
        exact ⟨hc.1, i, hi_in_S, hc.2⟩
    _ ≥ β := hi_util

/--
FPJR implies PJR: PJR is a special case of FPJR where T is the common approvals
and β = ℓ.
-/
theorem fpjr_implies_pjr (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_fpjr W → inst.is_pjr W := by
  intro h_fpjr S l h_S_subset hl_pos ⟨h_large, h_common⟩
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq h_common
  have hT_cand : T ⊆ inst.candidates := by
    intro c hc
    exact ((mem_common_approvals_iff inst S c).mp (hT_sub hc)).1
  have hT_all_l : ∀ i ∈ S, (inst.approves i ∩ T).card ≥ l := by
    intro i hi
    have : T ⊆ inst.approves i := by
      intro c hc
      exact ((mem_common_approvals_iff inst S c).mp (hT_sub hc)).2 i hi
    simp only [inter_eq_right.mpr this, hT_card, le_refl]
  exact h_fpjr S T l l h_S_subset hT_cand hl_pos hl_pos ⟨h_large, hT_card.le, hT_all_l⟩

-- ============================================================================
-- PRICEABILITY IMPLIES PJR+
-- ============================================================================

/--
For a valid price system, voters only pay for approved elected candidates.
Since non-elected candidates receive 0 total payment (C4), and payments are
non-negative, each individual payment to a non-elected candidate is 0.
-/
lemma PriceSystem.pays_only_elected (p : PriceSystem V C) (inst : ABCInstance V C k)
    (W : Finset C) (b : ℝ) (hvalid : p.is_valid inst W b)
    (i : V) (hi : i ∈ inst.voters) (c : C) (hc : c ∈ inst.candidates) (hcW : c ∉ W) :
    p i c = 0 := by
  by_cases happ : c ∈ inst.approves i
  · -- c is approved by i, but not elected
    have h_total : p.total_payment inst c = 0 := hvalid.2.2.2.2 c (mem_sdiff.mpr ⟨hc, hcW⟩)
    have h_nonneg : ∀ j ∈ inst.voters, 0 ≤ p j c := fun j hj => hvalid.1 j hj c
    -- If sum of non-negatives is 0, each term is 0
    have h_sum_zero : ∑ j ∈ inst.voters, p j c = 0 := h_total
    exact Finset.sum_eq_zero_iff_of_nonneg h_nonneg |>.mp h_sum_zero i hi
  · -- c is not approved by i
    exact hvalid.2.1 i hi c happ

/--
A voter's spending is entirely on approved elected candidates.
-/
lemma PriceSystem.spending_eq_elected_approved (p : PriceSystem V C) (inst : ABCInstance V C k)
    (W : Finset C) (b : ℝ) (hvalid : p.is_valid inst W b) (hW_sub : W ⊆ inst.candidates)
    (i : V) (hi : i ∈ inst.voters) :
    p.spending inst i = ∑ c ∈ W ∩ inst.approves i, p i c := by
  unfold spending
  rw [← Finset.sum_filter_add_sum_filter_not inst.candidates (· ∈ W ∩ inst.approves i)]
  have h_rest_zero : ∑ x ∈ inst.candidates.filter (· ∉ W ∩ inst.approves i), p i x = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    simp only [mem_filter, mem_inter, not_and] at hc
    by_cases hcW : c ∈ W
    · -- c ∈ W but c ∉ approves i
      have hc_not_app : c ∉ inst.approves i := by
        intro h_app
        exact hc.2 hcW h_app
      exact hvalid.2.1 i hi c hc_not_app
    · -- c ∉ W
      exact p.pays_only_elected inst W b hvalid i hi c hc.1 hcW
  rw [h_rest_zero, add_zero]
  congr 1
  ext c
  simp only [mem_filter, mem_inter]
  constructor
  · intro ⟨_, hc⟩; exact hc
  · intro ⟨hcW, hcA⟩; exact ⟨hW_sub hcW, hcW, hcA⟩

/--
Total spending by a group S is at most the number of candidates in W that S members approve.
This is because each candidate in W receives total payment 1, and S can only contribute
to candidates that its members approve.
-/
lemma PriceSystem.group_spending_le (p : PriceSystem V C) (inst : ABCInstance V C k)
    (W : Finset C) (b : ℝ) (hvalid : p.is_valid inst W b) (hW_sub : W ⊆ inst.candidates)
    (S : Finset V) (hS : S ⊆ inst.voters) :
    ∑ i ∈ S, p.spending inst i ≤ (W ∩ inst.union_approvals S).card := by
  -- Key idea: total spending by S on each candidate c ∈ W ∩ union_approvals is at most 1
  -- (since total payment to c from all voters is 1), and S can only pay for candidates
  -- in W ∩ union_approvals S.
  have h_spending : ∀ i ∈ S, p.spending inst i = ∑ c ∈ W ∩ inst.approves i, p i c := by
    intro i hi
    exact p.spending_eq_elected_approved inst W b hvalid hW_sub i (hS hi)
  -- Each voter in S only pays for candidates in W ∩ union_approvals S
  have h_subset : ∀ i ∈ S, W ∩ inst.approves i ⊆ W ∩ inst.union_approvals S := by
    intro i hi c hc
    simp only [mem_inter, union_approvals, mem_biUnion] at hc ⊢
    exact ⟨hc.1, i, hi, hc.2⟩
  -- Bound the sum
  calc ∑ i ∈ S, p.spending inst i
      = ∑ i ∈ S, ∑ c ∈ W ∩ inst.approves i, p i c := by
        apply Finset.sum_congr rfl h_spending
    _ ≤ ∑ i ∈ S, ∑ c ∈ W ∩ inst.union_approvals S, p i c := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum_of_subset_of_nonneg (h_subset i hi)
        intro c _ _
        exact hvalid.1 i (hS hi) c
    _ = ∑ c ∈ W ∩ inst.union_approvals S, ∑ i ∈ S, p i c := Finset.sum_comm
    _ ≤ ∑ c ∈ W ∩ inst.union_approvals S, p.total_payment inst c := by
        apply Finset.sum_le_sum
        intro c _
        unfold total_payment
        apply Finset.sum_le_sum_of_subset_of_nonneg hS
        intro i hi _
        exact hvalid.1 i hi c
    _ = ∑ _ ∈ W ∩ inst.union_approvals S, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hvalid.2.2.2.1 c (mem_inter.mp hc).1
    _ = (W ∩ inst.union_approvals S).card := by simp

/--
If |W ∩ union_approvals S| < ℓ, then S's total spending is at most ℓ - 1.
-/
lemma group_spending_bound (p : PriceSystem V C) (inst : ABCInstance V C k)
    (W : Finset C) (b : ℝ) (hvalid : p.is_valid inst W b) (hW_sub : W ⊆ inst.candidates)
    (S : Finset V) (hS : S ⊆ inst.voters) (l : ℕ)
    (h_coverage : (W ∩ inst.union_approvals S).card < l) :
    ∑ i ∈ S, p.spending inst i ≤ l - 1 := by
  have h := p.group_spending_le inst W b hvalid hW_sub S hS
  have hcard_nat : (W ∩ inst.union_approvals S).card ≤ l - 1 := Nat.le_sub_one_of_lt h_coverage
  have hl1 : 1 ≤ l := Nat.one_le_of_lt h_coverage
  have hcast : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - (1 : ℝ) := by
    simpa using (Nat.cast_sub hl1)
  have hcard : ((W ∩ inst.union_approvals S).card : ℝ) ≤ l - 1 := by
    rw [← hcast]; exact Nat.cast_le.mpr hcard_nat
  linarith

/--
Total payment to elected candidates equals the committee size.
-/
lemma PriceSystem.total_elected_payment (p : PriceSystem V C) (inst : ABCInstance V C k)
    (W : Finset C) (b : ℝ) (hvalid : p.is_valid inst W b) :
    ∑ c ∈ W, p.total_payment inst c = W.card := by
  have h : ∀ c ∈ W, p.total_payment inst c = 1 := hvalid.2.2.2.1
  trans (∑ _ ∈ W, (1 : ℝ))
  · exact Finset.sum_congr rfl h
  · simp

/--
If common approvals has ≥ ℓ candidates but W ∩ union_approvals has < ℓ,
then there exists a candidate approved by everyone in S that is not in W.
-/
lemma exists_common_not_in_W (inst : ABCInstance V C k) (W : Finset C)
    (S : Finset V) (l : ℕ) (hS_nonempty : S.Nonempty)
    (h_common : (inst.common_approvals S).card ≥ l)
    (h_coverage : (W ∩ inst.union_approvals S).card < l) :
    ∃ c ∈ inst.candidates \ W, ∀ i ∈ S, c ∈ inst.approves i := by
  -- common_approvals S ⊆ union_approvals S
  have h_common_sub_union : inst.common_approvals S ⊆ inst.union_approvals S := by
    intro c hc
    obtain ⟨i, hi⟩ := hS_nonempty
    simp only [union_approvals, mem_biUnion]
    exact ⟨i, hi, (mem_common_approvals_iff inst S c).mp hc |>.2 i hi⟩
  -- Since |common_approvals| ≥ l and |W ∩ union_approvals| < l, not all common approvals are in W
  have h_not_sub : ¬(inst.common_approvals S ⊆ W) := by
    intro h_sub
    have hsub : inst.common_approvals S ⊆ W ∩ inst.union_approvals S := by
      intro c hc
      exact mem_inter.mpr ⟨h_sub hc, h_common_sub_union hc⟩
    have hle : (inst.common_approvals S).card ≤ (W ∩ inst.union_approvals S).card :=
      Finset.card_le_card hsub
    omega
  obtain ⟨c, hc_common, hc_not_in_W⟩ := Finset.not_subset.mp h_not_sub
  have hc := (mem_common_approvals_iff inst S c).mp hc_common
  exact ⟨c, mem_sdiff.mpr ⟨hc.1, hc_not_in_W⟩, hc.2⟩

/--
Priceability implies PJR+: If a committee W of size k is priceable, then it satisfies PJR+.

**Proof sketch** (following Peters-Skowron):
Suppose W is priceable with budget b and price system p, and assume for contradiction that
|W ∩ ∪_{i∈S} A_i| < ℓ for some ℓ-cohesive group S.

1. Since voters only pay for approved elected candidates, S's total spending is
   at most |W ∩ ∪A_i| ≤ ℓ - 1 (each candidate gets total payment 1).
2. S's unspent budget is |S|·b - (spending) ≥ ℓnb/k - (ℓ-1).
3. Use the PJR+ premise: there exists c ∈ candidates \ W approved by all of S.
4. By exhaustiveness, supporters of c have unspent budget ≤ 1, so S's unspent budget ≤ 1.
5. We show k < nb (total payment < total budget), which gives ℓnb/k > ℓ,
   so unspent > 1, contradiction.
6. To show k < nb: If k = nb, then all money is spent, so S spends |S|b = all their budget.
   But |S| ≥ ℓn/k = ℓ/b, so S's budget is ≥ ℓ. Yet S can only spend on < ℓ candidates,
   each with total payment 1. So S's spending ≤ ℓ-1 < ℓ ≤ S's budget, contradiction.
-/
theorem priceable_implies_pjr_plus (inst : ABCInstance V C k) (W : Finset C)
    (hW_card : W.card = k) (hW_sub : W ⊆ inst.candidates) :
    inst.is_priceable W → inst.is_pjr_plus W := by
  intro ⟨b, p, hb_nonneg, hvalid, hexhaust⟩ S l hS_sub hl_pos ⟨h_large, h_c⟩
  -- Prove by contradiction: assume coverage < l
  by_contra h_not_pjr
  push_neg at h_not_pjr
  -- Step 1: Let c be approved by all of S but not in W (from the PJR+ premise)
  obtain ⟨c, hc_sdiff, hc_all_approve⟩ := h_c
  -- Step 2: S's spending is bounded by l - 1
  have h_spending_bound : ∑ i ∈ S, p.spending inst i ≤ l - 1 :=
    group_spending_bound p inst W b hvalid hW_sub S hS_sub l h_not_pjr
  -- Step 3: S's unspent budget
  have h_unspent_S : ∑ i ∈ S, p.unspent inst b i = S.card * b - ∑ i ∈ S, p.spending inst i := by
    simp only [PriceSystem.unspent, Finset.sum_sub_distrib, Finset.sum_const]
    ring
  -- Step 4: S is a subset of supporters of c
  have hS_supporters : S ⊆ inst.supporters c := by
    intro i hi
    simp only [supporters, mem_filter]
    exact ⟨hS_sub hi, hc_all_approve i hi⟩
  -- Step 5: By exhaustiveness, unspent budget of supporters of c is ≤ 1
  have h_exhaust_c : ∑ i ∈ inst.supporters c, p.unspent inst b i ≤ 1 := hexhaust c hc_sdiff
  -- Step 6: Therefore, S's unspent budget is ≤ 1
  have h_S_unspent_le : ∑ i ∈ S, p.unspent inst b i ≤ 1 := by
    calc ∑ i ∈ S, p.unspent inst b i
        ≤ ∑ i ∈ inst.supporters c, p.unspent inst b i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hS_supporters
          intro i hi _
          simp only [PriceSystem.unspent, supporters, mem_filter] at hi ⊢
          linarith [hvalid.2.2.1 i hi.1]
      _ ≤ 1 := h_exhaust_c
  -- Step 7: Lower bound on S's unspent budget
  -- From h_large: l * n ≤ |S| * k
  -- S's budget = |S| * b
  -- S's spending ≤ l - 1
  -- S's unspent ≥ |S| * b - (l - 1)
  have h_S_budget : (S.card : ℝ) * b ≥ l * inst.voters.card * b / k := by
    have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr inst.k_pos
    rw [ge_iff_le, div_le_iff₀ hk_pos]
    calc l * inst.voters.card * b
        = (l * inst.voters.card : ℕ) * b := by push_cast; ring
      _ ≤ (S.card * k : ℕ) * b := by
          apply mul_le_mul_of_nonneg_right _ hb_nonneg
          exact Nat.cast_le.mpr h_large
      _ = S.card * b * k := by push_cast; ring
  have h_unspent_lower : ∑ i ∈ S, p.unspent inst b i ≥ S.card * b - (l - 1) := by
    rw [h_unspent_S]
    linarith [h_spending_bound]
  -- Step 8: Key inequality - we need to show total payment k < total budget n * b
  -- Total payment to W is k (each of k candidates gets 1)
  -- If k = n * b, then all money is spent
  -- But then S would spend all their budget |S| * b ≥ l * n * b / k = l
  -- Yet S's spending ≤ l - 1 < l, contradiction
  -- So k < n * b, which means n * b / k > 1
  have h_total_payment : (∑ c ∈ W, p.total_payment inst c : ℝ) = k := by
    rw [p.total_elected_payment inst W b hvalid, hW_card]
  have h_total_spending_le : ∑ c ∈ W, p.total_payment inst c ≤ inst.voters.card * b := by
    calc ∑ c ∈ W, p.total_payment inst c
        = ∑ c ∈ W, ∑ i ∈ inst.voters, p i c := rfl
      _ = ∑ i ∈ inst.voters, ∑ c ∈ W, p i c := Finset.sum_comm
      _ ≤ ∑ i ∈ inst.voters, p.spending inst i := by
          apply Finset.sum_le_sum
          intro i hi
          calc ∑ c ∈ W, p i c
              ≤ ∑ c ∈ inst.candidates, p i c := by
                apply Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => hW_sub hc)
                intro c _ _
                exact hvalid.1 i hi c
            _ = p.spending inst i := rfl
      _ ≤ ∑ i ∈ inst.voters, b := by
          apply Finset.sum_le_sum
          intro i hi
          exact hvalid.2.2.1 i hi
      _ = inst.voters.card * b := by simp [Finset.sum_const]
  -- So k ≤ n * b
  have hk_le_nb : (k : ℝ) ≤ inst.voters.card * b := by
    calc (k : ℝ) = ∑ c ∈ W, p.total_payment inst c := h_total_payment.symm
      _ ≤ inst.voters.card * b := h_total_spending_le
  -- Now we show k < n * b (strict inequality)
  -- Suppose k = n * b. Then all money is spent, i.e., every voter spends exactly b.
  -- In particular, S spends exactly |S| * b.
  -- But S's spending ≤ l - 1, and |S| * b ≥ l * n * b / k = l (when k = n * b).
  -- So l ≤ l - 1, contradiction.
  have hk_lt_nb : (k : ℝ) < inst.voters.card * b := by
    by_contra h_eq_or_gt
    push_neg at h_eq_or_gt
    have hk_eq : (k : ℝ) = inst.voters.card * b := le_antisymm hk_le_nb h_eq_or_gt
    -- When k = n * b, total spending = total budget, so each voter spends exactly b
    -- This means S's total spending = |S| * b
    have h_all_spend_b : ∑ i ∈ inst.voters, p.spending inst i = inst.voters.card * b := by
      have h2 : (k : ℝ) ≤ ∑ i ∈ inst.voters, p.spending inst i := by
        calc (k : ℝ) = ∑ c ∈ W, p.total_payment inst c := h_total_payment.symm
          _ = ∑ c ∈ W, ∑ i ∈ inst.voters, p i c := rfl
          _ = ∑ i ∈ inst.voters, ∑ c ∈ W, p i c := Finset.sum_comm
          _ ≤ ∑ i ∈ inst.voters, p.spending inst i := by
              apply Finset.sum_le_sum; intro i hi
              apply Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => hW_sub hc)
              intro c _ _; exact hvalid.1 i hi c
      have h3 : ∑ i ∈ inst.voters, p.spending inst i ≤ inst.voters.card * b := by
        calc ∑ i ∈ inst.voters, p.spending inst i
            ≤ ∑ i ∈ inst.voters, b := by
              apply Finset.sum_le_sum; intro i hi; exact hvalid.2.2.1 i hi
          _ = inst.voters.card * b := by simp [Finset.sum_const]
      linarith
    -- Since every voter spends exactly b (equality from total = budget), S's spending = |S| * b
    have h_S_spending_eq : ∑ i ∈ S, p.spending inst i = S.card * b := by
      -- Each voter in S spends exactly b
      have h_each_b : ∀ i ∈ inst.voters, p.spending inst i = b := by
        intro i hi
        have hle : p.spending inst i ≤ b := hvalid.2.2.1 i hi
        have hge : p.spending inst i ≥ b := by
          by_contra hlt
          push_neg at hlt
          -- If some voter spends < b, total spending < n*b, contradiction
          have : ∑ j ∈ inst.voters, p.spending inst j < inst.voters.card * b := by
            calc ∑ j ∈ inst.voters, p.spending inst j
                = p.spending inst i + ∑ j ∈ inst.voters.erase i, p.spending inst j := by
                  rw [Finset.add_sum_erase _ _ hi]
              _ < b + ∑ j ∈ inst.voters.erase i, b := by
                  apply add_lt_add_of_lt_of_le hlt
                  apply Finset.sum_le_sum
                  intro j hj
                  exact hvalid.2.2.1 j (Finset.mem_of_mem_erase hj)
              _ = b + ((inst.voters.card : ℝ) - 1) * b := by
                  have hcard_pos : 1 ≤ inst.voters.card := Finset.card_pos.mpr inst.voters_nonempty
                  simp [Finset.sum_const, Finset.card_erase_of_mem hi, Nat.cast_sub hcard_pos]
              _ = inst.voters.card * b := by ring
          linarith [h_all_spend_b]
        linarith
      calc ∑ i ∈ S, p.spending inst i
          = ∑ i ∈ S, b := Finset.sum_congr rfl (fun i hi => h_each_b i (hS_sub hi))
        _ = S.card * b := by simp [Finset.sum_const]
    -- S's budget ≥ l (since nb/k = 1 when k = nb)
    have h_S_budget_ge_l : (S.card : ℝ) * b ≥ l := by
      calc S.card * b
          ≥ l * inst.voters.card * b / k := h_S_budget
        _ = l * (inst.voters.card * b / k) := by ring
        _ = l * (k / k) := by rw [hk_eq]
        _ = l * 1 := by rw [div_self (ne_of_gt (Nat.cast_pos.mpr inst.k_pos))]
        _ = l := by ring
    -- Contradiction: S's spending = S's budget ≥ l, but S's spending ≤ l - 1
    have h_contradiction : (l : ℝ) ≤ l - 1 := by
      calc (l : ℝ) ≤ S.card * b := h_S_budget_ge_l
        _ = ∑ i ∈ S, p.spending inst i := h_S_spending_eq.symm
        _ ≤ l - 1 := h_spending_bound
    linarith
  -- Now we can derive the final contradiction
  -- S's unspent ≥ |S| * b - (l - 1) ≥ l * n * b / k - l + 1 > l * 1 - l + 1 = 1
  have h_final : ∑ i ∈ S, p.unspent inst b i > 1 := by
    have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr inst.k_pos
    have h_ratio_gt_one : inst.voters.card * b / k > 1 :=
      (one_lt_div hk_pos).mpr hk_lt_nb
    calc ∑ i ∈ S, p.unspent inst b i
        ≥ S.card * b - (l - 1) := h_unspent_lower
      _ ≥ l * inst.voters.card * b / k - (l - 1) := by linarith [h_S_budget]
      _ = l * (inst.voters.card * b / k) - l + 1 := by ring
      _ > l * 1 - l + 1 := by
          have : l * (inst.voters.card * b / k) > l * 1 := by
            apply mul_lt_mul_of_pos_left h_ratio_gt_one
            exact Nat.cast_pos.mpr hl_pos
          linarith
      _ = 1 := by ring
  linarith

/--
Priceability implies PJR: immediate from priceability implies PJR+ and PJR+ implies PJR.
-/
theorem priceable_implies_pjr (inst : ABCInstance V C k) (W : Finset C)
    (hW_card : W.card = k) (hW_sub : W ⊆ inst.candidates) :
    inst.is_priceable W → inst.is_pjr W := by
  intro h_priceable
  have h_pjr_plus : inst.is_pjr_plus W :=
    priceable_implies_pjr_plus inst W hW_card hW_sub h_priceable
  exact pjr_plus_implies_pjr inst W h_pjr_plus

-- ============================================================================
-- LINDAHL AND WEAK PRICEABILITY RELATIONSHIPS
-- ============================================================================

/--
Lindahl priceability implies weak priceability: the same price system works.

**Proof sketch:** Given d ∈ A_i \ W, take T = {d} ∪ (A_i ∩ W). Since d ∉ W,
we have |A_i ∩ T| = 1 + |A_i ∩ W| > |A_i ∩ W|. By Lindahl exhaustiveness,
Σ_{c ∈ T} p i c > 1, which equals p i d + Σ_{c ∈ A_i ∩ W} p i c.
-/
theorem lindahl_priceable_implies_weakly_priceable (inst : ABCInstance V C k) (W : Finset C)
    (hW_sub : W ⊆ inst.candidates) :
    inst.is_lindahl_priceable W → inst.is_weakly_priceable W := by
  intro ⟨p, h_nonneg, h_bounded, h_lindahl⟩
  refine ⟨p, h_nonneg, h_bounded, ?_⟩
  -- Show weak exhaustiveness
  intro i hi d hd
  -- d ∈ (A_i ∩ candidates) \ W
  simp only [mem_sdiff, mem_inter] at hd
  obtain ⟨⟨hd_app, hd_cand⟩, hd_notW⟩ := hd
  -- Take T = {d} ∪ (A_i ∩ W)
  set T := {d} ∪ (inst.approves i ∩ W) with hT_def
  have hT_sub : T ⊆ inst.candidates := by
    intro c hc
    rw [hT_def] at hc
    simp only [mem_union, mem_singleton, mem_inter] at hc
    rcases hc with rfl | ⟨_, hcW⟩
    · exact hd_cand
    · exact hW_sub hcW
  -- |A_i ∩ T| = 1 + |A_i ∩ W|
  have hd_not_in : d ∉ inst.approves i ∩ W := by
    simp only [mem_inter, not_and]
    intro _; exact hd_notW
  have h1 : inst.approves i ∩ T = {d} ∪ (inst.approves i ∩ W) := by
    rw [hT_def]
    ext c
    simp only [mem_inter, mem_union, mem_singleton]
    constructor
    · intro ⟨hc_app, hc_T⟩
      rcases hc_T with rfl | ⟨hc_app', hcW⟩
      · left; rfl
      · right; exact ⟨hc_app', hcW⟩
    · intro hc
      rcases hc with rfl | ⟨hc_app, hcW⟩
      · exact ⟨hd_app, Or.inl rfl⟩
      · exact ⟨hc_app, Or.inr ⟨hc_app, hcW⟩⟩
  have hT_card : (inst.approves i ∩ T).card = (inst.approves i ∩ W).card + 1 := by
    rw [h1, card_union_of_disjoint (disjoint_singleton_left.mpr hd_not_in), card_singleton]
    ring
  -- Apply Lindahl exhaustiveness
  have h_gt : (inst.approves i ∩ T).card > (inst.approves i ∩ W).card := by omega
  have h_sum : ∑ c ∈ T, p i c > 1 := h_lindahl i hi T hT_sub h_gt
  -- The sum over T equals p i d + sum over A_i ∩ W
  have h_sum_eq : ∑ c ∈ T, p i c = p i d + ∑ c ∈ inst.approves i ∩ W, p i c := by
    rw [hT_def, sum_union (disjoint_singleton_left.mpr hd_not_in), sum_singleton]
  linarith

/--
Priceability (Peters-Skowron) implies weak priceability (Munagala et al.).
Proof from "On the Edge of Core (Non-)Emptiness: An Automated
Reasoning Approach to Approval-Based Multi-Winner Voting", Appendix E.1
Ratip Emin Berker, Emanuel Tewolde, Vincent Conitzer, Mingyu Guo, Marijn Heule, and Lirong Xia
https://arxiv.org/pdf/2512.16895

**Proof sketch:**
Given (b, p) satisfying priceability, construct q as:
- q i c = p i c / b for c ∈ W
- q i c = unspent_i / b + ε for c ∈ A_i ∩ C \ W, where ε > 0 is small
- q i c = 0 otherwise

Key facts:
1. Total payment = k, total budget = n·b, so k ≤ n·b (i.e., 1/b ≤ n/k)
2. By exhaustiveness: Σ_{i: c ∈ A_i} unspent_i ≤ 1 for c ∉ W

For c ∈ W: Σ_i q i c = 1/b ≤ n/k ✓
For c ∉ W: Σ_i q i c ≤ 1/b + n·ε, choose ε small enough that this ≤ n/k

For weak exhaustiveness:
q i d + Σ_{c ∈ A_i ∩ W} q i c = unspent/b + ε + spending/b = 1 + ε > 1 ✓
-/
theorem priceable_implies_weakly_priceable (inst : ABCInstance V C k) (W : Finset C)
    (hW_card : W.card = k) (hW_sub : W ⊆ inst.candidates) :
    inst.is_priceable W → inst.is_weakly_priceable W := by
  intro ⟨b, p, hb_nonneg, hvalid, hexhaust⟩
  -- b > 0 (since each elected candidate gets total payment 1, and W is nonempty)
  have hb_pos : 0 < b := by
    by_contra hb_le
    push_neg at hb_le
    have hb_eq : b = 0 := le_antisymm hb_le hb_nonneg
    -- If b = 0, all spending is 0
    have h_spend_zero : ∀ i ∈ inst.voters, p.spending inst i = 0 := by
      intro i hi
      have h_spend_le : p.spending inst i ≤ b := hvalid.2.2.1 i hi
      rw [hb_eq] at h_spend_le
      have h_nonneg : 0 ≤ p.spending inst i := Finset.sum_nonneg (fun c _ => hvalid.1 i hi c)
      linarith
    -- So each p i c = 0 for c ∈ candidates
    have h_zero_cand : ∀ i ∈ inst.voters, ∀ c ∈ inst.candidates, p i c = 0 := by
      intro i hi c hc
      have h_le : p i c ≤ p.spending inst i := Finset.single_le_sum (fun c _ => hvalid.1 i hi c) hc
      have h_nonneg : 0 ≤ p i c := hvalid.1 i hi c
      linarith [h_spend_zero i hi]
    -- But W ⊆ candidates and elected_paid_one says Σ_i p i c = 1 for c ∈ W
    obtain ⟨c, hc⟩ := Finset.card_pos.mp (hW_card.symm ▸ inst.k_pos)
    have h_one : p.total_payment inst c = 1 := hvalid.2.2.2.1 c hc
    have h_zero : p.total_payment inst c = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact h_zero_cand i hi c (hW_sub hc)
    linarith
  -- Key bound: k ≤ n·b
  have hk_le_nb : (k : ℝ) ≤ inst.voters.card * b := by
    calc (k : ℝ) = ∑ c ∈ W, p.total_payment inst c := by
            rw [p.total_elected_payment inst W b hvalid, hW_card]
      _ = ∑ c ∈ W, ∑ i ∈ inst.voters, p i c := rfl
      _ = ∑ i ∈ inst.voters, ∑ c ∈ W, p i c := Finset.sum_comm
      _ ≤ ∑ i ∈ inst.voters, p.spending inst i := by
          apply Finset.sum_le_sum; intro i hi
          apply Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => hW_sub hc)
          intro c _ _; exact hvalid.1 i hi c
      _ ≤ ∑ i ∈ inst.voters, b := by
          apply Finset.sum_le_sum; intro i hi; exact hvalid.2.2.1 i hi
      _ = inst.voters.card * b := by simp [Finset.sum_const]
  -- Therefore 1/b ≤ n/k
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr inst.k_pos
  have hn_pos : (0 : ℝ) < inst.voters.card := Nat.cast_pos.mpr (Finset.card_pos.mpr inst.voters_nonempty)
  have h_inv_b_le : 1 / b ≤ inst.voters.card / k := by
    have hb_ne : b ≠ 0 := ne_of_gt hb_pos
    have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    field_simp [hb_ne, hk_ne]
    have hk_le_nb' : (k : ℝ) ≤ b * inst.voters.card := by
      simpa [mul_comm] using hk_le_nb
    exact hk_le_nb'
  -- Choose ε > 0 small enough
  -- If n/k > 1/b, use ε = (n/k - 1/b) / (2n)
  -- If n/k = 1/b, use ε = 1/(2k) (and everyone's unspent is 0)
  set δ : ℝ := inst.voters.card / k - 1 / b with hδ_def
  have hδ_nonneg : 0 ≤ δ := by linarith
  set ε : ℝ := if δ > 0 then δ / (2 * inst.voters.card) else 1 / (2 * k) with hε_def
  have hε_pos : 0 < ε := by
    rw [hε_def]
    split_ifs with hδ_pos
    · exact div_pos hδ_pos (by linarith)
    · exact div_pos (by linarith : (0 : ℝ) < 1) (by linarith)
  -- Construct the new price system q
  set q : PriceSystem V C := fun i c =>
    if c ∈ W then p i c / b
    else if c ∈ inst.approves i ∩ inst.candidates then
      p.unspent inst b i / b + ε
    else 0 with hq_def
  use q
  constructor
  -- (1) q is non-negative
  · intro i hi c
    by_cases hcW : c ∈ W
    · have h_pc_nonneg : 0 ≤ p i c := hvalid.1 i hi c
      have h_div_nonneg : 0 ≤ p i c / b := div_nonneg h_pc_nonneg (le_of_lt hb_pos)
      simpa [hq_def, hcW] using h_div_nonneg
    · by_cases hcA : c ∈ inst.approves i ∩ inst.candidates
      · have h_unspent_nonneg : 0 ≤ p.unspent inst b i := by
          simp [PriceSystem.unspent]
          linarith [hvalid.2.2.1 i hi]
        have h_div_nonneg : 0 ≤ p.unspent inst b i / b :=
          div_nonneg h_unspent_nonneg (le_of_lt hb_pos)
        have h_add_nonneg : 0 ≤ p.unspent inst b i / b + ε :=
          add_nonneg h_div_nonneg (le_of_lt hε_pos)
        have hcA' : c ∈ inst.approves i ∧ c ∈ inst.candidates := by
          simpa [mem_inter] using hcA
        simpa [hq_def, hcW, hcA, hcA'] using h_add_nonneg
      · have hcA' : ¬ (c ∈ inst.approves i ∧ c ∈ inst.candidates) := by
          intro h
          exact hcA (by simpa [mem_inter] using h)
        simp [hq_def, hcW, hcA']
  constructor
  -- (2) Total payment bounded by n/k
  · intro c hc
    simp only [PriceSystem.total_payment]
    by_cases hcW : c ∈ W
    · -- c ∈ W: sum = (1/b) · Σ p i c = 1/b ≤ n/k
      have h_simp : ∀ i, q i c = p i c / b := fun i => by simp only [hq_def, hcW, ↓reduceIte]
      simp only [h_simp]
      calc ∑ i ∈ inst.voters, p i c / b
          = (∑ i ∈ inst.voters, p i c) / b := by
            have h := (Finset.sum_div (s := inst.voters) (f := fun i => p i c) b)
            simpa using h.symm
        _ = p.total_payment inst c / b := rfl
        _ = 1 / b := by rw [hvalid.2.2.2.1 c hcW]
        _ ≤ inst.voters.card / k := h_inv_b_le
    · -- c ∉ W: more complex
      have h_simp : ∀ i, q i c = if c ∈ inst.approves i then p.unspent inst b i / b + ε else 0 := by
        intro i
        simp only [hq_def, hcW, ↓reduceIte, mem_inter, hc, and_true]
      simp only [h_simp]
      rw [← Finset.sum_filter]
      -- The filter is exactly supporters
      have h_filter_eq : inst.voters.filter (c ∈ inst.approves ·) = inst.supporters c := rfl
      rw [h_filter_eq]
      -- Split into unspent part and ε part
      have h_sum_split : ∑ i ∈ inst.supporters c, (p.unspent inst b i / b + ε) =
          (∑ i ∈ inst.supporters c, p.unspent inst b i) / b + (inst.supporters c).card * ε := by
        calc
          ∑ i ∈ inst.supporters c, (p.unspent inst b i / b + ε)
              = ∑ i ∈ inst.supporters c, p.unspent inst b i / b +
                  ∑ i ∈ inst.supporters c, ε := Finset.sum_add_distrib
          _ = (∑ i ∈ inst.supporters c, p.unspent inst b i) / b +
                  (inst.supporters c).card * ε := by
                simp [Finset.sum_div, Finset.sum_const]
      rw [h_sum_split]
      -- By exhaustiveness: Σ unspent ≤ 1
      have h_exhaust : ∑ i ∈ inst.supporters c, p.unspent inst b i ≤ 1 :=
        hexhaust c (mem_sdiff.mpr ⟨hc, hcW⟩)
      -- Number of supporters ≤ n
      have h_supp_le : (inst.supporters c).card ≤ inst.voters.card :=
        Finset.card_le_card (fun i hi => (mem_filter.mp hi).1)
      -- Now bound the total
      by_cases hδ_pos : δ > 0
      · -- δ > 0 case: reuse coarse bound and simplify
        have hε_val : ε = δ / (2 * inst.voters.card) := by simp [hε_def, hδ_pos]
        have h_bound : (∑ i ∈ inst.supporters c, p.unspent inst b i) / b +
            (inst.supporters c).card * ε ≤ 1 / b + inst.voters.card * ε := by
          apply add_le_add
          · exact div_le_div_of_nonneg_right h_exhaust (le_of_lt hb_pos)
          · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h_supp_le) (le_of_lt hε_pos)
        have h_simpl : inst.voters.card * (δ / (2 * inst.voters.card)) = δ / 2 := by
          have hn_ne : (inst.voters.card : ℝ) ≠ 0 := ne_of_gt hn_pos
          field_simp [hn_ne]
        calc (∑ i ∈ inst.supporters c, p.unspent inst b i) / b + (inst.supporters c).card * ε
            ≤ 1 / b + inst.voters.card * ε := h_bound
          _ = 1 / b + δ / 2 := by simpa [hε_val, h_simpl]
          _ ≤ inst.voters.card / k := by
            have hδ_nonneg' : 0 ≤ δ := hδ_nonneg
            have h_half_le : δ / 2 ≤ δ := by nlinarith
            calc 1 / b + δ / 2 ≤ 1 / b + δ := add_le_add_left h_half_le _
            _ = inst.voters.card / k := by rw [hδ_def]; ring
      · -- δ = 0 case: all voters spend exactly b, so unspent is 0
        have hδ_eq : δ = 0 := le_antisymm (le_of_not_gt hδ_pos) hδ_nonneg
        have hε_val : ε = 1 / (2 * k) := by simp [hε_def, hδ_eq]
        -- Each voter must spend b (otherwise total spending < n·b contradicting k = n·b)
        have h_all_spend_b : ∀ i ∈ inst.voters, p.spending inst i = b := by
          intro i hi
          have hle : p.spending inst i ≤ b := hvalid.2.2.1 i hi
          have hge : p.spending inst i ≥ b := by
            by_contra hlt; push_neg at hlt
            have h_strict : ∑ j ∈ inst.voters, p.spending inst j < inst.voters.card * b := by
              calc ∑ j ∈ inst.voters, p.spending inst j
                  = p.spending inst i + ∑ j ∈ inst.voters.erase i, p.spending inst j := by
                      rw [Finset.add_sum_erase _ _ hi]
                _ < b + ∑ j ∈ inst.voters.erase i, b := by
                      apply add_lt_add_of_lt_of_le hlt
                      apply Finset.sum_le_sum
                      intro j hj; exact hvalid.2.2.1 j (Finset.mem_of_mem_erase hj)
                _ = b + ((inst.voters.card : ℝ) - 1) * b := by
                      simp [Finset.sum_const, Finset.card_erase_of_mem hi, nsmul_eq_mul]
                      have hcard : 1 ≤ inst.voters.card := Finset.card_pos.mpr inst.voters_nonempty
                      simp [Nat.cast_sub hcard]
                _ = inst.voters.card * b := by ring
            have h_payment_le : (k : ℝ) ≤ ∑ j ∈ inst.voters, p.spending inst j := by
              calc (k : ℝ) = ∑ c' ∈ W, p.total_payment inst c' := by
                      rw [p.total_elected_payment inst W b hvalid, hW_card]
                _ = ∑ c' ∈ W, ∑ j ∈ inst.voters, p j c' := rfl
                _ = ∑ j ∈ inst.voters, ∑ c' ∈ W, p j c' := Finset.sum_comm
                _ ≤ ∑ j ∈ inst.voters, p.spending inst j := by
                    apply Finset.sum_le_sum; intro j hj
                    apply Finset.sum_le_sum_of_subset_of_nonneg (fun c' hc' => hW_sub hc')
                    intro c' _ _; exact hvalid.1 j hj c'
            have hk_lt : (k : ℝ) < inst.voters.card * b := by linarith
            have hδ_alt : δ = (inst.voters.card * b - k) / (k * b) := by
              have hb_ne : b ≠ 0 := hb_pos.ne'
              have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
              calc
                δ = (inst.voters.card : ℝ) / k - 1 / b := hδ_def
                _ = ((inst.voters.card : ℝ) * b - k) / (k * b) := by
                  field_simp [hb_ne, hk_ne]
            have hnum_pos : inst.voters.card * b - k > 0 := by linarith
            have hden_pos : 0 < k * b := mul_pos hk_pos hb_pos
            have hδ_pos' : δ > 0 := by
              have : (inst.voters.card * b - k) / (k * b) > 0 := div_pos hnum_pos hden_pos
              simpa [hδ_alt, mul_comm] using this
            linarith
          linarith
        have h_unspent_zero : ∀ i ∈ inst.voters, p.unspent inst b i = 0 := by
          intro i hi
          simp [PriceSystem.unspent, h_all_spend_b i hi]
        have h_sum_zero : ∑ i ∈ inst.supporters c, p.unspent inst b i = 0 :=
          Finset.sum_eq_zero (fun i hi => h_unspent_zero i ((mem_filter.mp hi).1))
        have h_lhs : (∑ i ∈ inst.supporters c, p.unspent inst b i) / b +
            (inst.supporters c).card * ε = (inst.supporters c).card * ε := by
          simp [h_sum_zero]
        have h_bound : (inst.supporters c).card * ε ≤ inst.voters.card / k := by
          calc (inst.supporters c).card * ε
              = (inst.supporters c).card * (1 / (2 * k)) := by simp [hε_val]
          _ ≤ inst.voters.card * (1 / (2 * k)) := by
              apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h_supp_le)
              linarith
          _ = inst.voters.card / (2 * k) := by ring
          _ ≤ inst.voters.card / k := by
              have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
              have h_rewrite : inst.voters.card / (2 * k) = (inst.voters.card : ℝ) / k / 2 := by
                field_simp [hk_ne]
              have h_nonneg : 0 ≤ (inst.voters.card : ℝ) / k := by
                have hnum_nonneg : 0 ≤ (inst.voters.card : ℝ) := Nat.cast_nonneg _
                exact div_nonneg hnum_nonneg (le_of_lt hk_pos)
              calc inst.voters.card / (2 * k)
                  = (inst.voters.card : ℝ) / k / 2 := h_rewrite
                _ ≤ (inst.voters.card : ℝ) / k := by nlinarith
        have h_goal : (∑ i ∈ inst.supporters c, p.unspent inst b i) / b +
            (inst.supporters c).card * ε ≤ inst.voters.card / k := by
          linarith [h_lhs, h_bound]
        exact h_goal
  -- (3) Weak exhaustiveness
  · intro i hi d hd
    simp only [mem_sdiff, mem_inter] at hd
    obtain ⟨⟨hd_app, hd_cand⟩, hd_notW⟩ := hd
    -- q i d = unspent/b + ε
    have hq_d : q i d = p.unspent inst b i / b + ε := by
      simp only [hq_def, hd_notW, ↓reduceIte, mem_inter, hd_app, hd_cand, and_self]
    rw [hq_d]
    -- Σ_{c ∈ A_i ∩ W} q i c = Σ p i c / b
    have h_sum_W : ∑ c ∈ inst.approves i ∩ W, q i c = (∑ c ∈ inst.approves i ∩ W, p i c) / b := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c hc
      simp only [hq_def, (mem_inter.mp hc).2, ↓reduceIte]
    rw [h_sum_W]
    -- spending on W = total spending for valid p (non-elected get 0 payment)
    have h_spending_eq : ∑ c ∈ inst.approves i ∩ W, p i c = p.spending inst i := by
      have h_valid_spending := p.spending_eq_elected_approved inst W b hvalid hW_sub i hi
      rw [h_valid_spending]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext c; simp only [mem_inter, and_comm]
    rw [h_spending_eq]
    -- unspent + spending = b
    have h_sum_eq : p.unspent inst b i + p.spending inst i = b := by
      simp only [PriceSystem.unspent]; ring
    calc p.unspent inst b i / b + ε + p.spending inst i / b
        = (p.unspent inst b i + p.spending inst i) / b + ε := by ring
      _ = b / b + ε := by rw [h_sum_eq]
      _ = 1 + ε := by rw [div_self (ne_of_gt hb_pos)]
      _ > 1 := by linarith

-- ============================================================================
-- WEAK PRICEABILITY IMPLIES SUB-CORE
-- ============================================================================

/--
Weak priceability implies sub-core: If a committee is weakly priceable, it lies in the sub-core.

**Proof sketch** (following Munagala-Shen-Wang):
Suppose W is weakly priceable but not in the sub-core. Then there exist S, T with
|T| ≤ |S|·k/n such that ∀ i ∈ S, A_i ∩ W ⊊ A_i ∩ T.

For each i ∈ S, pick d_i ∈ (A_i ∩ T) \ (A_i ∩ W). By weak exhaustiveness:
  p_i(d_i) + Σ_{c ∈ A_i ∩ W} p_i(c) > 1

Since {d_i} ∪ (A_i ∩ W) ⊆ T, we have Σ_{c ∈ T} p_i(c) > 1 for all i ∈ S.

Summing over S and using the total payment bound:
  |T| · (n/k) ≥ Σ_{c ∈ T} Σ_i p_i(c) ≥ Σ_{i ∈ S} Σ_{c ∈ T} p_i(c) > |S|

This contradicts |T| ≤ |S|·k/n.

Reference: "Auditing for Core Stability in Participatory Budgeting"
by Munagala, Shen, Wang (WINE 2022), Proposition 7.3
-/
theorem weakly_priceable_implies_sub_core (inst : ABCInstance V C k) (W : Finset C) :
    inst.is_weakly_priceable W → inst.is_in_sub_core W := by
  intro ⟨p, h_nonneg, h_bounded, h_exhaust⟩
         S T h_S_sub h_T_sub h_S_nonempty h_size
  -- Prove by contradiction: assume all voters in S strictly prefer T to W
  by_contra h_all_prefer
  push_neg at h_all_prefer
  -- h_all_prefer : ∀ i ∈ S, W ∩ inst.approves i ⊂ T ∩ inst.approves i

  -- For each i ∈ S, the payment sum over T is > 1
  have h_each_gt_one : ∀ i ∈ S, ∑ c ∈ T, p i c > 1 := by
    intro i hi
    have h_prefer := h_all_prefer i hi
    -- W ∩ A_i ⊊ T ∩ A_i means there exists d ∈ (T ∩ A_i) \ (W ∩ A_i)
    obtain ⟨d, hd_in, hd_not⟩ := Finset.exists_of_ssubset h_prefer
    simp only [mem_inter] at hd_in
    have hd_T : d ∈ T := hd_in.1
    have hd_app : d ∈ inst.approves i := hd_in.2
    have hd_not_W : d ∉ W := fun hd_W => hd_not (mem_inter.mpr ⟨hd_W, hd_app⟩)
    -- d ∈ (A_i ∩ candidates) \ W, so weak exhaustiveness applies
    have hd_sdiff : d ∈ (inst.approves i ∩ inst.candidates) \ W :=
      mem_sdiff.mpr ⟨mem_inter.mpr ⟨hd_app, h_T_sub hd_T⟩, hd_not_W⟩
    have h_exhaust_i := h_exhaust i (h_S_sub hi) d hd_sdiff
    -- {d} ∪ (A_i ∩ W) ⊆ T
    have h_subset : {d} ∪ (inst.approves i ∩ W) ⊆ T := by
      intro c hc
      simp only [mem_union, mem_singleton, mem_inter] at hc
      rcases hc with rfl | ⟨hc_app, hc_W⟩
      · exact hd_T
      · -- W ∩ A_i ⊆ T ∩ A_i (from ssubset)
        have h_sub := (Finset.ssubset_iff_subset_ne.mp h_prefer).1
        exact (mem_inter.mp (h_sub (mem_inter.mpr ⟨hc_W, hc_app⟩))).1
    have h_disjoint : Disjoint ({d} : Finset C) (inst.approves i ∩ W) :=
      disjoint_singleton_left.mpr (fun h => hd_not_W (mem_inter.mp h).2)
    calc ∑ c ∈ T, p i c
        ≥ ∑ c ∈ {d} ∪ (inst.approves i ∩ W), p i c :=
          Finset.sum_le_sum_of_subset_of_nonneg h_subset
            (fun c _ _ => h_nonneg i (h_S_sub hi) c)
      _ = p i d + ∑ c ∈ inst.approves i ∩ W, p i c := by
          rw [sum_union h_disjoint, sum_singleton]
      _ > 1 := h_exhaust_i

  -- Sum over S is > |S|
  have h_sum_S_gt : ∑ i ∈ S, ∑ c ∈ T, p i c > S.card := by
    calc ∑ i ∈ S, ∑ c ∈ T, p i c
        > ∑ _ ∈ S, (1 : ℝ) := by
          apply Finset.sum_lt_sum
          · intro i hi; exact le_of_lt (h_each_gt_one i hi)
          · obtain ⟨i, hi⟩ := h_S_nonempty
            exact ⟨i, hi, h_each_gt_one i hi⟩
      _ = S.card := by simp

  -- Total payment bound: Σ_{c∈T} total_payment(c) ≤ |T| · n/k
  have h_total_bound : ∑ c ∈ T, p.total_payment inst c ≤ T.card * (inst.voters.card / k) := by
    calc ∑ c ∈ T, p.total_payment inst c
        ≤ ∑ c ∈ T, (inst.voters.card / k : ℝ) :=
          Finset.sum_le_sum (fun c hc => h_bounded c (h_T_sub hc))
      _ = T.card * (inst.voters.card / k) := by simp [Finset.sum_const]

  have h_sum_comm : ∑ c ∈ T, p.total_payment inst c = ∑ i ∈ inst.voters, ∑ c ∈ T, p i c := by
    simp only [PriceSystem.total_payment]; exact Finset.sum_comm

  have h_sum_S_le : ∑ i ∈ S, ∑ c ∈ T, p i c ≤ ∑ i ∈ inst.voters, ∑ c ∈ T, p i c :=
    Finset.sum_le_sum_of_subset_of_nonneg h_S_sub
      (fun i hi _ => Finset.sum_nonneg (fun c _ => h_nonneg i hi c))

  -- Chain: |T| · n/k ≥ Σ total_payment = Σ_voters Σ_T ≥ Σ_S Σ_T > |S|
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr inst.k_pos
  have h_chain : (T.card : ℝ) * (inst.voters.card / k : ℝ) > (S.card : ℝ) := by
    calc (T.card : ℝ) * (inst.voters.card / k : ℝ)
        ≥ ∑ c ∈ T, p.total_payment inst c := h_total_bound
      _ = ∑ i ∈ inst.voters, ∑ c ∈ T, p i c := h_sum_comm
      _ ≥ ∑ i ∈ S, ∑ c ∈ T, p i c := h_sum_S_le
      _ > S.card := h_sum_S_gt

  -- This gives T.card * voters.card > S.card * k
  -- But h_size says T.card * voters.card ≤ S.card * k - Contradiction!
  have h_size' : (T.card : ℝ) * inst.voters.card ≤ (S.card : ℝ) * k := by
    exact_mod_cast h_size
  have h_contra : (T.card : ℝ) * inst.voters.card > (S.card : ℝ) * k := by
    have h_mul := mul_lt_mul_of_pos_right h_chain hk_pos
    -- (T.card)*(voters/k)*k simplifies to (T.card)*voters
    have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    have h_simpl : (T.card : ℝ) * (inst.voters.card / k : ℝ) * k = (T.card : ℝ) * inst.voters.card := by
      field_simp [hk_ne]
    simpa [h_simpl] using h_mul

  linarith [h_contra, h_size']

end ABCInstance
