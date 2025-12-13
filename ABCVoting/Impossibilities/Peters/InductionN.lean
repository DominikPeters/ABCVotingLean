import Mathlib.Logic.Equiv.Fin.Basic

import ABCVoting.ABCRule
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Strategyproofness
import ABCVoting.Impossibilities.Peters.StrategyproofnessPlentiful

open Finset BigOperators ABCInstance

/-!
# Induction on the Number of Voters (Peters, Lemma 5)

We work in the Peters setting with `m = k+1` candidates, i.e. the candidate type is `Fin (k+1)`.

Given a rule for `q*k` voters, we induce a rule for `k` voters by repeating each voter `q` times.

The nontrivial part is strategyproofness: a manipulation by voter `i` in the `k`-voter instance
corresponds to `q` consecutive manipulations by each copy of `i` in the `q*k`-voter instance.
-/

/-
Original proof as written in the paper:
\begin{lemma}
	\label{lem:induction-n}
	Suppose $k\ge 2$ and $m = k+1$, and let $q \ge 1$ be an integer. If there exists a proportional and strategyproof committee rule for $q\cdot k$ voters, then there also exists such a rule for $k$ voters.
\end{lemma}
\begin{proof}
	For convenience, we write profiles as lists. Given a profile $P$, we write $qP$ for the profile obtained by concatenating $q$ copies of $P$. Let $f_{qk}$ be the rule for $q\cdot k$ voters. We define the rule $f_k$ for $k$ voters as follows:
	\[ f_k(P) = f_{qk}(qP) \quad \text{for all profiles $P \in \mathcal B^k$.}  \]

	\emph{Proportionality.} Suppose $P \in \mathcal B^k$ is a party-list profile in which at least $\frac nk = \frac kk = 1$ voters approve $\{c\}$. Then $qP$ is a party-list profile in which at least $q \cdot \frac nk = \frac{qn}k = q$ voters approve $\{c\}$. Since $f_{qk}$ is proportional, $c\in f_{qk}(qP) = f_k(P)$.

	\emph{Strategyproofness.} Suppose for a contradiction that $f_k$ is not strategyproof, so that there is $P$ and an $i$-variant $P'$ with $f_k(P') \cap P(i) \supsetneq f_k(P) \cap P(i)$. Because $m = k+1$, the committees $f_k(P')$ and $f_k(P)$ must differ in exactly 1 candidate. Since the manipulation was successful, $f_k(P')$ must be obtained by replacing a non-approved candidate in $f_k(P)$ by an approved one, say $f_k(P') = f_k(P) \cup \{c\} \setminus \{d\}$ with $c \in P(i) \not\ni d$. Now consider $f_{qk}(qP)$, and step-by-step let each of the $q$ copies of $P(i)$ in $qP$ manipulate from $P(i)$ to $P'(i)$ obtaining $qP'$ in the last step. Because $f_{qk}$ is strategyproof, at each step of this process $f_{qk}$ cannot have exchanged a non-approved candidate by an approved candidate according to $P(i)$. This contradicts that $f_k(P') = f_k(P) \cup \{c\} \setminus \{d\}$.
\end{proof}
-/

namespace Peters.InductionN

abbrev Cand (k : ℕ) := Fin (k + 1)

-- ============================================================================
-- Expanding an instance from k voters to q*k voters
-- ============================================================================

noncomputable def expand_voters (k q : ℕ) (hq : 0 < q)
    (inst : ABCInstance (Fin k) (Cand k) k) :
    ABCInstance (Fin (q * k)) (Cand k) k where
  voters :=
    ((Finset.univ : Finset (Fin q)).product inst.voters).image finProdFinEquiv
  candidates := inst.candidates
  approves := fun v => inst.approves (finProdFinEquiv.symm v).2
  approves_subset := by
    classical
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
    have hpv : p.2 ∈ inst.voters := (Finset.mem_product.mp hp).2
    simpa using inst.approves_subset p.2 hpv
  voters_nonempty := by
    classical
    rcases inst.voters_nonempty with ⟨v0, hv0⟩
    let t0 : Fin q := ⟨0, hq⟩
    refine ⟨finProdFinEquiv (t0, v0), ?_⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨(t0, v0), ?_, rfl⟩
    simp [Finset.mem_product, hv0]
  k_pos := inst.k_pos
  k_le_m := inst.k_le_m

lemma mem_expand_voters_iff (k q : ℕ) (hq : 0 < q)
    (inst : ABCInstance (Fin k) (Cand k) k) (v : Fin (q * k)) :
    v ∈ (expand_voters k q hq inst).voters ↔ (finProdFinEquiv.symm v).2 ∈ inst.voters := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
    simpa using (Finset.mem_product.mp hp).2
  · intro hv
    refine Finset.mem_image.mpr ?_
    refine ⟨finProdFinEquiv.symm v, ?_, by
      simpa using (finProdFinEquiv.apply_symm_apply v)⟩
    have : (finProdFinEquiv.symm v).1 ∈ (Finset.univ : Finset (Fin q)) := by simp
    simpa [Finset.mem_product, this, hv]

lemma expand_voters_voters_card (k q : ℕ) (hq : 0 < q)
    (inst : ABCInstance (Fin k) (Cand k) k) :
    (expand_voters k q hq inst).voters.card = q * inst.voters.card := by
  classical
  have hinj : Function.Injective (fun x : Fin q × Fin k => finProdFinEquiv x) :=
    finProdFinEquiv.injective
  calc
    (expand_voters k q hq inst).voters.card
        = (((Finset.univ : Finset (Fin q)).product inst.voters).image finProdFinEquiv).card := rfl
    _ = ((Finset.univ : Finset (Fin q)).product inst.voters).card :=
      Finset.card_image_of_injective _ hinj
    _ = q * inst.voters.card := by simp [Finset.card_product]

lemma expand_voters_is_party_list (k q : ℕ) (hq : 0 < q)
    (inst : ABCInstance (Fin k) (Cand k) k) :
    inst.is_party_list → (expand_voters k q hq inst).is_party_list := by
  classical
  intro hpl v₁ hv₁ v₂ hv₂
  have hv₁' :
      (finProdFinEquiv.symm v₁).2 ∈ inst.voters :=
    (mem_expand_voters_iff (k := k) (q := q) hq inst v₁).1 hv₁
  have hv₂' :
      (finProdFinEquiv.symm v₂).2 ∈ inst.voters :=
    (mem_expand_voters_iff (k := k) (q := q) hq inst v₂).1 hv₂
  by_cases h : (finProdFinEquiv.symm v₁).2 = (finProdFinEquiv.symm v₂).2
  · left
    have hmod : v₁.modNat = v₂.modNat := by
      simpa [finProdFinEquiv_symm_apply] using h
    simpa [expand_voters, finProdFinEquiv_symm_apply, hmod]
  ·
    have := hpl (finProdFinEquiv.symm v₁).2 hv₁' (finProdFinEquiv.symm v₂).2 hv₂'
    simpa [expand_voters] using this

lemma expand_voters_singleton_party (k q : ℕ) (hq : 0 < q)
    (inst : ABCInstance (Fin k) (Cand k) k) (c : Cand k) :
    (expand_voters k q hq inst).singleton_party c =
      ((Finset.univ : Finset (Fin q)).product (inst.singleton_party c)).image finProdFinEquiv := by
  classical
  ext v
  constructor
  · intro hv
    have hvv : v ∈ (expand_voters k q hq inst).voters := (Finset.mem_filter.mp hv).1
    have hballot : (expand_voters k q hq inst).approves v = {c} := (Finset.mem_filter.mp hv).2
    refine Finset.mem_image.mpr ?_
    refine ⟨finProdFinEquiv.symm v, ?_, by
      simpa using (finProdFinEquiv.apply_symm_apply v)⟩
    have hp2 : (finProdFinEquiv.symm v).2 ∈ inst.singleton_party c := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨(mem_expand_voters_iff (k := k) (q := q) hq inst v).1 hvv, ?_⟩
      simpa [expand_voters] using hballot
    have hp1 : (finProdFinEquiv.symm v).1 ∈ (Finset.univ : Finset (Fin q)) := by simp
    exact Finset.mem_product.mpr ⟨hp1, hp2⟩
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨_, hpv⟩
    have hpv_mem : p.2 ∈ inst.voters := (Finset.mem_filter.mp hpv).1
    have hpv_eq : inst.approves p.2 = {c} := (Finset.mem_filter.mp hpv).2
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, ?_⟩
    · -- voter membership
      refine Finset.mem_image.mpr ?_
      refine ⟨p, ?_, rfl⟩
      have : p.1 ∈ (Finset.univ : Finset (Fin q)) := by simp
      simpa [Finset.mem_product, this] using hpv_mem
    · -- ballot equality
      have hmod : (finProdFinEquiv p).modNat = p.2 := by
        have hA :
            finProdFinEquiv.symm (finProdFinEquiv p) =
              ((finProdFinEquiv p).divNat, (finProdFinEquiv p).modNat) := by
          simpa using (finProdFinEquiv_symm_apply (x := finProdFinEquiv p))
        have hB : finProdFinEquiv.symm (finProdFinEquiv p) = p := by
          simpa using (finProdFinEquiv.symm_apply_apply p)
        have hC : p = ((finProdFinEquiv p).divNat, (finProdFinEquiv p).modNat) := by
          simpa [hB] using hA
        have : p.2 = (finProdFinEquiv p).modNat := by
          simpa using congrArg Prod.snd hC
        simpa using this.symm
      simpa [expand_voters, finProdFinEquiv_symm_apply, hmod, hpv_eq]

lemma expand_voters_singleton_party_size (k q : ℕ) (hq : 0 < q)
    (inst : ABCInstance (Fin k) (Cand k) k) (c : Cand k) :
    (expand_voters k q hq inst).singleton_party_size c = q * inst.singleton_party_size c := by
  classical
  -- use the `singleton_party` rewriting lemma, then compute card of the product
  simp [singleton_party_size_eq_card, expand_voters_singleton_party (k := k) (q := q) hq inst c,
    Finset.card_image_of_injective, finProdFinEquiv.injective, Finset.card_product]

lemma approvedCandidates_expand_voters (k q : ℕ) (hq : 0 < q)
    (inst : ABCInstance (Fin k) (Cand k) k) :
    (expand_voters k q hq inst).approvedCandidates = inst.approvedCandidates := by
  classical
  ext c
  constructor
  · intro hc
    rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hcA⟩
    have hv' : (finProdFinEquiv.symm v).2 ∈ inst.voters :=
      (mem_expand_voters_iff (k := k) (q := q) hq inst v).1 hv
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨(finProdFinEquiv.symm v).2, hv', ?_⟩
    simpa [expand_voters] using hcA
  · intro hc
    rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hcA⟩
    let t0 : Fin q := ⟨0, hq⟩
    let v' : Fin (q * k) := finProdFinEquiv (t0, v)
    have hv' : v' ∈ (expand_voters k q hq inst).voters := by
      refine Finset.mem_image.mpr ?_
      refine ⟨(t0, v), ?_, rfl⟩
      simp [Finset.mem_product, hv]
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨v', hv', ?_⟩
    have hvmod : v'.modNat = v := by
      have hA : finProdFinEquiv.symm v' = (v'.divNat, v'.modNat) := by
        simpa using (finProdFinEquiv_symm_apply (x := v'))
      have hB : finProdFinEquiv.symm v' = (t0, v) := by
        simpa [v'] using (finProdFinEquiv.symm_apply_apply (t0, v))
      have hC : (v'.divNat, v'.modNat) = (t0, v) := (Eq.trans (Eq.symm hA) hB)
      simpa using congrArg Prod.snd hC
    simpa [expand_voters, hvmod] using hcA

lemma plentiful_expand_voters_iff (k q : ℕ) (hq : 0 < q)
    (inst : ABCInstance (Fin k) (Cand k) k) :
    (expand_voters k q hq inst).plentiful ↔ inst.plentiful := by
  classical
  unfold plentiful
  simpa [approvedCandidates_expand_voters (k := k) (q := q) hq inst]

lemma is_unapproved_expand_voters_iff (k q : ℕ) (hq : 0 < q)
    (inst : ABCInstance (Fin k) (Cand k) k) (c : Cand k) :
    (expand_voters k q hq inst).is_unapproved c ↔ inst.is_unapproved c := by
  classical
  unfold is_unapproved
  constructor
  · intro hun v hv
    let t0 : Fin q := ⟨0, hq⟩
    let v' : Fin (q * k) := finProdFinEquiv (t0, v)
    have hv' : v' ∈ (expand_voters k q hq inst).voters := by
      refine Finset.mem_image.mpr ?_
      refine ⟨(t0, v), ?_, rfl⟩
      simp [Finset.mem_product, hv]
    have : c ∉ (expand_voters k q hq inst).approves v' := hun v' hv'
    have hvmod : v'.modNat = v := by
      have hA : finProdFinEquiv.symm v' = (v'.divNat, v'.modNat) := by
        simpa using (finProdFinEquiv_symm_apply (x := v'))
      have hB : finProdFinEquiv.symm v' = (t0, v) := by
        simpa [v'] using (finProdFinEquiv.symm_apply_apply (t0, v))
      have hC : (v'.divNat, v'.modNat) = (t0, v) := (Eq.trans (Eq.symm hA) hB)
      simpa using congrArg Prod.snd hC
    simpa [expand_voters, hvmod] using this
  · intro hun v hv
    have hv' : (finProdFinEquiv.symm v).2 ∈ inst.voters :=
      (mem_expand_voters_iff (k := k) (q := q) hq inst v).1 hv
    have : c ∉ inst.approves (finProdFinEquiv.symm v).2 := hun _ hv'
    simpa [expand_voters] using this

-- ============================================================================
-- Induced rule
-- ============================================================================

noncomputable def induced_rule (k q : ℕ) (hq : 0 < q)
    (f : ABCRule (Fin (q * k)) (Cand k) k) :
    ABCRule (Fin k) (Cand k) k where
  apply inst := f (expand_voters k q hq inst)
  extensional := by
    classical
    intro inst inst' hv hc ha
    apply f.extensional (expand_voters k q hq inst) (expand_voters k q hq inst')
    · simp [expand_voters, hv]
    · simpa [expand_voters, hc]
    · intro v hvv
      have hv_orig :
          (finProdFinEquiv.symm v).2 ∈ inst.voters :=
        (mem_expand_voters_iff (k := k) (q := q) hq inst v).1 hvv
      have : inst.approves (finProdFinEquiv.symm v).2 = inst'.approves (finProdFinEquiv.symm v).2 :=
        ha _ hv_orig
      simpa [expand_voters, this]

lemma induced_rule_wellFormed (k q : ℕ) (hq : 0 < q)
    (f : ABCRule (Fin (q * k)) (Cand k) k) (hwf : f.IsWellFormed) :
    (induced_rule k q hq f).IsWellFormed := by
  classical
  intro inst
  simpa [induced_rule] using hwf (expand_voters k q hq inst)

lemma induced_rule_resolute (k q : ℕ) (hq : 0 < q)
    (f : ABCRule (Fin (q * k)) (Cand k) k) (hres : f.IsResolute) :
    (induced_rule k q hq f).IsResolute := by
  intro inst
  simpa [induced_rule] using hres (expand_voters k q hq inst)

lemma induced_rule_weak_efficiency (k q : ℕ) (hq : 0 < q)
    (f : ABCRule (Fin (q * k)) (Cand k) k)
    (heff : f.SatisfiesWeakEfficiency) :
    (induced_rule k q hq f).SatisfiesWeakEfficiency := by
  classical
  intro inst hpl W hW c hc
  have hpl' : (expand_voters k q hq inst).plentiful :=
    (plentiful_expand_voters_iff (k := k) (q := q) hq inst).2 hpl
  have hun' : ¬(expand_voters k q hq inst).is_unapproved c :=
    (heff (expand_voters k q hq inst) hpl' W (by simpa [induced_rule] using hW) c hc)
  intro hun
  exact hun' ((is_unapproved_expand_voters_iff (k := k) (q := q) hq inst c).2 hun)

lemma induced_rule_proportionality (k q : ℕ) (hq : 0 < q)
    (f : ABCRule (Fin (q * k)) (Cand k) k)
    (hprop : f.SatisfiesProportionality) :
    (induced_rule k q hq f).SatisfiesProportionality := by
  classical
  intro inst c hpl hcand hquota W hW
  have hpl' : (expand_voters k q hq inst).is_party_list :=
    expand_voters_is_party_list (k := k) (q := q) hq inst hpl
  have hcand' : c ∈ (expand_voters k q hq inst).candidates := by simpa [expand_voters] using hcand
  have hquota' :
      (expand_voters k q hq inst).singleton_party_size c * k ≥ (expand_voters k q hq inst).voters.card := by
    -- both sides scale by q
    simpa [expand_voters_singleton_party_size (k := k) (q := q) hq inst c,
      expand_voters_voters_card (k := k) (q := q) hq inst, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using Nat.mul_le_mul_left q hquota
  exact hprop (expand_voters k q hq inst) c hpl' hcand' hquota' W (by simpa [induced_rule] using hW)

-- ============================================================================
-- Strategyproofness on plentiful instances (Peters Lemma 5)
-- ============================================================================

noncomputable def chain_instance (k q : ℕ) (hq : 0 < q)
    (inst inst' : ABCInstance (Fin k) (Cand k) k) (i : Fin k)
    (hvar : inst.is_i_variant inst' i) (t : ℕ) :
    ABCInstance (Fin (q * k)) (Cand k) k where
  voters := (expand_voters k q hq inst).voters
  candidates := inst.candidates
  approves := fun v =>
    let p := finProdFinEquiv.symm v
    if p.2 = i ∧ p.1.1 < t then inst'.approves i else inst.approves p.2
  approves_subset := by
    classical
    intro v hv
    set p : Fin q × Fin k := finProdFinEquiv.symm v with hp
    have hv_orig : p.2 ∈ inst.voters := by
      simpa [hp] using (mem_expand_voters_iff (k := k) (q := q) hq inst v).1 hv
    by_cases h : p.2 = i ∧ p.1.1 < t
    · have hi_inst : i ∈ inst.voters := by simpa [h.1] using hv_orig
      have hi' : i ∈ inst'.voters := by simpa [hvar.1] using hi_inst
      have hs : inst'.approves i ⊆ inst'.candidates := inst'.approves_subset i hi'
      have hcand' : inst'.candidates = inst.candidates := by simpa using hvar.2.1.symm
      simpa [h, hcand'] using hs
    ·
      have hs : inst.approves p.2 ⊆ inst.candidates := inst.approves_subset _ hv_orig
      simpa [h] using hs
  voters_nonempty := (expand_voters k q hq inst).voters_nonempty
  k_pos := inst.k_pos
  k_le_m := inst.k_le_m

-- f applied to chain_instance at t=0 equals f applied to expand_voters inst
lemma chain_instance_zero_output (k q : ℕ) (hq : 0 < q)
    (inst inst' : ABCInstance (Fin k) (Cand k) k) (i : Fin k)
    (hvar : inst.is_i_variant inst' i)
    (f : ABCRule (Fin (q * k)) (Cand k) k) :
    f (chain_instance k q hq inst inst' i hvar 0) = f (expand_voters k q hq inst) := by
  apply f.extensional
  · rfl  -- voters
  · rfl  -- candidates
  · intro v _
    simp only [chain_instance, expand_voters, Nat.not_lt_zero, and_false, ↓reduceIte]

-- f applied to chain_instance at t ≥ q equals f applied to expand_voters inst'
lemma chain_instance_ge_q_output (k q : ℕ) (hq : 0 < q)
    (inst inst' : ABCInstance (Fin k) (Cand k) k) (i : Fin k)
    (hvar : inst.is_i_variant inst' i) (t : ℕ) (ht : t ≥ q)
    (f : ABCRule (Fin (q * k)) (Cand k) k) :
    f (chain_instance k q hq inst inst' i hvar t) = f (expand_voters k q hq inst') := by
  classical
  apply f.extensional
  · -- voters are equal
    simp only [chain_instance, expand_voters]
    ext v
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
      refine Finset.mem_image.mpr ⟨p, ?_, rfl⟩
      have hp2 : p.2 ∈ inst.voters := (Finset.mem_product.mp hp).2
      rw [hvar.1] at hp2
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hp2⟩
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
      refine Finset.mem_image.mpr ⟨p, ?_, rfl⟩
      have hp2 : p.2 ∈ inst'.voters := (Finset.mem_product.mp hp).2
      rw [← hvar.1] at hp2
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hp2⟩
  · -- candidates
    simp only [chain_instance, expand_voters]
    exact hvar.2.1
  · -- approves (only for voters!)
    intro v hv
    simp only [chain_instance, expand_voters]
    simp only [chain_instance] at hv
    set p := finProdFinEquiv.symm v with hp_def
    -- v is a voter, so p.2 ∈ inst.voters
    have hp2_mem : p.2 ∈ inst.voters := (mem_expand_voters_iff k q hq inst v).mp hv
    by_cases h : p.2 = i
    · -- copy of voter i
      have hlt : p.1.1 < t := Nat.lt_of_lt_of_le p.1.isLt ht
      simp only [h, hlt, and_self, ↓reduceIte]
    · -- not voter i: use that inst and inst' agree on non-i voters
      simp only [h, false_and, ↓reduceIte]
      exact hvar.2.2 p.2 hp2_mem h

-- ApprovedCandidates of chain_instance includes those of non-i voters
lemma chain_instance_approvedCandidates_of_non_i (k q : ℕ) (hq : 0 < q)
    (inst inst' : ABCInstance (Fin k) (Cand k) k) (i : Fin k)
    (hvar : inst.is_i_variant inst' i) (t : ℕ) :
    ∀ c, (∃ v ∈ inst.voters, v ≠ i ∧ c ∈ inst.approves v) →
         c ∈ (chain_instance k q hq inst inst' i hvar t).approvedCandidates := by
  classical
  intro c ⟨v, hv, hne, hc⟩
  -- Use the first copy of voter v (index 0)
  let v' : Fin (q * k) := finProdFinEquiv (⟨0, hq⟩, v)
  have hv'_mem : v' ∈ (chain_instance k q hq inst inst' i hvar t).voters := by
    simp only [chain_instance]
    refine Finset.mem_image.mpr ⟨(⟨0, hq⟩, v), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hv⟩
  have hv'_approves : c ∈ (chain_instance k q hq inst inst' i hvar t).approves v' := by
    simp only [chain_instance, v']
    have hsymm : finProdFinEquiv.symm (finProdFinEquiv (⟨0, hq⟩, v)) = (⟨0, hq⟩, v) :=
      finProdFinEquiv.symm_apply_apply _
    simp only [hsymm, hne, false_and, ↓reduceIte]
    exact hc
  exact Finset.mem_biUnion.mpr ⟨v', hv'_mem, hv'_approves⟩

-- ApprovedCandidates of chain_instance includes inst.approves i when t < q
lemma chain_instance_approvedCandidates_of_i (k q : ℕ) (hq : 0 < q)
    (inst inst' : ABCInstance (Fin k) (Cand k) k) (i : Fin k)
    (hi : i ∈ inst.voters)
    (hvar : inst.is_i_variant inst' i) (t : ℕ) (ht : t < q) :
    inst.approves i ⊆ (chain_instance k q hq inst inst' i hvar t).approvedCandidates := by
  classical
  intro c hc
  -- Use the t-th copy of voter i (which still votes inst.approves i)
  let i' : Fin (q * k) := finProdFinEquiv (⟨t, ht⟩, i)
  have hi'_mem : i' ∈ (chain_instance k q hq inst inst' i hvar t).voters := by
    simp only [chain_instance]
    refine Finset.mem_image.mpr ⟨(⟨t, ht⟩, i), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hi⟩
  have hi'_approves : c ∈ (chain_instance k q hq inst inst' i hvar t).approves i' := by
    simp only [chain_instance, i']
    have hsymm : finProdFinEquiv.symm (finProdFinEquiv (⟨t, ht⟩, i)) = (⟨t, ht⟩, i) :=
      finProdFinEquiv.symm_apply_apply _
    simp only [hsymm, Fin.val_mk, Nat.lt_irrefl, and_false, ↓reduceIte]
    exact hc
  exact Finset.mem_biUnion.mpr ⟨i', hi'_mem, hi'_approves⟩

-- Chain instance preserves plentiful when t < q
lemma chain_instance_plentiful_lt (k q : ℕ) (hq : 0 < q)
    (inst inst' : ABCInstance (Fin k) (Cand k) k) (i : Fin k)
    (hi : i ∈ inst.voters)
    (hvar : inst.is_i_variant inst' i) (t : ℕ) (ht : t < q)
    (hpl : inst.plentiful) :
    (chain_instance k q hq inst inst' i hvar t).plentiful := by
  classical
  unfold ABCInstance.plentiful
  -- approvedCandidates of chain_instance ⊇ approvedCandidates of inst
  have hsub : inst.approvedCandidates ⊆
              (chain_instance k q hq inst inst' i hvar t).approvedCandidates := by
    intro c hc
    rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hcv⟩
    by_cases hvi : v = i
    · -- c is approved by voter i
      rw [hvi] at hcv
      exact chain_instance_approvedCandidates_of_i k q hq inst inst' i hi hvar t ht hcv
    · -- c is approved by voter v ≠ i
      exact chain_instance_approvedCandidates_of_non_i k q hq inst inst' i hvar t c ⟨v, hv, hvi, hcv⟩
  calc k ≤ inst.approvedCandidates.card := hpl
       _ ≤ (chain_instance k q hq inst inst' i hvar t).approvedCandidates.card :=
           Finset.card_le_card hsub

-- Chain instance preserves plentiful when t ≥ q (uses inst'.plentiful)
lemma chain_instance_plentiful_ge (k q : ℕ) (hq : 0 < q)
    (inst inst' : ABCInstance (Fin k) (Cand k) k) (i : Fin k)
    (hvar : inst.is_i_variant inst' i) (t : ℕ) (ht : t ≥ q)
    (hpl' : inst'.plentiful) :
    (chain_instance k q hq inst inst' i hvar t).plentiful := by
  classical
  -- At t ≥ q, chain_instance equals expand_voters inst' (via f.extensional)
  -- We prove plentiful directly using similar approach
  unfold ABCInstance.plentiful
  have hsub : inst'.approvedCandidates ⊆
              (chain_instance k q hq inst inst' i hvar t).approvedCandidates := by
    intro c hc
    rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hcv⟩
    by_cases hvi : v = i
    · -- c is approved by voter i in inst'
      rw [hvi] at hcv
      -- Use the 0-th copy of i (which approves inst'.approves i since 0 < t)
      let i' : Fin (q * k) := finProdFinEquiv (⟨0, hq⟩, i)
      have hi'_mem : i' ∈ (chain_instance k q hq inst inst' i hvar t).voters := by
        simp only [chain_instance]
        have hi_mem : i ∈ inst.voters := by rw [hvar.1, ← hvi]; exact hv
        refine Finset.mem_image.mpr ⟨(⟨0, hq⟩, i), ?_, rfl⟩
        exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hi_mem⟩
      have hi'_approves : c ∈ (chain_instance k q hq inst inst' i hvar t).approves i' := by
        simp only [chain_instance, i']
        have hsymm : finProdFinEquiv.symm (finProdFinEquiv (⟨0, hq⟩, i)) = (⟨0, hq⟩, i) :=
          finProdFinEquiv.symm_apply_apply _
        have hlt : (0 : ℕ) < t := Nat.lt_of_lt_of_le hq ht
        simp only [hsymm, Fin.val_mk, hlt, and_self, ↓reduceIte]
        exact hcv
      exact Finset.mem_biUnion.mpr ⟨i', hi'_mem, hi'_approves⟩
    · -- c is approved by voter v ≠ i in inst'
      -- By hvar, inst.approves v = inst'.approves v for v ≠ i
      have hv_inst : v ∈ inst.voters := by rw [hvar.1]; exact hv
      have happroves_eq : inst.approves v = inst'.approves v := hvar.2.2 v hv_inst hvi
      have hcv_inst : c ∈ inst.approves v := by rw [happroves_eq]; exact hcv
      exact chain_instance_approvedCandidates_of_non_i k q hq inst inst' i hvar t c
            ⟨v, hv_inst, hvi, hcv_inst⟩
  calc k ≤ inst'.approvedCandidates.card := hpl'
       _ ≤ (chain_instance k q hq inst inst' i hvar t).approvedCandidates.card :=
           Finset.card_le_card hsub

-- Adjacent chain instances form an i-variant pair
lemma chain_instance_step_variant (k q : ℕ) (hq : 0 < q)
    (inst inst' : ABCInstance (Fin k) (Cand k) k) (i : Fin k)
    (hi : i ∈ inst.voters)
    (hvar : inst.is_i_variant inst' i) (t : ℕ) (ht : t < q) :
    let chain_t := chain_instance k q hq inst inst' i hvar t
    let chain_t1 := chain_instance k q hq inst inst' i hvar (t + 1)
    let voter_t : Fin (q * k) := finProdFinEquiv (⟨t, ht⟩, i)
    chain_t.is_i_variant chain_t1 voter_t := by
  classical
  intro chain_t chain_t1 voter_t
  constructor
  · -- voters are equal
    rfl
  constructor
  · -- candidates are equal
    rfl
  · -- approvals agree for v ≠ voter_t
    intro v _ hne
    show chain_t.approves v = chain_t1.approves v
    simp only [chain_t, chain_t1, chain_instance]
    set p := finProdFinEquiv.symm v with hp_def
    by_cases h : p.2 = i
    · -- v is a copy of voter i
      -- We need to show the conditions differ: p.1.1 < t vs p.1.1 < t + 1
      -- If p = (t, i), then v = voter_t, contradiction with hne
      -- Otherwise, either both are < t, or p.1.1 = t and we get voter_t = v
      by_cases hpt : p.1.1 < t
      · -- p.1.1 < t implies p.1.1 < t + 1
        simp only [h, hpt, and_self, ↓reduceIte, Nat.lt_add_one_iff, Nat.le_of_lt hpt]
      · -- p.1.1 ≥ t
        by_cases hpt1 : p.1.1 < t + 1
        · -- p.1.1 = t exactly
          have heq : p.1.1 = t := Nat.eq_of_lt_succ_of_not_lt hpt1 hpt
          -- Then v = finProdFinEquiv (⟨t, ht⟩, i) = voter_t
          have hp1 : p.1 = ⟨t, ht⟩ := by
            ext
            simp only [Fin.val_mk]
            exact heq
          have hv_eq : v = voter_t := by
            have hp_eq : p = (⟨t, ht⟩, i) := Prod.ext hp1 h
            calc v = finProdFinEquiv (finProdFinEquiv.symm v) :=
                     (finProdFinEquiv.apply_symm_apply v).symm
                 _ = finProdFinEquiv p := rfl
                 _ = finProdFinEquiv (⟨t, ht⟩, i) := by rw [hp_eq]
                 _ = voter_t := rfl
          exact absurd hv_eq hne
        · -- p.1.1 ≥ t + 1, so both conditions are false
          simp only [h, hpt, and_false, ↓reduceIte, hpt1]
    · -- v is not a copy of voter i
      simp only [h, false_and, ↓reduceIte]

-- The approval that changes is inst.approves i → inst'.approves i
lemma chain_instance_step_approval (k q : ℕ) (hq : 0 < q)
    (inst inst' : ABCInstance (Fin k) (Cand k) k) (i : Fin k)
    (hvar : inst.is_i_variant inst' i) (t : ℕ) (ht : t < q) :
    let chain_t := chain_instance k q hq inst inst' i hvar t
    let chain_t1 := chain_instance k q hq inst inst' i hvar (t + 1)
    let voter_t : Fin (q * k) := finProdFinEquiv (⟨t, ht⟩, i)
    chain_t.approves voter_t = inst.approves i ∧
    chain_t1.approves voter_t = inst'.approves i := by
  intro chain_t chain_t1 voter_t
  have hpair : finProdFinEquiv.symm voter_t = (⟨t, ht⟩, i) := by
    simp only [voter_t, Equiv.symm_apply_apply]
  simp only [chain_t, chain_t1, chain_instance, hpair, Fin.val_mk]
  constructor
  · -- chain_t.approves voter_t = inst.approves i
    simp only [Nat.lt_irrefl, and_false, ↓reduceIte]
  · -- chain_t1.approves voter_t = inst'.approves i
    simp only [Nat.lt_add_one_iff, le_refl, and_self, ↓reduceIte]

-- Voter membership in chain_instance
lemma chain_instance_voter_mem (k q : ℕ) (hq : 0 < q)
    (inst inst' : ABCInstance (Fin k) (Cand k) k) (i : Fin k)
    (hi : i ∈ inst.voters)
    (hvar : inst.is_i_variant inst' i) (t : ℕ) (ht : t < q) :
    let voter_t : Fin (q * k) := finProdFinEquiv (⟨t, ht⟩, i)
    voter_t ∈ (chain_instance k q hq inst inst' i hvar t).voters := by
  intro voter_t
  simp only [chain_instance]
  refine Finset.mem_image.mpr ⟨(⟨t, ht⟩, i), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hi⟩

theorem induction_n (k q : ℕ)
    (hk : 3 ≤ k)
    (hq : 1 ≤ q)
    (f : ABCRule (Fin (q * k)) (Cand k) k)
    (hwf : f.IsWellFormed)
    (hres : f.IsResolute)
    (heff : f.SatisfiesWeakEfficiency)
    (hprop : f.SatisfiesProportionality)
    (hsp : Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f) :
    ∃ (f' : ABCRule (Fin k) (Cand k) k),
      f'.IsWellFormed ∧
      f'.IsResolute ∧
      f'.SatisfiesWeakEfficiency ∧
      f'.SatisfiesProportionality ∧
      Peters.SatisfiesResoluteStrategyproofnessOnPlentiful f' := by
    sorry

end Peters.InductionN
