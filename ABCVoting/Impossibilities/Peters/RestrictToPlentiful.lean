/-
Definitions of axioms restricted to plentiful instances
-/

import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Strategyproofness

open Finset BigOperators
open ABCInstance

namespace Peters

variable {V C : Type*} [DecidableEq V] [DecidableEq C] {k : ℕ}

/--
Resolute strategyproofness restricted to *plentiful* instances.

This matches Peters' convention of implicitly restricting the domain of the rule to profiles
with at least `k` approved candidates in total (so that a size-`k` committee can be formed
using only approved candidates).
-/
def SatisfiesResoluteStrategyproofnessOnPlentiful (f : ABCRule V C k) : Prop :=
  ∀ (inst inst' : ABCInstance V C k) (i : V),
    inst.plentiful →
    inst'.plentiful →
    i ∈ inst.voters →
    inst.is_i_variant inst' i →
    inst'.approves i ⊂ inst.approves i →
    ∀ (hres : f.IsResolute),
      ¬((f.resolute_committee inst' hres) ∩ inst.approves i ⊃
        (f.resolute_committee inst hres) ∩ inst.approves i)

lemma strategyproof_onPlentiful_of_strategyproof (f : ABCRule V C k)
    (hsp : f.SatisfiesResoluteStrategyproofness) :
    SatisfiesResoluteStrategyproofnessOnPlentiful f := by
  intro inst inst' i _ _ hi hvar hsub hres
  exact hsp inst inst' i hi hvar hsub hres

/--
Well-formed restricted to plentiful instances.
-/
def IsWellFormedOnPlentiful (f : ABCRule V C k) : Prop :=
  ∀ (inst : ABCInstance V C k),
    inst.plentiful →
    (f inst).Nonempty ∧
    ∀ W ∈ f inst, W.card = k ∧ W ⊆ inst.candidates

lemma well_formed_onPlentiful_of_well_formed (f : ABCRule V C k)
    (hwf : f.IsWellFormed) :
    IsWellFormedOnPlentiful f := by
  intro inst hpl
  exact hwf inst

end Peters
