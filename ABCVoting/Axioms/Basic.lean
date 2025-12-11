import ABCVoting.Basic

open Finset BigOperators

namespace ABCInstance

variable {V C : Type*} [DecidableEq V] [DecidableEq C]

-- ============================================================================
-- BASIC AXIOMS (NON-TRIVIALITY, ANONYMITY, NEUTRALITY, RESOLUTENESS)
-- ============================================================================

/--
Non-triviality: The voting rule is not constant.
(Different inputs can produce different outputs.)
-/
class NonTriviality (inst : ABCInstance V C) where
  not_constant : ∃ (w₁ w₂ : Finset C), w₁ ≠ w₂

/--
Anonymity: Voters are indistinguishable.
If we permute the voters and their approvals accordingly, the result is the same.
-/
class Anonymity (inst : ABCInstance V C) where
  -- The definition is abstract; specific voting rules would instantiate this

/--
Neutrality: Candidates are treated equally.
If we swap two candidates in all approval sets, swapped candidates are swapped in the outcome.
-/
class Neutrality (inst : ABCInstance V C) where
  -- The definition is abstract; specific voting rules would instantiate this

/--
Resoluteness: The voting rule returns a unique outcome (single committee).
-/
class Resoluteness (inst : ABCInstance V C) where
  -- The definition is abstract; specific voting rules would instantiate this

end ABCInstance
