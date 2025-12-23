-- ============================================================================
-- ABC VOTING PROJECT
-- ============================================================================
-- A formalization of approval ballot committee (ABC) voting rules in Lean 4.
--
-- This project studies voting rules for committees and proves key properties
-- about satisfaction of justified representation axioms and Pareto optimality.

-- ============================================================================
-- CORE DEFINITIONS
-- ============================================================================

import ABCVoting.Basic
import ABCVoting.ABCRule

-- ============================================================================
-- AXIOMS AND PROPERTIES
-- ============================================================================

import ABCVoting.Axioms.Basic
import ABCVoting.Axioms.JRAxioms
import ABCVoting.Axioms.Pareto
import ABCVoting.Axioms.Relationships
import ABCVoting.Axioms.Proportionality
import ABCVoting.Axioms.Efficiency
import ABCVoting.Axioms.Strategyproofness

-- ============================================================================
-- VOTING RULES: PROPORTIONAL APPROVAL VOTING (PAV)
-- ============================================================================

import ABCVoting.Rules.PAV.Defs
import ABCVoting.Rules.PAV.Pareto
import ABCVoting.Rules.PAV.EJR
import ABCVoting.Rules.PAV.Counterexamples

-- ============================================================================
-- VOTING RULES: METHOD OF EQUAL SHARES (MES)
-- ============================================================================

import ABCVoting.Rules.MES.Defs
import ABCVoting.Rules.MES.EJR

-- ============================================================================
-- VOTING RULES: GREEDY COHESIVE RULE (GCR)
-- ============================================================================

import ABCVoting.Rules.GreedyCohesiveRule.Defs
import ABCVoting.Rules.GreedyCohesiveRule.FJR
import ABCVoting.Rules.GreedyCohesiveRule.Existence

-- ============================================================================
-- IMPOSSIBILITY RESULTS
-- ============================================================================

import ABCVoting.Impossibilities.Peters.Main
import ABCVoting.Impossibilities.KluivingDeVriesVrijbergenBoixelEndriss.Main
