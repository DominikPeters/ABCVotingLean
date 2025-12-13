# Formalizing the Theory of Approval-Based Committee Voting in Lean 4

This repository contains a formalization of the theory of approval-based committee voting (ABC voting) in the Lean 4 proof assistant. It includes definitions and proofs of various voting rules, axioms, and their relationships.

# Axioms

* JR, PJR, EJR, EJR+, FJR, FPJR
* Core, Disjoint Core
* Pareto-optimality
* Implications between axioms (e.g., Core implies FJR, EJR+ implies EJR)

# Voting Rules

* Proportional Approval Voting (PAV)
    * satisfies EJR+
    * satisfies disjoint core
    * (in progress) satisfies core up to k=7
    * satisfies Paretro-optimality
* Method of Equal Shares (MES), uncompleted
    * satisfies EJR+

# Impossibility Results

* (in progress) Peters' impossibility: No ABC rule can satisfy strategyproofness, weak efficiency, and proportionality.
