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
    * satisfies core up to k=7
    * satisfies Pareto-optimality
* Method of Equal Shares (MES), uncompleted
    * satisfies EJR+

# Impossibility Results

* Peters' impossibility: No ABC rule can satisfy strategyproofness, weak efficiency, and proportionality.

# Future Work

* Define priceability, show it implies PJR+
* Define seqPhragmen, show it satisfies priceability and PJR+
* Formalize various counterexamples (core failures for PAV at k=9, MES failing core; Phragmen failing EJR, PO-failures for MES and Phragmen)
* Define Greedy Cohesive Rule and use it to prove that FJR exists
* GJCR?
* Sub-core?
* Stuff from Janson (e.g. monotonicity properties)
* perhaps: PAV intersects core for k = 8
* Proportionality degree (definition, EJR => 1/2, l-1 => EJR, extreme stretch goal: prop degree of Phragmen, and seqPav results)
* Prove impossibility for irresolute rules (https://staff.fnwi.uva.nl/u.endriss/pubs/files/KluivingEtAlECAI2020.pdf)
* CC and utilitarian approximations?
* Approximations to the core, disjoint core => 2-utility approximation, extreme stretch goal: show 32-Kamesh result