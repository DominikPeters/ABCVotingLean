/-
# Core Inequality for PAV

This file verifies the key inequality used in the proof that PAV satisfies
the core for committee size k ≤ 7.

The inequality states that for any ballot A that strictly prefers a potential
deviation T to the committee W, the contribution δ_A to the sum of PAV score
differences satisfies:

  δ_A > (k/|T| - 1) · |T \ W|

This is Inequality (3) in the paper "The Core of Approval-Based Committee
Elections with Few Candidates" by Dominik Peters.
-/

import ABCVoting.Basic

open Finset BigOperators

/-!
## Key Definitions

The inequality involves these quantities:
- `k`: committee size
- `T_size`: size of the potential deviation |T|
- `W_cap_T`: size of W ∩ T
- `W_minus_T`: size of W \ T = k - W_cap_T
- `T_minus_W`: size of T \ W = T_size - W_cap_T
- `a`: |(W \ T) ∩ A| (approved candidates in W \ T)
- `b`: |(W ∩ T) ∩ A| (approved candidates in W ∩ T)
- `c`: |(T \ W) ∩ A| (approved candidates in T \ W)

The ballot prefers T to W iff u_A(T) > u_A(W), i.e., b + c > a + b, i.e., c > a.
-/

/--
The δ_A value: contribution of ballot A to the sum of PAV score differences.

δ_A = [(W_minus_T - a) · c] / (a + b + 1) - [a · (T_minus_W - c)] / (a + b)

When a + b = 0, the second term is 0 (since a = 0).
-/
noncomputable def delta_A (W_minus_T T_minus_W a b c : ℕ) : ℚ :=
  (W_minus_T - a : ℚ) * c / (a + b + 1) - a * (T_minus_W - c) / (a + b)

/--
The right-hand side of the inequality: (k/|T| - 1) · |T \ W|
-/
noncomputable def core_rhs (k T_size T_minus_W : ℕ) : ℚ :=
  ((k : ℚ) / T_size - 1) * T_minus_W

/--
The core inequality that needs to hold for ballots preferring T to W.
-/
def core_ineq_holds (k T_size W_cap_T a b c : ℕ) : Prop :=
  let W_minus_T := k - W_cap_T
  let T_minus_W := T_size - W_cap_T
  delta_A W_minus_T T_minus_W a b c > core_rhs k T_size T_minus_W

/-!
## Simplified form for computation

To make the inequality decidable, we clear denominators and work with integers.
The inequality δ_A > RHS becomes (after multiplying by positive denominators):

  (W_minus_T - a) * c * (a + b) * T_size - a * (T_minus_W - c) * (a + b + 1) * T_size
  > (k - T_size) * T_minus_W * (a + b + 1) * (a + b)

Note: When a + b = 0, we have a = b = 0, so the inequality simplifies to:
  W_minus_T * c * T_size > (k - T_size) * T_minus_W
-/

/--
Cleared-denominator version of the inequality for the case a + b > 0.
-/
def core_ineq_cleared (k T_size W_cap_T a b c : ℕ) : Prop :=
  let W_minus_T := k - W_cap_T
  let T_minus_W := T_size - W_cap_T
  (W_minus_T - a) * c * (a + b) * T_size - a * (T_minus_W - c) * (a + b + 1) * T_size
  > (k - T_size) * T_minus_W * (a + b + 1) * (a + b)

/--
Cleared-denominator version for the case a + b = 0 (so a = 0).
-/
def core_ineq_cleared_ab_zero (k T_size W_cap_T c : ℕ) : Prop :=
  let W_minus_T := k - W_cap_T
  let T_minus_W := T_size - W_cap_T
  W_minus_T * c * T_size > (k - T_size) * T_minus_W

/-!
## Test cases

Let's verify some specific cases to ensure our definitions are correct.
-/

-- k=7, T_size=4, W_cap_T=2 means W_minus_T=5, T_minus_W=2
-- RHS = (7/4 - 1) * 2 = 3/4 * 2 = 3/2
example : core_rhs 7 4 2 = 3/2 := by unfold core_rhs; norm_num

-- With a=0, b=0, c=1: δ_A = 5*1/1 - 0 = 5 > 3/2 ✓
example : delta_A 5 2 0 0 1 = 5 := by unfold delta_A; norm_num

-- With a=0, b=1, c=1: δ_A = 5*1/2 - 0 = 5/2 > 3/2 ✓
example : delta_A 5 2 0 1 1 = 5/2 := by unfold delta_A; norm_num

/-!
## Main verification

We verify the inequality for all valid parameter combinations with k ≤ 7.

Valid parameters satisfy:
- 1 ≤ T_size < k
- 0 ≤ W_cap_T < T_size (so T_minus_W > 0)
- 0 ≤ a ≤ W_minus_T = k - W_cap_T
- 0 ≤ b ≤ W_cap_T
- 0 ≤ c ≤ T_minus_W = T_size - W_cap_T
- c > a (ballot prefers T to W)
-/

-- First, let's try a specific small case to see if the approach works
theorem core_ineq_k2_t1 :
    ∀ W_cap_T a b c : ℕ,
    W_cap_T < 1 →  -- W_cap_T = 0
    a ≤ 2 - W_cap_T →
    b ≤ W_cap_T →
    c ≤ 1 - W_cap_T →
    c > a →
    core_ineq_holds 2 1 W_cap_T a b c := by
  intro W_cap_T a b c hWT ha hb hc hpref
  interval_cases W_cap_T
  -- W_cap_T = 0, so W_minus_T = 2, T_minus_W = 1
  -- a ≤ 2, b ≤ 0 (so b = 0), c ≤ 1, c > a
  -- Since c ≤ 1 and c > a ≥ 0, we have c = 1 and a = 0
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
  simp_all only [core_ineq_holds, delta_A, core_rhs] <;> norm_num

-- k=3, T_size ∈ {1, 2}
theorem core_ineq_k3 :
    ∀ T_size W_cap_T a b c : ℕ,
    1 ≤ T_size → T_size < 3 →
    W_cap_T < T_size →
    a ≤ 3 - W_cap_T →
    b ≤ W_cap_T →
    c ≤ T_size - W_cap_T →
    c > a →
    core_ineq_holds 3 T_size W_cap_T a b c := by
  intro T_size W_cap_T a b c hT1 hT2 hWT ha hb hc hpref
  unfold core_ineq_holds delta_A core_rhs
  interval_cases T_size <;> interval_cases W_cap_T <;>
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
  simp_all <;> norm_num

-- k=4, T_size ∈ {1, 2, 3}
theorem core_ineq_k4 :
    ∀ T_size W_cap_T a b c : ℕ,
    1 ≤ T_size → T_size < 4 →
    W_cap_T < T_size →
    a ≤ 4 - W_cap_T →
    b ≤ W_cap_T →
    c ≤ T_size - W_cap_T →
    c > a →
    core_ineq_holds 4 T_size W_cap_T a b c := by
  intro T_size W_cap_T a b c hT1 hT2 hWT ha hb hc hpref
  unfold core_ineq_holds delta_A core_rhs
  interval_cases T_size <;> interval_cases W_cap_T <;>
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
  simp_all <;> norm_num

-- k=5
theorem core_ineq_k5 :
    ∀ T_size W_cap_T a b c : ℕ,
    1 ≤ T_size → T_size < 5 →
    W_cap_T < T_size →
    a ≤ 5 - W_cap_T →
    b ≤ W_cap_T →
    c ≤ T_size - W_cap_T →
    c > a →
    core_ineq_holds 5 T_size W_cap_T a b c := by
  intro T_size W_cap_T a b c hT1 hT2 hWT ha hb hc hpref
  unfold core_ineq_holds delta_A core_rhs
  interval_cases T_size <;> interval_cases W_cap_T <;>
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
  simp_all <;> norm_num

-- k=6
theorem core_ineq_k6 :
    ∀ T_size W_cap_T a b c : ℕ,
    1 ≤ T_size → T_size < 6 →
    W_cap_T < T_size →
    a ≤ 6 - W_cap_T →
    b ≤ W_cap_T →
    c ≤ T_size - W_cap_T →
    c > a →
    core_ineq_holds 6 T_size W_cap_T a b c := by
  intro T_size W_cap_T a b c hT1 hT2 hWT ha hb hc hpref
  simp only [core_ineq_holds, delta_A, core_rhs]
  interval_cases T_size <;> interval_cases W_cap_T <;>
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
  simp_all <;> norm_num

-- k=7, the main result
-- Split by T_size to avoid timeout
theorem core_ineq_k7_t1 :
    ∀ W_cap_T a b c : ℕ,
    W_cap_T < 1 →
    a ≤ 7 - W_cap_T →
    b ≤ W_cap_T →
    c ≤ 1 - W_cap_T →
    c > a →
    core_ineq_holds 7 1 W_cap_T a b c := by
  intro W_cap_T a b c hWT ha hb hc hpref
  simp only [core_ineq_holds, delta_A, core_rhs]
  interval_cases W_cap_T <;>
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
  simp_all <;> norm_num

theorem core_ineq_k7_t2 :
    ∀ W_cap_T a b c : ℕ,
    W_cap_T < 2 →
    a ≤ 7 - W_cap_T →
    b ≤ W_cap_T →
    c ≤ 2 - W_cap_T →
    c > a →
    core_ineq_holds 7 2 W_cap_T a b c := by
  intro W_cap_T a b c hWT ha hb hc hpref
  simp only [core_ineq_holds, delta_A, core_rhs]
  interval_cases W_cap_T <;>
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
  simp_all <;> norm_num

theorem core_ineq_k7_t3 :
    ∀ W_cap_T a b c : ℕ,
    W_cap_T < 3 →
    a ≤ 7 - W_cap_T →
    b ≤ W_cap_T →
    c ≤ 3 - W_cap_T →
    c > a →
    core_ineq_holds 7 3 W_cap_T a b c := by
  intro W_cap_T a b c hWT ha hb hc hpref
  simp only [core_ineq_holds, delta_A, core_rhs]
  interval_cases W_cap_T <;>
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
  simp_all <;> norm_num

theorem core_ineq_k7_t4 :
    ∀ W_cap_T a b c : ℕ,
    W_cap_T < 4 →
    a ≤ 7 - W_cap_T →
    b ≤ W_cap_T →
    c ≤ 4 - W_cap_T →
    c > a →
    core_ineq_holds 7 4 W_cap_T a b c := by
  intro W_cap_T a b c hWT ha hb hc hpref
  simp only [core_ineq_holds, delta_A, core_rhs]
  interval_cases W_cap_T <;>
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
  simp_all <;> norm_num

theorem core_ineq_k7_t5 :
    ∀ W_cap_T a b c : ℕ,
    W_cap_T < 5 →
    a ≤ 7 - W_cap_T →
    b ≤ W_cap_T →
    c ≤ 5 - W_cap_T →
    c > a →
    core_ineq_holds 7 5 W_cap_T a b c := by
  intro W_cap_T a b c hWT ha hb hc hpref
  simp only [core_ineq_holds, delta_A, core_rhs]
  interval_cases W_cap_T <;>
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
  simp_all <;> norm_num

theorem core_ineq_k7_t6 :
    ∀ W_cap_T a b c : ℕ,
    W_cap_T < 6 →
    a ≤ 7 - W_cap_T →
    b ≤ W_cap_T →
    c ≤ 6 - W_cap_T →
    c > a →
    core_ineq_holds 7 6 W_cap_T a b c := by
  intro W_cap_T a b c hWT ha hb hc hpref
  simp only [core_ineq_holds, delta_A, core_rhs]
  interval_cases W_cap_T <;>
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
  simp_all <;> norm_num

-- Combine all T_size cases for k=7
theorem core_ineq_k7 :
    ∀ T_size W_cap_T a b c : ℕ,
    1 ≤ T_size → T_size < 7 →
    W_cap_T < T_size →
    a ≤ 7 - W_cap_T →
    b ≤ W_cap_T →
    c ≤ T_size - W_cap_T →
    c > a →
    core_ineq_holds 7 T_size W_cap_T a b c := by
  intro T_size W_cap_T a b c hT1 hT2 hWT ha hb hc hpref
  interval_cases T_size
  · exact core_ineq_k7_t1 W_cap_T a b c hWT ha hb hc hpref
  · exact core_ineq_k7_t2 W_cap_T a b c hWT ha hb hc hpref
  · exact core_ineq_k7_t3 W_cap_T a b c hWT ha hb hc hpref
  · exact core_ineq_k7_t4 W_cap_T a b c hWT ha hb hc hpref
  · exact core_ineq_k7_t5 W_cap_T a b c hWT ha hb hc hpref
  · exact core_ineq_k7_t6 W_cap_T a b c hWT ha hb hc hpref
