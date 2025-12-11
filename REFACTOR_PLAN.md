# ABCRule Refactoring Plan

## Goals

1. Build extensionality into `ABCRule` definition
2. Parameterize `ABCInstance` by `k` to eliminate `hk : inst.k = k` noise
3. Move `ABCRule.lean` to `ABCVoting/ABCRule.lean` (core file, not an axiom)

---

## Change 1: Parameterize ABCInstance by k

### Before:
```lean
structure ABCInstance (V C : Type*) where
  voters : Finset V
  candidates : Finset C
  approves : V → Finset C
  k : ℕ
  ...
```

### After:
```lean
structure ABCInstance (V C : Type*) (k : ℕ) where
  voters : Finset V
  candidates : Finset C
  approves : V → Finset C
  -- k is now a type parameter, not a field
  ...
```

### Benefit:
- Eliminates all `hk : inst.k = k` hypotheses throughout codebase
- Type-level enforcement that rules match instances

---

## Change 2: ABCRule as structure with extensionality

### Before:
```lean
def ABCRule (V C : Type*) [DecidableEq V] [DecidableEq C] (k : ℕ) :=
  (inst : ABCInstance V C) → inst.k = k → Finset (Finset C)
```

### After:
```lean
structure ABCRule (V C : Type*) [DecidableEq V] [DecidableEq C] (k : ℕ) where
  apply : ABCInstance V C k → Finset (Finset C)
  extensional : ∀ inst inst',
    inst.voters = inst'.voters →
    inst.candidates = inst'.candidates →
    (∀ v ∈ inst.voters, inst.approves v = inst'.approves v) →
    apply inst = apply inst'
```

### Add coercion:
```lean
instance : CoeFun (ABCRule V C k) (fun _ => ABCInstance V C k → Finset (Finset C)) where
  coe f := f.apply
```

---

## Change 3: File reorganization

- Move `ABCVoting/Axioms/ABCRule.lean` → `ABCVoting/ABCRule.lean`
- It's the core type definition, not an axiom

---

## Files to update

1. **Basic.lean** - Add `k` parameter to `ABCInstance`
2. **ABCRule.lean** - Structure with extensionality, move to root
3. **Strategyproofness.lean** - Remove `hk` args, remove `IsBallotExtensional`
4. **Proportionality.lean** - Remove `hk` args
5. **Efficiency.lean** - Remove `hk` args
6. **Rules/PAV/** - Construct with extensionality proof, remove `hk` args
7. **SingletonApprovers.lean** - Remove `hk` args, remove extensionality hypotheses

---

## Proving extensionality for concrete rules

For PAV: The score `Σ v ∈ inst.voters, ...` only uses `inst.approves v` for voters.
If two instances agree on `approves` for all voters, scores are equal, so maximizers are equal.

Similar for Phragmén, MES, etc.
