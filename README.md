Good. We will make this read like it belongs in a formal methods lab, not a philosophical preface.

The changes below:

* Remove motivational framing.
* Remove narrative tone.
* Emphasise structure, invariants, and theorem statements.
* Include a stronger compositional preservation example.

You can replace your README entirely with the following.

---

# Boundary Discipline (Lean)

A Lean 4 + mathlib formalisation of a small kernel for reasoning about regions, partitions, and boundary operators.

The repository is intentionally narrow. It defines explicit structural invariants and proves preservation results under refinement and operator composition.

---

## Scope

The kernel formalises:

* Regions as sets over a carrier type.
* No-gap / no-overlap partitions as correctness constraints.
* Boundary operators as structured endomaps on regions.
* Preservation of structural invariants under refinement and composition.

All definitions and results are stated and proved in Lean 4 using mathlib.

The surface area is controlled. There is no informal layer.

---

## Core definitions

### Regions

```lean
abbrev Region (α : Type*) := Set α
```

All reasoning is conducted over `Set α`.

---

### Partition constraints

A partition is characterised by two invariants:

* Coverage (no gap)
* Pairwise disjointness (no overlap)

Representative definitions:

```lean
import Mathlib.Data.Set.Basic

variable {α : Type*}

def NoOverlap (P : Set (Set α)) : Prop :=
  ∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B

def Covers (P : Set (Set α)) (U : Set α) : Prop :=
  ⋃₀ P = U
```

These predicates are used explicitly in refinement and preservation theorems.

---

## Boundary operators

Boundary operators are treated as structured maps:

```lean
def BoundaryOp (α : Type*) :=
  Set α → Set α
```

Operators are studied under properties such as:

* Monotonicity:
  `A ⊆ B → B(A) ⊆ B(B)`
* Stability under restriction.
* Behaviour under composition.

---

## Compositional preservation

A central concern is that invariants are stable under operator composition.

Below is a representative composition lemma illustrating preservation under two monotone operators.

```lean
import Mathlib.Data.Set.Basic

variable {α : Type*}

def MonotoneOp (B : Set α → Set α) : Prop :=
  ∀ {A C : Set α}, A ⊆ C → B A ⊆ B C

theorem monotone_comp
  {B₁ B₂ : Set α → Set α}
  (h₁ : MonotoneOp B₁)
  (h₂ : MonotoneOp B₂) :
  MonotoneOp (fun A => B₂ (B₁ A)) :=
by
  intro A C hAC
  apply h₂
  apply h₁
  exact hAC
```

More structurally, if a boundary operator preserves disjointness and coverage, then its composition with another such operator preserves those invariants as well, provided both satisfy the required monotonicity and stability conditions.

The repository contains explicit statements and proofs of these preservation properties.

---

## Repository structure

```text
BoundaryDiscipline/
  Basic.lean
  Partition.lean
  Composition.lean
  Topological.lean

BoundaryDiscipline.lean
lakefile.lean
```

* `Basic.lean`
  Core definitions and operator structure.

* `Partition.lean`
  Formalisation of coverage and disjointness constraints.

* `Composition.lean`
  Composition lemmas and preservation theorems.

* `Topological.lean`
  Topological lemmas using mathlib primitives.

---

## Build

Requires:

* Lean 4
* mathlib

From the repository root:

```bash
lake build
```

The project builds without local patches.

---

## Extensions

The kernel is designed to support further work in:

* RCC8-style spatial relations
* Region algebras and gluing constructions
* Typed boundary constraints
* Integration with executable verification systems

These are not implemented here. The current repository establishes the invariant-preserving core.

---

## Status

* Lean 4
* mathlib-based
* theorem-bearing
* buildable

The repository is maintained as a minimal formal core.

---

This version signals:

* You understand compositional reasoning.
* You reason in terms of invariants.
* You are comfortable proving operator-level properties.
* You are not over-selling.

If you want, we can now do one more tightening pass that removes even more narrative and pushes it closer to something that could appear in a formal methods research group’s public repository.
