import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import BoundaryDiscipline.Basic
import BoundaryDiscipline.Partition
import BoundaryDiscipline.Composition

namespace BoundaryDiscipline

/-
A trace-carrying boundary operator.
The goal is auditability: an operator can be transported with a human-readable
trace of the composition path, without changing the underlying semantics.
-/

variable {α : Type}

structure TracedBoundaryOp (α : Type) where
  trace : List String
  op : BoundaryOp α

namespace TracedBoundaryOp

instance : CoeFun (TracedBoundaryOp α) (fun _ => Region α → Region α) where
  coe t := t.op

/-- Extract the underlying boundary operator. -/
def underlying (t : TracedBoundaryOp α) : BoundaryOp α := t.op

/-- A traced identity operator. -/
def id (α : Type) : TracedBoundaryOp α where
  trace := ["id"]
  op := {
    bdry := fun A => A
    monotone' := by
      intro A B hAB
      exact hAB
    bdry_empty' := by
      simp
    bdry_union_subset' := by
      intro A B
      simp
  }

/--
Attach a label to an existing operator.
This is useful when you already have an operator but want it to show up in audits.
-/
def label (name : String) (b : BoundaryOp α) : TracedBoundaryOp α where
  trace := [name]
  op := b

/--
Compose traced operators.
Convention: (t₂ ⊚ t₁) means apply t₁ first, then t₂.
Trace concatenation is t₁.trace ++ t₂.trace, so reading left-to-right gives the
application order.
-/
def comp (t₂ t₁ : TracedBoundaryOp α) : TracedBoundaryOp α where
  trace := t₁.trace ++ t₂.trace
  op := t₂.op ⊚ t₁.op

infixr:90 " ⊚ " => comp

/-- Monotonicity is inherited from the underlying operator. -/
theorem monotone (t : TracedBoundaryOp α) : Monotone t.op := t.op.monotone

/-- Boundary of empty is inherited. -/
theorem bdry_empty (t : TracedBoundaryOp α) : t.op ∅ = ∅ := t.op.bdry_empty

/-- Union-subset axiom is inherited. -/
theorem bdry_union_subset (t : TracedBoundaryOp α) (A B : Region α) :
    t.op (A ∪ B) ⊆ t.op A ∪ t.op B :=
  t.op.bdry_union_subset A B

/--
If each component preserves disjointness, then the composed traced operator
preserves disjointness, and the trace records the composition.
This is the auditable version of the lemma in `BoundaryDiscipline.Composition`.
-/
theorem preservesDisjoint_comp
    (t₂ t₁ : TracedBoundaryOp α)
    (h₁ : PreservesDisjoint t₁.op)
    (h₂ : PreservesDisjoint t₂.op) :
    PreservesDisjoint (t₂ ⊚ t₁).op := by
  -- Under the hood, it is exactly the same proof as the non-traced version.
  simpa [TracedBoundaryOp.comp] using PreservesDisjoint.comp (t₂.op) (t₁.op) h₁ h₂

/--
Constraint propagation with audit trace:
If P is a no-gap/no-overlap partition and the traced operator preserves disjointness,
then the boundary images of pieces remain disjoint.
-/
theorem partition_disjoint_under_traced_boundary
    {ι : Type} {U : Region α} {P : ι → Region α}
    (hP : Partition U P)
    (t : TracedBoundaryOp α)
    (hbd : PreservesDisjoint t.op) :
    ∀ i j : ι, i ≠ j → Disjoint (t (P i)) (t (P j)) := by
  intro i j hij
  -- Use the existing theorem from Composition.lean.
  have := partition_disjoint_under_boundary (hP := hP) (b := t.op) hbd
  simpa using this i j hij

end TracedBoundaryOp

end BoundaryDiscipline
