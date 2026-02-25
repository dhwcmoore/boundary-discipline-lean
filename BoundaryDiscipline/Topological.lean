import Mathlib.Topology.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import BoundaryDiscipline.Basic

namespace BoundaryDiscipline

/-
A canonical topological instance.
In mathlib, the topological boundary of a set is `frontier`.
We package `frontier` as a `BoundaryOp`, proving the minimal axioms from `Basic.lean`.

Important: we do NOT assert that `frontier` preserves disjointness.
In general it does not. If you want a disjointness-preservation result, you must
add explicit separation hypotheses (and those hypotheses vary by topology).
-/

open Set

variable {α : Type} [TopologicalSpace α]

/-- The topological boundary operator as a `BoundaryOp`. -/
def topoBoundaryOp (α : Type) [TopologicalSpace α] : BoundaryOp α where
  bdry := frontier
  monotone' := by
    intro A B hAB
    exact Monotone.frontier hAB
  bdry_empty' := by
    exact frontier_empty
  bdry_union_subset' := by
    intro A B
    exact frontier_union_subset A B

namespace topoBoundaryOp

/--
A small, useful fact: topological boundary is always contained in closure.
This is a standard property of `frontier` in mathlib.
-/
theorem boundary_subset_closure (A : Region α) :
    (topoBoundaryOp α) A ⊆ closure A := by
  unfold topoBoundaryOp
  exact frontier_subset_closure A

/--
Another standard fact: the boundary is disjoint from the interior complement
formulation is available via inclusion into the complement of the interior.
This lemma is a discipline-friendly way to express that boundary points are not
interior points, without committing to stronger separation axioms.
-/
theorem boundary_subset_compl_interior (A : Region α) :
    (topoBoundaryOp α) A ⊆ (interior A)ᶜ := by
  unfold topoBoundaryOp
  exact frontier_subset_compl_interior A

/--
Union behaviour, restated in the `BoundaryOp` vocabulary.
-/
theorem boundary_union_subset (A B : Region α) :
    (topoBoundaryOp α) (A ∪ B) ⊆ (topoBoundaryOp α) A ∪ (topoBoundaryOp α) B := by
  unfold topoBoundaryOp
  exact frontier_union_subset A B

end topoBoundaryOp

end BoundaryDiscipline
