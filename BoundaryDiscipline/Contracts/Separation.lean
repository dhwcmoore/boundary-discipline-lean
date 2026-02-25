import Mathlib.Topology.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import BoundaryDiscipline.Basic
import BoundaryDiscipline.Topological
import BoundaryDiscipline.Composition

namespace BoundaryDiscipline

open Set

variable {α : Type} [TopologicalSpace α]

/-
Discipline contract for topological boundary:

Topological boundary does not preserve disjointness in general.
So we do not pretend it does.

Instead, we expose explicit separation hypotheses that are sufficient.

Contract S1:
  Disjoint (closure A) (closure B)

Guarantee G1:
  Disjoint (frontier A) (frontier B)

This is strong but honest, and it composes well with your Partition story:
to preserve no-overlap constraints under topological boundary, require closure-level
separation of partition pieces (or whatever weaker variant you later develop).
-/

/--
S1 → G1:
If closures are disjoint, then boundaries are disjoint.
This is a general topological fact, requiring no extra separation axioms,
because frontier is always a subset of closure.
-/
theorem frontier_disjoint_of_closure_disjoint
    (A B : Region α)
    (h : Disjoint (closure A) (closure B)) :
    Disjoint (frontier A) (frontier B) := by
  -- Use Disjoint.mono with subset facts.
  refine h.mono ?_ ?_
  · exact frontier_subset_closure
  · exact frontier_subset_closure

/--
A discipline-friendly contract wrapper for the `topoBoundaryOp`.
Under the closure-disjointness hypothesis, `topoBoundaryOp` preserves disjointness.
-/
theorem topoBoundaryOp_preservesDisjoint_of_closure_disjoint :
    (∀ A B : Region α, Disjoint (closure A) (closure B) →
      Disjoint ((topoBoundaryOp α) A) ((topoBoundaryOp α) B)) := by
  intro A B h
  -- `(topoBoundaryOp α) A` is `frontier A`
  simpa [topoBoundaryOp] using frontier_disjoint_of_closure_disjoint (α := α) A B h

/--
Partition-level consequence (conditional):

If P is a no-gap/no-overlap partition of U, and additionally every distinct pair
of pieces has disjoint closures, then applying topological boundary to each piece
preserves pairwise disjointness.

This is the exact "discipline" pattern you want:
- base constraint: disjoint pieces
- additional contract: closure-disjointness
- derived guarantee: boundary images disjoint
-/
theorem partition_disjoint_under_topoBoundaryOp_of_closure_disjoint
    {ι : Type} {U : Region α} {P : ι → Region α}
    (hP : Partition U P)
    (hClosure : ∀ i j : ι, i ≠ j → Disjoint (closure (P i)) (closure (P j))) :
    ∀ i j : ι, i ≠ j →
      Disjoint ((topoBoundaryOp α) (P i)) ((topoBoundaryOp α) (P j)) := by
  intro i j hij
  -- apply closure-disjointness contract, then use the boundary theorem
  have hcl : Disjoint (closure (P i)) (closure (P j)) := hClosure i j hij
  -- now conclude boundary disjointness
  simpa [topoBoundaryOp] using frontier_disjoint_of_closure_disjoint (α := α) (P i) (P j) hcl

end BoundaryDiscipline
