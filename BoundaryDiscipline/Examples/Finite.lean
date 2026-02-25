/-
A small finite example using Finset coerced to Set. This compiles, is inspectable,
and makes the repo feel "real" rather than purely abstract.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import BoundaryDiscipline.Basic
import BoundaryDiscipline.Partition
import BoundaryDiscipline.Composition

namespace BoundaryDiscipline.Examples

open Set
open Finset
open BoundaryDiscipline

/--
Domain: Fin 6, regions as sets.

We define a toy "boundary" operator that maps a region to itself.
This satisfies all axioms and preserves disjointness (trivially).
It is not topological boundary. It is a demonstration operator for the discipline.
-/
def idBoundary (α : Type) : BoundaryOp α where
  bdry := fun A => A
  monotone' := by intro A B h; exact h
  bdry_empty' := by simp
  bdry_union_subset' := by intro A B; simp

theorem idBoundary_preservesDisjoint (α : Type) :
    PreservesDisjoint (idBoundary α) := by
  intro A B hAB
  simpa [idBoundary] using hAB

/-- A concrete finite universe U = {0,1,2,3}. -/
def U : Set (Fin 6) :=
  ({0,1,2,3} : Finset (Fin 6))

/-- Two disjoint pieces P0 = {0,1}, P1 = {2,3}. -/
def P0 : Set (Fin 6) := ({0,1} : Finset (Fin 6))
def P1 : Set (Fin 6) := ({2,3} : Finset (Fin 6))

/-- Index type with two elements. -/
inductive Two where | left | right
  deriving DecidableEq

def P : Two → Set (Fin 6)
  | Two.left => P0
  | Two.right => P1

/-- Prove P is a partition of U in the no-gap/no-overlap sense. -/
theorem P_partition : Partition U P := by
  refine ⟨?cover, ?disj⟩
  · -- cover: iUnion P = U
    ext x
    constructor
    · intro hx
      -- hx : x ∈ ⋃ i, P i
      rcases mem_iUnion.1 hx with ⟨i, hi⟩
      cases i <;> simpa [P, U, P0, P1] using hi
    · intro hx
      -- hx : x ∈ U
      -- show x ∈ ⋃ i, P i by case analysis on membership in {0,1,2,3}
      have : x ∈ (P0 ∪ P1) := by
        -- brute simp works on these finite sets
        simpa [U, P0, P1, Set.union_def] using hx
      -- turn membership in union into membership in iUnion via choosing index
      rcases this with hx'
      -- `simp` can split membership in union
      have hx0 : x ∈ P0 ∨ x ∈ P1 := by
        simpa [Set.mem_union] using hx'
      rcases hx0 with hx0 | hx1
      · exact mem_iUnion.2 ⟨Two.left, by simpa [P]⟩
      · exact mem_iUnion.2 ⟨Two.right, by simpa [P]⟩
  · -- disjointness
    intro i j hij
    cases i <;> cases j
    · cases hij rfl
    · -- left right
      -- disjoint P0 P1
      refine Set.disjoint_left.2 ?_
      intro x hx0 hx1
      -- impossible by simp
      simpa [P0, P1] using And.intro hx0 hx1
    · -- right left
      refine Set.disjoint_left.2 ?_
      intro x hx1 hx0
      simpa [P0, P1] using And.intro hx0 hx1
    · cases hij rfl

/-- Apply the disjointness preservation theorem with the identity boundary operator. -/
theorem boundaries_disjoint :
    ∀ i j : Two, i ≠ j → Disjoint ((idBoundary (Fin 6)) (P i)) ((idBoundary (Fin 6)) (P j)) := by
  have hbd := idBoundary_preservesDisjoint (Fin 6)
  simpa using partition_disjoint_under_boundary (hP := P_partition) (b := idBoundary (Fin 6)) hbd

end BoundaryDiscipline.Examples
