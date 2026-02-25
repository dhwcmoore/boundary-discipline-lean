/-
This is the no-gap / no-overlap core. It is stated abstractly, so it works on any domain.
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import BoundaryDiscipline.Basic

namespace BoundaryDiscipline

/--
A family of regions `P : ι → Region α` forms a no-gap/no-overlap partition of `U`
when:
1) Cover (no gap): ⋃ i, P i = U
2) Pairwise disjoint (no overlap): i ≠ j → Disjoint (P i) (P j)
-/
structure Partition {α ι : Type} (U : Region α) (P : ι → Region α) : Prop where
  cover : (Set.iUnion P) = U
  disjoint : ∀ i j : ι, i ≠ j → Disjoint (P i) (P j)

namespace Partition

variable {α ι : Type} {U : Region α} {P : ι → Region α}

theorem cover_subset (h : Partition U P) : Set.iUnion P ⊆ U := by
  simpa [h.cover] using Set.Subset.rfl

theorem cover_superset (h : Partition U P) : U ⊆ Set.iUnion P := by
  simpa [h.cover] using Set.Subset.rfl

/--
Refinement: if Q refines P pointwise (every Q j sits inside some P (f j)),
and Q itself is a partition of U, then U is still covered, etc.
This is a lightweight lemma you can later strengthen into a refinement calculus.
-/
theorem refinement_preserves_cover
    {κ : Type} {Q : κ → Region α} (hQ : Partition U Q) :
    (Set.iUnion Q) = U :=
  hQ.cover

end Partition

end BoundaryDiscipline
