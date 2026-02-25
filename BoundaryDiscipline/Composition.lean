/-
Here we connect boundary operators to partitions, and prove something nontrivial but honest:
boundary images preserve disjointness under a strong but checkable condition
(a "non-interference" constraint). This is exactly the kind of "discipline" you want:
explicit assumptions, explicit guarantee.
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import BoundaryDiscipline.Basic
import BoundaryDiscipline.Partition

namespace BoundaryDiscipline

open Set

variable {α ι : Type}

/--
A sufficient condition for a boundary operator to preserve disjointness:
if A and B are disjoint, then bdry A and bdry B are disjoint.

This is not always true in topology, and that is fine: this repo is discipline-first,
so we surface the condition as an explicit contract.
-/
def PreservesDisjoint (b : BoundaryOp α) : Prop :=
  ∀ A B : Region α, Disjoint A B → Disjoint (b A) (b B)

namespace PreservesDisjoint

theorem comp
    (b₂ b₁ : BoundaryOp α)
    (h₁ : PreservesDisjoint b₁)
    (h₂ : PreservesDisjoint b₂) :
    PreservesDisjoint (b₂ ⊚ b₁) := by
  intro A B hAB
  have : Disjoint (b₁ A) (b₁ B) := h₁ A B hAB
  exact h₂ (b₁ A) (b₁ B) this

end PreservesDisjoint

/--
If P is a no-gap/no-overlap partition of U, and b preserves disjointness,
then the family (b ∘ P) remains pairwise disjoint.

This is a typical "constraint propagation" theorem:
the partition constraint is stable under a boundary transformation, given a contract.
-/
theorem partition_disjoint_under_boundary
    {U : Region α} {P : ι → Region α}
    (hP : Partition U P)
    (b : BoundaryOp α)
    (hbd : PreservesDisjoint b) :
    ∀ i j : ι, i ≠ j → Disjoint (b (P i)) (b (P j)) := by
  intro i j hij
  apply hbd
  exact hP.disjoint i j hij

end BoundaryDiscipline
