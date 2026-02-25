import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Tactic

namespace BoundaryDiscipline

/--
A `Region α` is just a set of points of type `α`.
This keeps the core abstract and lets us plug in finite, topological, metric,
or symbolic domains later.
-/
abbrev Region (α : Type) := Set α

/--
A `BoundaryOp α` is an operator on regions: ∂ : Region α → Region α,
equipped with axioms that make it behave like a boundary-like operator
in an abstract, discipline-first way.

These axioms are intentionally lightweight:
- monotone: respects inclusion
- empty: boundary of ∅ is ∅
- union: boundary of a union is contained in the union of boundaries

This is enough to support composition reasoning and constraint propagation.
You can strengthen later (idempotence, locality, etc.).
-/
structure BoundaryOp (α : Type) where
  bdry : Region α → Region α
  monotone' : Monotone bdry
  bdry_empty' : bdry ∅ = ∅
  bdry_union_subset' : ∀ A B : Region α, bdry (A ∪ B) ⊆ bdry A ∪ bdry B

namespace BoundaryOp

variable {α : Type}

instance : CoeFun (BoundaryOp α) (fun _ => Region α → Region α) where
  coe b := b.bdry

theorem monotone (b : BoundaryOp α) : Monotone b := b.monotone'

theorem bdry_empty (b : BoundaryOp α) : b ∅ = ∅ := b.bdry_empty'

theorem bdry_union_subset (b : BoundaryOp α) (A B : Region α) :
    b (A ∪ B) ⊆ b A ∪ b B :=
  b.bdry_union_subset' A B

/--
Compose two boundary operators. This models "boundary constraint composition"
as operator composition. The resulting operator satisfies the same axioms.
-/
def comp (b₂ b₁ : BoundaryOp α) : BoundaryOp α where
  bdry := fun A => b₂ (b₁ A)
  monotone' := by
    intro A B hAB
    exact (b₂.monotone) (b₁.monotone hAB)
  bdry_empty' := by
    simp [bdry_empty]
  bdry_union_subset' := by
    intro A B
    -- Use union-subset axiom twice.
    have h1 : b₁ (A ∪ B) ⊆ b₁ A ∪ b₁ B := b₁.bdry_union_subset A B
    have h2 : b₂ (b₁ (A ∪ B)) ⊆ b₂ (b₁ A ∪ b₁ B) := (b₂.monotone) h1
    have h3 : b₂ (b₁ A ∪ b₁ B) ⊆ b₂ (b₁ A) ∪ b₂ (b₁ B) := b₂.bdry_union_subset (b₁ A) (b₁ B)
    exact Set.Subset.trans h2 h3

/-- Notation for composition (right-to-left). -/
infixr:90 " ⊚ " => comp

end BoundaryOp

end BoundaryDiscipline
