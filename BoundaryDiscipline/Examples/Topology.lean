import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import BoundaryDiscipline.Topological
import BoundaryDiscipline.Contracts.Separation

namespace BoundaryDiscipline.Examples

open Set
open BoundaryDiscipline

/-
A small, concrete topological example on ℝ.
We choose two *closed* regions whose closures are trivially themselves,
and whose closures are disjoint. Then the discipline contract gives that
their boundaries (frontiers) are disjoint.

This file is deliberately "boring but legible": it demonstrates that the
abstract discipline statements are not empty, and it compiles without
needing delicate interval-closure lemmas.
-/

namespace RealExample

/-- Two closed regions in ℝ. -/
def A : Set ℝ := Iic (0 : ℝ) -- {x | x ≤ 0}
def B : Set ℝ := Ici (1 : ℝ) -- {x | 1 ≤ x}

/-- A and B are disjoint (obvious order separation). -/
theorem A_disjoint_B : Disjoint A B := by
  refine Set.disjoint_left.2 ?_
  intro x hxA hxB
  -- hxA : x ≤ 0, hxB : 1 ≤ x, impossible
  have : (1 : ℝ) ≤ (0 : ℝ) := by
    -- 1 ≤ x ≤ 0
    exact le_trans hxB hxA
  linarith

/-- Closures of A and B are disjoint. Since A and B are closed, closure = itself. -/
theorem closureA_disjoint_closureB : Disjoint (closure A) (closure B) := by
  -- Use the fact that Iic and Ici are closed in ℝ.
  have hAclosed : IsClosed A := by
    simpa [A] using (isClosed_Iic : IsClosed (Iic (0 : ℝ)))
  have hBclosed : IsClosed B := by
    simpa [B] using (isClosed_Ici : IsClosed (Ici (1 : ℝ)))
  -- Replace closures by the sets themselves.
  -- Then reuse the disjointness proof.
  simpa [hAclosed.closure_eq, hBclosed.closure_eq] using A_disjoint_B

/--
Discipline consequence: boundaries (frontiers) are disjoint under closure-level separation.
-/
theorem frontierA_disjoint_frontierB : Disjoint (frontier A) (frontier B) := by
  -- Apply the contract theorem from Contracts/Separation.lean
  exact frontier_disjoint_of_closure_disjoint (α := ℝ) A B closureA_disjoint_closureB

/--
Same statement, expressed through `topoBoundaryOp` (the BoundaryOp packaging of `frontier`).
-/
theorem topoBoundaryOpA_disjoint_topoBoundaryOpB :
    Disjoint ((topoBoundaryOp ℝ) A) ((topoBoundaryOp ℝ) B) := by
  -- `topoBoundaryOp` is definitionally `frontier` packaged.
  simpa [topoBoundaryOp] using frontierA_disjoint_frontierB

end RealExample

end BoundaryDiscipline.Examples
