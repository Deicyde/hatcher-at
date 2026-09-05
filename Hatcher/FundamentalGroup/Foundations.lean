import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Affine

noncomputable section

open unitInterval

namespace Hatcher

universe u

/-- **Hatcher, Example 1.1 (page 25).** Two paths in a real topological vector
space with the same endpoints are homotopic relative to those endpoints by the
straight-line homotopy. -/
def affinePathHomotopy
    {E : Type u} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [Module ℝ E] [ContinuousSMul ℝ E]
    {x₀ x₁ : E} (p q : Path x₀ x₁) : p.Homotopy q where
  toHomotopy := ContinuousMap.Homotopy.affine p.toContinuousMap q.toContinuousMap
  prop' t x hx := by
    rcases hx with rfl | hx
    · simp
    · rw [Set.mem_singleton_iff] at hx
      subst x
      simp

/-- The fundamental group with multiplication ordered by path concatenation:
`p * q` traverses `p` first and then `q`, as in Hatcher. -/
abbrev PathConcatenationGroup
    (X : Type u) [TopologicalSpace X] (x : X) :=
  (FundamentalGroup X x)ᵐᵒᵖ

namespace PathConcatenationGroup

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Regard a loop-homotopy class as an element of the path-concatenation
version of the fundamental group. -/
def fromPath (p : Path.Homotopic.Quotient x x) :
    PathConcatenationGroup X x :=
  MulOpposite.op (FundamentalGroup.fromPath p)

/-- **Hatcher, Proposition 1.3 (page 26).** In the path-concatenation
convention, multiplication is induced by traversing the left loop and then the
right loop. -/
@[simp]
theorem fromPath_trans (p q : Path.Homotopic.Quotient x x) :
    fromPath (p.trans q) = fromPath p * fromPath q :=
  rfl

end PathConcatenationGroup

end Hatcher
