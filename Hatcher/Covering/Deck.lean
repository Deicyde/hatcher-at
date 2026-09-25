/-
Project-local extensions to Mathlib's deck-transformation API: the deck action
on a fiber and the normal-cover predicate used below.
-/
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck

variable {E X : Type*} [TopologicalSpace E]

namespace deck

variable {p : E → X}

/-- The deck action restricted to a fiber. -/
@[implicit_reducible] def mulActionFiber (p : E → X) (x : X) :
    MulAction (deck p) (p ⁻¹' {x}) :=
  SubMulAction.mulAction ⟨p ⁻¹' {x}, fun h _ he ↦ (proj_smul h _).trans he⟩

@[simp]
theorem coe_mulActionFiber_smul (p : E → X) (x : X) (h : deck p) (e : p ⁻¹' {x}) :
    letI := mulActionFiber p x
    (↑(h • e) : E) = h • (e : E) :=
  rfl

end deck

namespace Hatcher.Covering

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- A normal covering is surjective and has a transitive deck action on every fiber. -/
structure IsNormal (p : E → X) : Prop where
  isCoveringMap : IsCoveringMap p
  surjective : Function.Surjective p
  isPretransitive (x : X) :
    letI := deck.mulActionFiber p x
    MulAction.IsPretransitive (deck p) (p ⁻¹' {x})

end Hatcher.Covering
