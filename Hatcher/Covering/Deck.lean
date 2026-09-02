/-
Compatibility layer for the deck-transformation API added after the project's
pinned Mathlib revision.

The `Homeomorph` instances and `deck` API are adapted from Mathlib PR #40135
by Kim Morrison:
https://github.com/leanprover-community/mathlib4/pull/40135
-/
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Covering.Basic

section Homeomorph

variable {X : Type*} [TopologicalSpace X]

/-- The tautological action by self-homeomorphisms. -/
instance Homeomorph.applyMulAction : MulAction (X ≃ₜ X) X where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
protected theorem Homeomorph.smul_def (f : X ≃ₜ X) (x : X) : f • x = f x := rfl

/-- The tautological self-homeomorphism action is faithful. -/
instance Homeomorph.applyFaithfulSMul : FaithfulSMul (X ≃ₜ X) X := ⟨Homeomorph.ext⟩

/-- The tautological self-homeomorphism action is continuous in the space variable. -/
instance Homeomorph.continuousConstSMul : ContinuousConstSMul (X ≃ₜ X) X :=
  ⟨fun h ↦ h.continuous⟩

end Homeomorph

variable {E X : Type*} [TopologicalSpace E]

/-- The group of self-homeomorphisms of `E` that commute with `p`. -/
def deck (p : E → X) : Subgroup (E ≃ₜ E) where
  carrier := { h | p ∘ h = p }
  one_mem' := rfl
  mul_mem' {f g} hf hg := by ext e; exact (congrFun hf (g e)).trans (congrFun hg e)
  inv_mem' {f} hf := by ext e; simpa using (congrFun hf (f.symm e)).symm

namespace deck

variable {p : E → X}

theorem mem_iff {h : E ≃ₜ E} : h ∈ deck p ↔ p ∘ h = p := Iff.rfl

@[simp]
theorem comp_eq (h : deck p) : p ∘ (h : E ≃ₜ E) = p := h.2

theorem proj_smul (h : deck p) (e : E) : p (h • e) = p e :=
  congrFun h.2 e

instance : ContinuousConstSMul (deck p) E :=
  ⟨fun h ↦ (h : E ≃ₜ E).continuous⟩

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
