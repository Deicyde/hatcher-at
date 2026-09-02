/-
Compatibility layer for the covering-space monodromy action added after the
project's pinned Mathlib revision.

Adapted from Mathlib PR #33108 by Junyan Xu:
https://github.com/leanprover-community/mathlib4/pull/33108
-/
import Mathlib.Topology.Homotopy.Lifting

noncomputable section

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
variable (cov : IsCoveringMap p)

/-- Endpoint transport gives the covering fiber an action of the fundamental
group. -/
@[reducible]
def fundamentalGroupMulAction (x : X) :
    MulAction (FundamentalGroup X x) (p ⁻¹' {x}) where
  smul := cov.monodromy (x := x) (y := x)
  mul_smul _ _ _ := cov.monodromy_trans_apply ..
  one_smul := congr_fun cov.monodromy_refl

/-- The permutation representation induced by monodromy on a covering fiber. -/
def monodromyPerm (x : X) : FundamentalGroup X x →* Equiv.Perm (p ⁻¹' {x}) :=
  letI := cov.fundamentalGroupMulAction x
  MulAction.toPermHom _ _

@[simp]
theorem coe_monodromyPerm {x γ} : cov.monodromyPerm x γ = cov.monodromy γ := rfl

end IsCoveringMap
