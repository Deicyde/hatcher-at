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

namespace Hatcher.Covering

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- A loop class lies in the image of the induced map on fundamental groups
exactly when its lift from the chosen point is closed. This is the second
clause of Hatcher, Proposition 1.31. -/
theorem mem_range_map_iff_monodromy_fixed
    (cov : IsCoveringMap p) (e₀ : E) (γ : FundamentalGroup X (p e₀)) :
    γ ∈ (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range ↔
      cov.monodromyPerm (p e₀) γ ⟨e₀, rfl⟩ = ⟨e₀, rfl⟩ := by
  constructor
  · rintro ⟨δ, rfl⟩
    change cov.monodromy (δ.toPath.map ⟨p, cov.continuous⟩) ⟨e₀, rfl⟩ = ⟨e₀, rfl⟩
    exact cov.monodromy_map δ.toPath
  · intro h
    obtain ⟨γ⟩ := γ
    change cov.monodromy ⟦γ⟧ ⟨e₀, rfl⟩ = ⟨e₀, rfl⟩ at h
    have h₁ : cov.liftPath γ e₀ γ.source 1 = e₀ := congrArg Subtype.val h
    let δ : Path e₀ e₀ :=
      ⟨cov.liftPath γ e₀ γ.source, cov.liftPath_zero γ e₀ γ.source, h₁⟩
    refine ⟨⟦δ⟧, ?_⟩
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact congr_fun (cov.liftPath_lifts γ e₀ γ.source) t

end Hatcher.Covering
