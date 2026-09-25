/-
Consequences of Mathlib's covering-space monodromy action.
-/
import Mathlib.Topology.Homotopy.Lifting

noncomputable section

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
