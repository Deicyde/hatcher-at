import Mathlib.Topology.Homotopy.Lifting

namespace Hatcher.Covering

open Function

variable {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace A] {p : E → X}

/-- A pointed map from a path-connected, locally path-connected space lifts
through a covering map exactly when its induced fundamental-group image lies
in the covering subgroup. This is Hatcher, Proposition 1.33. -/
theorem exists_lift_iff_range_le (cov : IsCoveringMap p)
    [PathConnectedSpace A] [LocPathConnectedSpace A]
    (f : C(A, X)) (a₀ : A) (e₀ : E) (he : p e₀ = f a₀) :
    (∃ F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f) ↔
      (FundamentalGroup.map f a₀).range ≤
        (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he).range := by
  constructor
  · rintro ⟨F, hF₀, hF⟩
    have hcomp : (⟨p, cov.continuous⟩ : C(E, X)).comp F = f := by
      ext a
      exact congr_fun hF a
    subst f
    subst e₀
    have he_rfl : he = rfl := Subsingleton.elim _ _
    rw [he_rfl]
    rintro _ ⟨γ, rfl⟩
    refine ⟨FundamentalGroup.map F a₀ γ, ?_⟩
    change (CategoryTheory.Iso.refl _).conj
        ((FundamentalGroup.map (⟨p, cov.continuous⟩ : C(E, X)) (F a₀))
          (FundamentalGroup.map F a₀ γ)) =
      FundamentalGroup.map
        ((⟨p, cov.continuous⟩ : C(E, X)).comp F) a₀ γ
    rw [CategoryTheory.Iso.refl_conj]
    change (γ.toPath.map F).map (⟨p, cov.continuous⟩ : C(E, X)) =
      γ.toPath.map ((⟨p, cov.continuous⟩ : C(E, X)).comp F)
    exact Path.Homotopic.Quotient.map_comp.symm
  · intro h
    obtain ⟨F, hF, _⟩ := cov.existsUnique_continuousMap_lifts_of_range_le he h
    exact ⟨F, hF⟩

end Hatcher.Covering
