import Hatcher.Covering.Monodromy
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.SetTheory.Cardinal.Defs

noncomputable section

open unitInterval

namespace Hatcher.Covering

universe u v

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- The fiber of a path-connected covering is equivalent to the quotient of
the fundamental group by the image of the induced map. This is Hatcher,
Proposition 1.32. -/
noncomputable def fiberEquivQuotientRange (cov : IsCoveringMap p)
    [PathConnectedSpace E] [PathConnectedSpace X] (e₀ : E) :
    p ⁻¹' {p e₀} ≃
      FundamentalGroup X (p e₀) ⧸
        (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range := by
  letI := cov.fundamentalGroupMulAction (p e₀)
  let base : p ⁻¹' {p e₀} := ⟨e₀, rfl⟩
  have htrans : MulAction.IsPretransitive
      (FundamentalGroup X (p e₀)) (p ⁻¹' {p e₀}) := by
    rw [MulAction.isPretransitive_iff_base base]
    intro e
    rcases e with ⟨e, he⟩
    change p e = p e₀ at he
    let η : Path e₀ e := PathConnectedSpace.somePath e₀ e
    let γ : Path (p e₀) (p e₀) :=
      (η.map cov.continuous).cast rfl he.symm
    have hη : (η : C(I, E)) = cov.liftPath γ e₀ γ.source := by
      apply (cov.eq_liftPath_iff' γ.source).2
      constructor
      · rfl
      · exact η.source
    refine ⟨FundamentalGroup.fromPath (.mk γ), ?_⟩
    apply Subtype.ext
    change cov.liftPath γ e₀ γ.source 1 = e
    rw [← hη]
    exact η.target
  letI := htrans
  have hstab : MulAction.stabilizer (FundamentalGroup X (p e₀)) base =
      (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range := by
    ext γ
    rw [MulAction.mem_stabilizer_iff]
    exact (mem_range_map_iff_monodromy_fixed cov e₀ γ).symm
  exact ((Equiv.Set.univ (p ⁻¹' {p e₀})).symm.trans
      (Equiv.setCongr (MulAction.orbit_eq_univ (FundamentalGroup X (p e₀)) base).symm)).trans
    ((MulAction.orbitEquivQuotientStabilizer (FundamentalGroup X (p e₀)) base).trans
      (Subgroup.quotientEquivOfEq hstab))

/-- Cardinal-valued form of `fiberEquivQuotientRange`, valid without a
finite-sheeted hypothesis. -/
theorem mk_fiber_eq_mk_quotientRange (cov : IsCoveringMap p)
    [PathConnectedSpace E] [PathConnectedSpace X] (e₀ : E) :
    Cardinal.lift.{v} (Cardinal.mk (p ⁻¹' {p e₀})) =
      Cardinal.lift.{u} (Cardinal.mk
        (FundamentalGroup X (p e₀) ⧸
          (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range)) :=
  Cardinal.mk_congr_lift (fiberEquivQuotientRange cov e₀)

end Hatcher.Covering
