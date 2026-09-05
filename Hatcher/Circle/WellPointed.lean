import Hatcher.VanKampen.WellPointedWedgeCover
import Mathlib.Geometry.Manifold.Instances.Sphere

noncomputable section

open Set Topology
open scoped unitInterval

namespace Hatcher

universe u v

/-- An open neighborhood modeled on a real topological vector space is
well-pointed when the chosen point is sent to the origin. -/
theorem WellPointedAt.of_open_homeomorph_zero
    {X : Type u} {E : Type v} [TopologicalSpace X]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E]
    {x₀ : X} {N : Set X} (hx₀ : x₀ ∈ N) (hN : IsOpen N)
    (e : N ≃ₜ E) (he : e ⟨x₀, hx₀⟩ = 0) :
    WellPointedAt x₀ := by
  let x₀N : N := ⟨x₀, hx₀⟩
  have hzero : e.symm 0 = x₀N := by
    rw [← he]
    exact e.toEquiv.symm_apply_apply x₀N
  refine ⟨N, hx₀, hN, ⟨?_⟩⟩
  refine
    { toFun := fun p => e.symm ((1 - (p.1 : ℝ)) • e p.2)
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · fun_prop
  · intro x
    simp
  · intro x
    simp [x₀N, hzero]
  · intro t x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    simp [x₀N, he, hzero]

namespace Circle

/-- The definitional identification of Mathlib's bundled circle with the
metric unit sphere. -/
def toMetricSphere : Circle ≃ₜ Metric.sphere (0 : ℂ) 1 where
  toFun z := ⟨z, z.2⟩
  invFun z := ⟨z, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The standard basepoint of the circle has a strongly contractible open
neighborhood. -/
theorem wellPointedAt_one : WellPointedAt (1 : Circle) := by
  let north : Metric.sphere (0 : ℂ) 1 := ⟨-1, by simp⟩
  let s := stereographic (norm_eq_of_mem_sphere north)
  let chart := toMetricSphere.toOpenPartialHomeomorph.trans s
  have hone : (1 : Circle) ∈ chart.source := by
    simp [chart, s, north, toMetricSphere]
    intro h
    have hval := congrArg Subtype.val h
    norm_num at hval
  have htarget : chart.target = Set.univ := by
    change (toMetricSphere.toOpenPartialHomeomorph.trans s).target = Set.univ
    rw [OpenPartialHomeomorph.trans_target]
    simp [s]
  let e : chart.source ≃ₜ (ℝ ∙ (north : ℂ))ᗮ :=
    chart.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr htarget).trans
        (Homeomorph.Set.univ ((ℝ ∙ (north : ℂ))ᗮ)))
  refine WellPointedAt.of_open_homeomorph_zero hone chart.open_source e ?_
  change s (toMetricSphere (1 : Circle)) = 0
  have honeg : toMetricSphere (1 : Circle) = -north := by
    ext
    simp [north, toMetricSphere]
  rw [honeg]
  exact stereographic_apply_neg north

end Circle

end Hatcher
