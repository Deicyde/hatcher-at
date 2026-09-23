import Hatcher.VanKampen.DiskBoundaryCircle

/-!
# Disk-boundary representatives of fundamental-group elements

Every based loop class is represented by a based map from the boundary of the
standard two-disk. The construction descends a chosen path representative to
`AddCircle 1` and transports it across the standard boundary homeomorphism.
-/

noncomputable section

open Real unitInterval
open scoped ContinuousMap TopCat

namespace Hatcher

universe u

variable {X : Type u} [TopologicalSpace X] {x₀ : X}

private noncomputable def fundamentalGroupPath
    (g : FundamentalGroup X x₀) : Path x₀ x₀ :=
  Quotient.out g.toPath

@[simp] private theorem mk_fundamentalGroupPath
    (g : FundamentalGroup X x₀) :
    (Path.Homotopic.Quotient.mk (fundamentalGroupPath g) :
      Path.Homotopic.Quotient x₀ x₀) = g.toPath :=
  Quotient.out_eq g.toPath

private noncomputable def addCircleMapOfFundamentalGroup
    (g : FundamentalGroup X x₀) : C(AddCircle (1 : ℝ), X) :=
  ⟨AddCircle.liftIco 1 0 (fundamentalGroupPath g).extend,
    AddCircle.liftIco_continuous
      (by simp only [zero_add, Path.extend_zero, Path.extend_one])
      (fundamentalGroupPath g).continuous_extend.continuousOn⟩

private noncomputable def circleMapOfFundamentalGroup
    (g : FundamentalGroup X x₀) : C(_root_.Circle, X) :=
  (addCircleMapOfFundamentalGroup g).comp
    ⟨(AddCircle.homeomorphCircle one_ne_zero).symm,
      (AddCircle.homeomorphCircle one_ne_zero).symm.continuous⟩

/-- A based map from the boundary of the standard two-disk representing the
given fundamental-group element. -/
noncomputable def diskBoundaryMapOfFundamentalGroup
    (g : FundamentalGroup X x₀) :
    C(((TopCat.diskBoundary.{u} 2 : TopCat.{u}) : Type u), X) :=
  (circleMapOfFundamentalGroup g).comp
    ⟨diskBoundaryTwoHomeomorphCircle,
      diskBoundaryTwoHomeomorphCircle.continuous⟩

private theorem homeomorphCircle_symm_expMap (t : ℝ) :
    (AddCircle.homeomorphCircle one_ne_zero).symm (Circle.expMap t) =
      (t : AddCircle (1 : ℝ)) := by
  apply (AddCircle.homeomorphCircle one_ne_zero).injective
  rw [Homeomorph.apply_symm_apply, AddCircle.homeomorphCircle_apply,
    AddCircle.toCircle_apply_mk]
  simp only [Circle.expMap_apply]
  congr 2
  ring

private theorem circleMapOfFundamentalGroup_apply_loop
    (g : FundamentalGroup X x₀) (t : unitInterval) :
    circleMapOfFundamentalGroup g (Circle.loopOfInt 1 t) =
      fundamentalGroupPath g t := by
  change addCircleMapOfFundamentalGroup g
      ((AddCircle.homeomorphCircle one_ne_zero).symm (Circle.loopOfInt 1 t)) = _
  change AddCircle.liftIco 1 0 (fundamentalGroupPath g).extend
      ((AddCircle.homeomorphCircle one_ne_zero).symm (Circle.loopOfInt 1 t)) = _
  have hloop : Circle.loopOfInt 1 t = Circle.expMap t := by
    simp [Circle.loopOfInt]
  rw [hloop]
  change AddCircle.liftIco 1 0 (fundamentalGroupPath g).extend
      ((AddCircle.homeomorphCircle one_ne_zero).symm (Circle.expMap t)) = _
  rw [homeomorphCircle_symm_expMap]
  by_cases ht : (t : ℝ) = 1
  · have ht' : t = (1 : unitInterval) := Subtype.ext ht
    subst t
    have hcircle : ((1 : ℝ) : AddCircle (1 : ℝ)) =
        ((0 : ℝ) : AddCircle (1 : ℝ)) := by
      simpa only [zero_add] using
        (AddCircle.coe_add_period (p := (1 : ℝ)) (0 : ℝ))
    change AddCircle.liftIco 1 0 (fundamentalGroupPath g).extend
      ((1 : ℝ) : AddCircle (1 : ℝ)) = _
    rw [hcircle, AddCircle.liftIco_zero_coe_apply (by norm_num)]
    simp
  · rw [AddCircle.liftIco_zero_coe_apply
        ⟨t.property.1, lt_of_le_of_ne t.property.2 ht⟩,
      (fundamentalGroupPath g).extend_apply t.property]

@[simp] private theorem circleMapOfFundamentalGroup_basepoint
    (g : FundamentalGroup X x₀) :
    circleMapOfFundamentalGroup g 1 = x₀ := by
  change addCircleMapOfFundamentalGroup g
    ((AddCircle.homeomorphCircle one_ne_zero).symm 1) = x₀
  change AddCircle.liftIco 1 0 (fundamentalGroupPath g).extend
    ((AddCircle.homeomorphCircle one_ne_zero).symm 1) = x₀
  rw [← Circle.expMap_zero, homeomorphCircle_symm_expMap]
  rw [AddCircle.liftIco_zero_coe_apply (by norm_num)]
  exact (fundamentalGroupPath g).extend_zero

/-- The chosen disk-boundary representative preserves the standard
basepoint. -/
@[simp] theorem diskBoundaryMapOfFundamentalGroup_basepoint
    (g : FundamentalGroup X x₀) :
    diskBoundaryMapOfFundamentalGroup g diskBoundaryTwoBasepoint.{u} = x₀ := by
  change circleMapOfFundamentalGroup g
    (diskBoundaryTwoHomeomorphCircle.{u} diskBoundaryTwoBasepoint.{u}) = x₀
  rw [diskBoundaryTwoHomeomorphCircle_basepoint.{u}]
  exact circleMapOfFundamentalGroup_basepoint g

/-- The standard positively oriented boundary loop maps to the given
fundamental-group element. -/
theorem diskBoundaryMapOfFundamentalGroup_generator
    (g : FundamentalGroup X x₀) :
    FundamentalGroup.mapOfEq (diskBoundaryMapOfFundamentalGroup g)
      (diskBoundaryMapOfFundamentalGroup_basepoint g)
      (FundamentalGroup.fromPath (.mk diskBoundaryTwoLoop.{u})) = g := by
  rw [FundamentalGroup.mapOfEq_apply]
  change FundamentalGroup.fromPath _ = FundamentalGroup.fromPath g.toPath
  apply congrArg FundamentalGroup.fromPath
  rw [← mk_fundamentalGroupPath g]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  rw [show (((diskBoundaryTwoLoop.{u}.map
      (diskBoundaryMapOfFundamentalGroup g).continuous).cast _ _) t) =
      (diskBoundaryTwoLoop.{u}.map
        (diskBoundaryMapOfFundamentalGroup g).continuous) t from
      congr_fun (Path.cast_coe _ _ _) t]
  change circleMapOfFundamentalGroup g
      (diskBoundaryTwoHomeomorphCircle.{u} (diskBoundaryTwoLoop.{u} t)) =
    fundamentalGroupPath g t
  have hcircle :
      diskBoundaryTwoHomeomorphCircle.{u} (diskBoundaryTwoLoop.{u} t) =
        Circle.loopOfInt 1 t := by
    have h := congrArg
      (fun p : Path (1 : _root_.Circle) 1 ↦ p t)
      diskBoundaryTwoHomeomorphCircle_map_loop.{u}
    simpa only [Path.cast_coe, Path.map_coe, Function.comp_apply] using h
  rw [hcircle]
  exact circleMapOfFundamentalGroup_apply_loop g t

end Hatcher
