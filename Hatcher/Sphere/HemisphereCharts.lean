import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Category.TopCat.ULift

/-!
# Stereographic models for hemispheres

This file keeps `TopCat.sphere` as the public sphere model.  Point-set
calculations pass through `sphereULiftHomeomorph`, the single explicit bridge
to Mathlib's underlying unit metric sphere.
-/

open Metric Set
open scoped EuclideanSpace RealInnerProductSpace

namespace Hatcher.Sphere

universe u

/-- The raw metric model underlying `TopCat.sphere n`.  This name is used only
to state the single `ULift` bridge and the geometry behind it. -/
abbrev RawSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The single explicit bridge from Mathlib's public `TopCat.sphere` to its
underlying unit metric sphere. -/
noncomputable def sphereULiftHomeomorph (n : ℕ) :
    ((TopCat.sphere.{u} n : TopCat.{u}) : Type u) ≃ₜ RawSphere n :=
  Homeomorph.ulift

/-- The last standard basis vector in the ambient space of `S^(n+1)`. -/
noncomputable def lastVector (n : ℕ) : EuclideanSpace ℝ (Fin (n + 2)) :=
  EuclideanSpace.single (Fin.last (n + 1)) 1

private noncomputable def rawNorthPole (n : ℕ) : RawSphere (n + 1) :=
  ⟨lastVector n, by simp [lastVector]⟩

private noncomputable def rawSouthPole (n : ℕ) : RawSphere (n + 1) :=
  -rawNorthPole n

/-- The north pole `e_last` of `TopCat.sphere (n+1)`. -/
noncomputable def northPole (n : ℕ) :
    ((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u) :=
  (sphereULiftHomeomorph (n + 1)).symm (rawNorthPole n)

/-- The south pole `-e_last` of `TopCat.sphere (n+1)`. -/
noncomputable def southPole (n : ℕ) :
    ((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u) :=
  (sphereULiftHomeomorph (n + 1)).symm (rawSouthPole n)

private def rawNorthHemisphere (n : ℕ) : Set (RawSphere (n + 1)) :=
  {x | 0 ≤ (x.1 : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))}

private def rawSouthHemisphere (n : ℕ) : Set (RawSphere (n + 1)) :=
  {x | (x.1 : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) ≤ 0}

private def rawEquator (n : ℕ) : Set (RawSphere (n + 1)) :=
  {x | (x.1 : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) = 0}

/-- The literal closed northern hemisphere, defined by a nonnegative last
coordinate. -/
noncomputable def northHemisphere (n : ℕ) :
    Set (((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u)) :=
  sphereULiftHomeomorph (n + 1) ⁻¹' rawNorthHemisphere n

/-- The literal closed southern hemisphere, defined by a nonpositive last
coordinate. -/
noncomputable def southHemisphere (n : ℕ) :
    Set (((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u)) :=
  sphereULiftHomeomorph (n + 1) ⁻¹' rawSouthHemisphere n

/-- The equator, defined by vanishing of the last coordinate. -/
noncomputable def equator (n : ℕ) :
    Set (((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u)) :=
  sphereULiftHomeomorph (n + 1) ⁻¹' rawEquator n

/-- The neighborhood of the northern hemisphere obtained by deleting the
south pole. -/
noncomputable def northNeighborhood (n : ℕ) :
    Set (((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u)) :=
  sphereULiftHomeomorph (n + 1) ⁻¹' ({rawSouthPole n}ᶜ : Set (RawSphere (n + 1)))

/-- The neighborhood of the southern hemisphere obtained by deleting the
north pole. -/
noncomputable def southNeighborhood (n : ℕ) :
    Set (((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u)) :=
  sphereULiftHomeomorph (n + 1) ⁻¹' ({rawNorthPole n}ᶜ : Set (RawSphere (n + 1)))

theorem northNeighborhood_eq_compl_southPole (n : ℕ) :
    northNeighborhood n = ({southPole n}ᶜ : Set _) := by
  ext x
  simp only [northNeighborhood, mem_preimage, mem_compl_iff, mem_singleton_iff]
  constructor
  · intro h hx
    apply h
    simpa [southPole] using congrArg (sphereULiftHomeomorph (n + 1)) hx
  · intro h hx
    apply h
    apply (sphereULiftHomeomorph (n + 1)).injective
    simpa [southPole] using hx

theorem southNeighborhood_eq_compl_northPole (n : ℕ) :
    southNeighborhood n = ({northPole n}ᶜ : Set _) := by
  ext x
  simp only [southNeighborhood, mem_preimage, mem_compl_iff, mem_singleton_iff]
  constructor
  · intro h hx
    apply h
    simpa [northPole] using congrArg (sphereULiftHomeomorph (n + 1)) hx
  · intro h hx
    apply h
    apply (sphereULiftHomeomorph (n + 1)).injective
    simpa [northPole] using hx

@[simp]
theorem mem_northHemisphere (n : ℕ)
    (x : ((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u)) :
    x ∈ northHemisphere n ↔
      0 ≤ (((sphereULiftHomeomorph (n + 1)) x : RawSphere (n + 1)).1 :
        EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) :=
  Iff.rfl

@[simp]
theorem mem_southHemisphere (n : ℕ)
    (x : ((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u)) :
    x ∈ southHemisphere n ↔
      (((sphereULiftHomeomorph (n + 1)) x : RawSphere (n + 1)).1 :
        EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) ≤ 0 :=
  Iff.rfl

@[simp]
theorem mem_equator (n : ℕ)
    (x : ((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u)) :
    x ∈ equator n ↔
      (((sphereULiftHomeomorph (n + 1)) x : RawSphere (n + 1)).1 :
        EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) = 0 :=
  Iff.rfl

theorem hemisphere_union (n : ℕ) :
    northHemisphere n ∪ southHemisphere n = Set.univ := by
  ext x
  simp only [northHemisphere, southHemisphere, rawNorthHemisphere,
    rawSouthHemisphere, mem_union, mem_preimage, mem_ofPred_eq, mem_univ,
    iff_true]
  exact le_total 0 _

theorem hemisphere_intersection (n : ℕ) :
    northHemisphere n ∩ southHemisphere n = equator n := by
  ext x
  simp only [northHemisphere, southHemisphere, equator, rawNorthHemisphere,
    rawSouthHemisphere, rawEquator, mem_inter_iff, mem_preimage, mem_ofPred_eq]
  exact ⟨fun h ↦ le_antisymm h.2 h.1, fun h ↦ ⟨h.ge, h.le⟩⟩

private noncomputable def rawStereographicChart (n : ℕ) (v : RawSphere (n + 1)) :
    ({v}ᶜ : Set (RawSphere (n + 1))) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)) := by
  let e := stereographic' (n + 1) v
  exact
    (Homeomorph.setCongr (stereographic'_source v).symm).trans
      (e.toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr (stereographic'_target v)).trans
          (Homeomorph.Set.univ _)))

@[simp]
private theorem rawStereographicChart_apply (n : ℕ) (v : RawSphere (n + 1))
    (x : ({v}ᶜ : Set (RawSphere (n + 1)))) :
    rawStereographicChart n v x = stereographic' (n + 1) v x.1 :=
  rfl

@[simp]
private theorem rawStereographicChart_symm_apply_coe (n : ℕ) (v : RawSphere (n + 1))
    (y : EuclideanSpace ℝ (Fin (n + 1))) :
    ((rawStereographicChart n v).symm y : RawSphere (n + 1)) =
      (stereographic' (n + 1) v).symm y :=
  rfl

private theorem inner_stereographic'_symm (n : ℕ) (v : RawSphere (n + 1))
    (y : EuclideanSpace ℝ (Fin (n + 1))) :
    inner ℝ (v : EuclideanSpace ℝ (Fin (n + 2)))
        ((stereographic' (n + 1) v).symm y : EuclideanSpace ℝ (Fin (n + 2))) =
      (‖y‖ ^ 2 - 4) / (‖y‖ ^ 2 + 4) := by
  rw [stereographic'_symm_apply]
  let U :
      (ℝ ∙ (v : EuclideanSpace ℝ (Fin (n + 2))))ᗮ ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (n + 1)
      (ne_zero_of_mem_unit_sphere v)).repr
  have hw :
      inner ℝ (v : EuclideanSpace ℝ (Fin (n + 2)))
        ((U.symm y : (ℝ ∙ (v : EuclideanSpace ℝ (Fin (n + 2))))ᗮ) :
          EuclideanSpace ℝ (Fin (n + 2))) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (U.symm y).2
  have hv :
      inner ℝ (v : EuclideanSpace ℝ (Fin (n + 2)))
        (v : EuclideanSpace ℝ (Fin (n + 2))) = 1 := by
    rw [real_inner_self_eq_norm_sq]
    simp [norm_eq_of_mem_sphere]
  have hnorm :
      ‖((U.symm y : (ℝ ∙ (v : EuclideanSpace ℝ (Fin (n + 2))))ᗮ) :
        EuclideanSpace ℝ (Fin (n + 2)))‖ = ‖y‖ :=
    U.symm.norm_map y
  simp only [inner_add_right, inner_smul_right]
  rw [hw, hv, hnorm]
  simp [div_eq_mul_inv, mul_comm]

private theorem inner_rawStereographicChart (n : ℕ) (v : RawSphere (n + 1))
    (x : ({v}ᶜ : Set (RawSphere (n + 1)))) :
    inner ℝ (v : EuclideanSpace ℝ (Fin (n + 2)))
        (x.1 : EuclideanSpace ℝ (Fin (n + 2))) =
      (‖rawStereographicChart n v x‖ ^ 2 - 4) /
        (‖rawStereographicChart n v x‖ ^ 2 + 4) := by
  have h := inner_stereographic'_symm n v (rawStereographicChart n v x)
  rw [← rawStereographicChart_symm_apply_coe] at h
  simpa using h

private theorem rawNorthHemisphere_chart_iff (n : ℕ)
    (x : ({rawSouthPole n}ᶜ : Set (RawSphere (n + 1)))) :
    x.1 ∈ rawNorthHemisphere n ↔
      rawStereographicChart n (rawSouthPole n) x ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 2 := by
  let y := rawStereographicChart n (rawSouthPole n) x
  have hinner := inner_rawStereographicChart n (rawSouthPole n) x
  have hleft :
      inner ℝ (rawSouthPole n : EuclideanSpace ℝ (Fin (n + 2)))
          (x.1 : EuclideanSpace ℝ (Fin (n + 2))) =
        -((x.1.1 : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) := by
    simp [rawSouthPole, rawNorthPole, lastVector,
      EuclideanSpace.inner_single_left]
  have hcoord :
      -((x.1.1 : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) =
        (‖y‖ ^ 2 - 4) / (‖y‖ ^ 2 + 4) := by
    rw [hleft] at hinner
    simpa only [y] using hinner
  have hden : 0 < ‖y‖ ^ 2 + (4 : ℝ) := by positivity
  have hmul :
      -((x.1.1 : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) *
          (‖y‖ ^ 2 + 4) = ‖y‖ ^ 2 - 4 :=
    (eq_div_iff hden.ne').mp hcoord
  simp only [rawNorthHemisphere, mem_ofPred_eq, mem_closedBall, dist_zero_right]
  constructor
  · intro hx
    have hy_sq : ‖y‖ ^ 2 ≤ 4 := by nlinarith
    nlinarith [norm_nonneg y, sq_nonneg (‖y‖ - 2)]
  · intro hy
    have hy_sq : ‖y‖ ^ 2 ≤ 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hy)
        (by positivity : 0 ≤ 2 + ‖y‖)]
    nlinarith

private theorem rawSouthHemisphere_chart_iff (n : ℕ)
    (x : ({rawNorthPole n}ᶜ : Set (RawSphere (n + 1)))) :
    x.1 ∈ rawSouthHemisphere n ↔
      rawStereographicChart n (rawNorthPole n) x ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 2 := by
  let y := rawStereographicChart n (rawNorthPole n) x
  have hinner := inner_rawStereographicChart n (rawNorthPole n) x
  have hleft :
      inner ℝ (rawNorthPole n : EuclideanSpace ℝ (Fin (n + 2)))
          (x.1 : EuclideanSpace ℝ (Fin (n + 2))) =
        ((x.1.1 : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) := by
    simp [rawNorthPole, lastVector, EuclideanSpace.inner_single_left]
  have hcoord :
      ((x.1.1 : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) =
        (‖y‖ ^ 2 - 4) / (‖y‖ ^ 2 + 4) := by
    rw [hleft] at hinner
    simpa only [y] using hinner
  have hden : 0 < ‖y‖ ^ 2 + (4 : ℝ) := by positivity
  have hmul :
      ((x.1.1 : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) *
          (‖y‖ ^ 2 + 4) = ‖y‖ ^ 2 - 4 :=
    (eq_div_iff hden.ne').mp hcoord
  simp only [rawSouthHemisphere, mem_ofPred_eq, mem_closedBall, dist_zero_right]
  constructor
  · intro hx
    have hy_sq : ‖y‖ ^ 2 ≤ 4 := by nlinarith
    nlinarith [norm_nonneg y, sq_nonneg (‖y‖ - 2)]
  · intro hy
    have hy_sq : ‖y‖ ^ 2 ≤ 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hy)
        (by positivity : 0 ≤ 2 + ‖y‖)]
    nlinarith

private theorem rawEquator_chart_iff (n : ℕ)
    (x : ({rawSouthPole n}ᶜ : Set (RawSphere (n + 1)))) :
    x.1 ∈ rawEquator n ↔
      rawStereographicChart n (rawSouthPole n) x ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 2 := by
  let y := rawStereographicChart n (rawSouthPole n) x
  have hinner := inner_rawStereographicChart n (rawSouthPole n) x
  have hleft :
      inner ℝ (rawSouthPole n : EuclideanSpace ℝ (Fin (n + 2)))
          (x.1 : EuclideanSpace ℝ (Fin (n + 2))) =
        -((x.1.1 : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) := by
    simp [rawSouthPole, rawNorthPole, lastVector,
      EuclideanSpace.inner_single_left]
  have hcoord :
      -((x.1.1 : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) =
        (‖y‖ ^ 2 - 4) / (‖y‖ ^ 2 + 4) := by
    rw [hleft] at hinner
    simpa only [y] using hinner
  have hden : 0 < ‖y‖ ^ 2 + (4 : ℝ) := by positivity
  have hmul :
      -((x.1.1 : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) *
          (‖y‖ ^ 2 + 4) = ‖y‖ ^ 2 - 4 :=
    (eq_div_iff hden.ne').mp hcoord
  simp only [rawEquator, mem_ofPred_eq, mem_sphere, dist_zero_right]
  constructor
  · intro hx
    have hy_sq : ‖y‖ ^ 2 = 4 := by nlinarith
    nlinarith [norm_nonneg y, sq_nonneg (‖y‖ - 2)]
  · intro hy
    nlinarith

private def nestedSubtypeHomeomorph {X : Type*} [TopologicalSpace X]
    {s t : Set X} (h : s ⊆ t) :
    s ≃ₜ {x : t // x.1 ∈ s} where
  toFun x := ⟨⟨x.1, h x.2⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem rawNorthHemisphere_subset_northNeighborhood (n : ℕ) :
    rawNorthHemisphere n ⊆ ({rawSouthPole n}ᶜ : Set (RawSphere (n + 1))) := by
  intro x hx
  simp only [mem_compl_iff, mem_singleton_iff]
  intro h
  subst x
  norm_num [rawNorthHemisphere, rawSouthPole, rawNorthPole, lastVector,
    PiLp.single_apply] at hx

private theorem rawSouthHemisphere_subset_southNeighborhood (n : ℕ) :
    rawSouthHemisphere n ⊆ ({rawNorthPole n}ᶜ : Set (RawSphere (n + 1))) := by
  intro x hx
  simp only [mem_compl_iff, mem_singleton_iff]
  intro h
  subst x
  norm_num [rawSouthHemisphere, rawNorthPole, lastVector, PiLp.single_apply] at hx

private theorem rawEquator_subset_northNeighborhood (n : ℕ) :
    rawEquator n ⊆ ({rawSouthPole n}ᶜ : Set (RawSphere (n + 1))) := by
  intro x hx
  simp only [mem_compl_iff, mem_singleton_iff]
  intro h
  subst x
  norm_num [rawEquator, rawSouthPole, rawNorthPole, lastVector,
    PiLp.single_apply] at hx

private theorem rawEquator_subset_southNeighborhood (n : ℕ) :
    rawEquator n ⊆ ({rawNorthPole n}ᶜ : Set (RawSphere (n + 1))) := by
  intro x hx
  simp only [mem_compl_iff, mem_singleton_iff]
  intro h
  subst x
  norm_num [rawEquator, rawNorthPole, lastVector, PiLp.single_apply] at hx

private noncomputable def northNeighborhoodRawHomeomorph (n : ℕ) :
    northNeighborhood n ≃ₜ
      ({rawSouthPole n}ᶜ : Set (RawSphere (n + 1))) :=
  (sphereULiftHomeomorph (n + 1)).subtype fun _ ↦ Iff.rfl

private noncomputable def southNeighborhoodRawHomeomorph (n : ℕ) :
    southNeighborhood n ≃ₜ
      ({rawNorthPole n}ᶜ : Set (RawSphere (n + 1))) :=
  (sphereULiftHomeomorph (n + 1)).subtype fun _ ↦ Iff.rfl

private noncomputable def northHemisphereRawHomeomorph (n : ℕ) :
    northHemisphere n ≃ₜ rawNorthHemisphere n :=
  (sphereULiftHomeomorph (n + 1)).subtype fun _ ↦ Iff.rfl

private noncomputable def southHemisphereRawHomeomorph (n : ℕ) :
    southHemisphere n ≃ₜ rawSouthHemisphere n :=
  (sphereULiftHomeomorph (n + 1)).subtype fun _ ↦ Iff.rfl

private noncomputable def equatorRawHomeomorph (n : ℕ) :
    equator n ≃ₜ rawEquator n :=
  (sphereULiftHomeomorph (n + 1)).subtype fun _ ↦ Iff.rfl

/-- Stereographic projection from the deleted south pole identifies the
northern neighborhood with Euclidean `(n+1)`-space. -/
noncomputable def northStereographicHomeomorph (n : ℕ) :
    northNeighborhood n ≃ₜ EuclideanSpace ℝ (Fin (n + 1)) :=
  (northNeighborhoodRawHomeomorph n).trans
    (rawStereographicChart n (rawSouthPole n))

/-- Stereographic projection from the deleted north pole identifies the
southern neighborhood with Euclidean `(n+1)`-space. -/
noncomputable def southStereographicHomeomorph (n : ℕ) :
    southNeighborhood n ≃ₜ EuclideanSpace ℝ (Fin (n + 1)) :=
  (southNeighborhoodRawHomeomorph n).trans
    (rawStereographicChart n (rawNorthPole n))

private noncomputable def rawNorthHemisphereHomeomorph (n : ℕ) :
    rawNorthHemisphere n ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 2 :=
  (nestedSubtypeHomeomorph (rawNorthHemisphere_subset_northNeighborhood n)).trans
    ((rawStereographicChart n (rawSouthPole n)).subtype
      (rawNorthHemisphere_chart_iff n))

private noncomputable def rawSouthHemisphereHomeomorph (n : ℕ) :
    rawSouthHemisphere n ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 2 :=
  (nestedSubtypeHomeomorph (rawSouthHemisphere_subset_southNeighborhood n)).trans
    ((rawStereographicChart n (rawNorthPole n)).subtype
      (rawSouthHemisphere_chart_iff n))

/-- The deleted-south-pole stereographic chart identifies the closed northern
hemisphere with the radius-two closed ball. -/
noncomputable def northHemisphereHomeomorph (n : ℕ) :
    northHemisphere n ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 2 :=
  (northHemisphereRawHomeomorph n).trans
    (rawNorthHemisphereHomeomorph n)

/-- The deleted-north-pole stereographic chart identifies the closed southern
hemisphere with the radius-two closed ball. -/
noncomputable def southHemisphereHomeomorph (n : ℕ) :
    southHemisphere n ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 2 :=
  (southHemisphereRawHomeomorph n).trans
    (rawSouthHemisphereHomeomorph n)

theorem northHemisphere_subset_northNeighborhood (n : ℕ) :
    northHemisphere n ⊆ northNeighborhood n := by
  intro x hx
  exact rawNorthHemisphere_subset_northNeighborhood n hx

theorem southHemisphere_subset_southNeighborhood (n : ℕ) :
    southHemisphere n ⊆ southNeighborhood n := by
  intro x hx
  exact rawSouthHemisphere_subset_southNeighborhood n hx

theorem equator_subset_northNeighborhood (n : ℕ) :
    equator n ⊆ northNeighborhood n := by
  intro x hx
  exact rawEquator_subset_northNeighborhood n hx

theorem equator_subset_southNeighborhood (n : ℕ) :
    equator n ⊆ southNeighborhood n := by
  intro x hx
  exact rawEquator_subset_southNeighborhood n hx

theorem northHemisphere_inclusion_square (n : ℕ)
    (x : northHemisphere n) :
    northStereographicHomeomorph n
        ⟨x.1, northHemisphere_subset_northNeighborhood n x.2⟩ =
      (northHemisphereHomeomorph n x).1 :=
  rfl

theorem southHemisphere_inclusion_square (n : ℕ)
    (x : southHemisphere n) :
    southStereographicHomeomorph n
        ⟨x.1, southHemisphere_subset_southNeighborhood n x.2⟩ =
      (southHemisphereHomeomorph n x).1 :=
  rfl

private noncomputable def rawNorthPoleInNorthNeighborhood (n : ℕ) :
    ({rawSouthPole n}ᶜ : Set (RawSphere (n + 1))) :=
  ⟨rawNorthPole n, by
    simpa [rawSouthPole] using ne_neg_of_mem_unit_sphere ℝ (rawNorthPole n)⟩

@[simp]
private theorem rawNorthChart_northPole (n : ℕ) :
    rawStereographicChart n (rawSouthPole n)
        (rawNorthPoleInNorthNeighborhood n) = 0 := by
  rw [rawStereographicChart_apply]
  change (stereographic' (n + 1) (rawSouthPole n)) (rawNorthPole n) = 0
  have hneg : rawNorthPole n = -(rawSouthPole n) := by simp [rawSouthPole]
  rw [hneg]
  simp [stereographic']

private theorem rawNorthChart_ne_zero_iff (n : ℕ)
    (x : ({rawSouthPole n}ᶜ : Set (RawSphere (n + 1)))) :
    x.1 ∈ ({rawNorthPole n}ᶜ : Set (RawSphere (n + 1))) ↔
      rawStereographicChart n (rawSouthPole n) x ∈
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  simp only [mem_compl_iff, mem_singleton_iff]
  apply not_congr
  constructor
  · intro h
    have hx : x = rawNorthPoleInNorthNeighborhood n := Subtype.ext h
    rw [hx]
    exact rawNorthChart_northPole n
  · intro h
    have hx := congrArg Subtype.val
      ((rawStereographicChart n (rawSouthPole n)).injective
        (h.trans (rawNorthChart_northPole n).symm))
    exact hx

private def rawOverlap (n : ℕ) : Set (RawSphere (n + 1)) :=
  ({rawSouthPole n}ᶜ : Set _) ∩ ({rawNorthPole n}ᶜ : Set _)

/-- The overlap of the two opposite-pole neighborhoods. -/
noncomputable def neighborhoodOverlap (n : ℕ) :
    Set (((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u)) :=
  northNeighborhood n ∩ southNeighborhood n

private noncomputable def overlapRawHomeomorph (n : ℕ) :
    neighborhoodOverlap n ≃ₜ rawOverlap n :=
  (sphereULiftHomeomorph (n + 1)).subtype fun _ ↦ Iff.rfl

private noncomputable def rawOverlapHomeomorph (n : ℕ) :
    rawOverlap n ≃ₜ
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  (nestedSubtypeHomeomorph (inter_subset_left : rawOverlap n ⊆ _)).trans
    ((rawStereographicChart n (rawSouthPole n)).subtype
      (fun x ↦ by
        simpa only [mem_inter_iff, and_iff_right x.2] using
          rawNorthChart_ne_zero_iff n x))

/-- The deleted-south-pole chart identifies the overlap with punctured
Euclidean space. -/
noncomputable def overlapStereographicHomeomorph (n : ℕ) :
    neighborhoodOverlap n ≃ₜ
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  (overlapRawHomeomorph n).trans (rawOverlapHomeomorph n)

private noncomputable def rawEquatorHomeomorph (n : ℕ) :
    rawEquator n ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 2 :=
  (nestedSubtypeHomeomorph (rawEquator_subset_northNeighborhood n)).trans
    ((rawStereographicChart n (rawSouthPole n)).subtype
      (rawEquator_chart_iff n))

/-- The deleted-south-pole chart identifies the equator with the radius-two
sphere in Euclidean `(n+1)`-space. -/
noncomputable def equatorStereographicHomeomorph (n : ℕ) :
    equator n ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 2 :=
  (equatorRawHomeomorph n).trans (rawEquatorHomeomorph n)

private noncomputable def radiusTwoSphereHomeomorphRawSphere (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 2 ≃ₜ RawSphere n :=
  (Homeomorph.smulOfNeZero (α := EuclideanSpace ℝ (Fin (n + 1)))
      ((2 : ℝ)⁻¹) (by norm_num)).subtype fun x ↦ by
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm]
    change ‖x‖ = 2 ↔ ‖((2 : ℝ)⁻¹) • x‖ = 1
    rw [norm_smul]
    norm_num
    constructor <;> intro h <;> nlinarith

/-- Scaling the radius-two equatorial sphere to radius one and applying the
same `ULift` bridge identifies the equator with `TopCat.sphere n`. -/
noncomputable def equatorSphereHomeomorph (n : ℕ) :
    equator n ≃ₜ
      ((TopCat.sphere.{u} n : TopCat.{u}) : Type u) :=
  (equatorStereographicHomeomorph n).trans
    ((radiusTwoSphereHomeomorphRawSphere n).trans
      (sphereULiftHomeomorph n).symm)

theorem equator_subset_overlap (n : ℕ) :
    equator n ⊆ neighborhoodOverlap n :=
  fun _ hx ↦ ⟨equator_subset_northNeighborhood n hx,
    equator_subset_southNeighborhood n hx⟩

theorem isOpen_northNeighborhood (n : ℕ) :
    IsOpen (northNeighborhood n) := by
  exact (isOpen_compl_singleton :
      IsOpen ({rawSouthPole n}ᶜ : Set (RawSphere (n + 1)))).preimage
    (sphereULiftHomeomorph (n + 1)).continuous

theorem isOpen_southNeighborhood (n : ℕ) :
    IsOpen (southNeighborhood n) := by
  exact (isOpen_compl_singleton :
      IsOpen ({rawNorthPole n}ᶜ : Set (RawSphere (n + 1)))).preimage
    (sphereULiftHomeomorph (n + 1)).continuous

theorem northHemisphere_subset_interior_northNeighborhood (n : ℕ) :
    northHemisphere n ⊆ interior (northNeighborhood n) := by
  rw [(isOpen_northNeighborhood n).interior_eq]
  exact northHemisphere_subset_northNeighborhood n

theorem southHemisphere_subset_interior_southNeighborhood (n : ℕ) :
    southHemisphere n ⊆ interior (southNeighborhood n) := by
  rw [(isOpen_southNeighborhood n).interior_eq]
  exact southHemisphere_subset_southNeighborhood n

/-- The canonical inclusion of the radius-two sphere into punctured
Euclidean space. -/
def radiusTwoSphereInPunctured (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 2) :
    ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  ⟨x.1, by
    intro hzero
    have hnorm := x.2
    rw [mem_sphere_zero_iff_norm, hzero] at hnorm
    norm_num at hnorm⟩

theorem continuous_radiusTwoSphereInPunctured (n : ℕ) :
    Continuous (radiusTwoSphereInPunctured n) := by
  exact continuous_subtype_val.subtype_mk _

theorem equator_inclusion_square (n : ℕ) (x : equator n) :
    overlapStereographicHomeomorph n
        ⟨x.1, equator_subset_overlap n x.2⟩ =
      radiusTwoSphereInPunctured n
        (equatorStereographicHomeomorph n x) :=
  rfl

/-- The point-set and chart data for Hatcher's literal north/south hemisphere
decomposition of `TopCat.sphere (n+1)`.  The three square fields say that the
hemisphere and equator charts commute with the canonical subtype inclusions;
these are the equalities used to transport radial strong deformation
retractions in the subsequent neighborhood-cover construction. -/
structure HemisphereChartData (n : ℕ) where
  northHemisphere : Set (((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u))
  southHemisphere : Set (((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u))
  equator : Set (((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u))
  northPole : ((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u)
  southPole : ((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u)
  northNeighborhood : Set (((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u))
  southNeighborhood : Set (((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u))
  northNeighborhood_eq : northNeighborhood = ({southPole}ᶜ : Set _)
  southNeighborhood_eq : southNeighborhood = ({northPole}ᶜ : Set _)
  northHemisphere_spec : ∀ x, x ∈ northHemisphere ↔
    0 ≤ (((sphereULiftHomeomorph (n + 1)) x : RawSphere (n + 1)).1 :
      EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))
  southHemisphere_spec : ∀ x, x ∈ southHemisphere ↔
    (((sphereULiftHomeomorph (n + 1)) x : RawSphere (n + 1)).1 :
      EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) ≤ 0
  equator_spec : ∀ x, x ∈ equator ↔
    (((sphereULiftHomeomorph (n + 1)) x : RawSphere (n + 1)).1 :
      EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) = 0
  cover : northHemisphere ∪ southHemisphere = Set.univ
  intersection : northHemisphere ∩ southHemisphere = equator
  northOpen : IsOpen northNeighborhood
  southOpen : IsOpen southNeighborhood
  northSubset : northHemisphere ⊆ northNeighborhood
  southSubset : southHemisphere ⊆ southNeighborhood
  northInteriorSubset : northHemisphere ⊆ interior northNeighborhood
  southInteriorSubset : southHemisphere ⊆ interior southNeighborhood
  equatorNorthSubset : equator ⊆ northNeighborhood
  equatorSouthSubset : equator ⊆ southNeighborhood
  northChart : northNeighborhood ≃ₜ EuclideanSpace ℝ (Fin (n + 1))
  southChart : southNeighborhood ≃ₜ EuclideanSpace ℝ (Fin (n + 1))
  northHemisphereChart : northHemisphere ≃ₜ
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 2
  southHemisphereChart : southHemisphere ≃ₜ
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 2
  overlapChart : (northNeighborhood ∩ southNeighborhood :
      Set (((TopCat.sphere.{u} (n + 1) : TopCat.{u}) : Type u))) ≃ₜ
    ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1))))
  equatorChart : equator ≃ₜ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 2
  equatorSphere : equator ≃ₜ
    ((TopCat.sphere.{u} n : TopCat.{u}) : Type u)
  northSquare : ∀ x : northHemisphere,
    northChart ⟨x.1, northSubset x.2⟩ = (northHemisphereChart x).1
  southSquare : ∀ x : southHemisphere,
    southChart ⟨x.1, southSubset x.2⟩ = (southHemisphereChart x).1
  equatorSquare : ∀ x : equator,
    overlapChart ⟨x.1, ⟨equatorNorthSubset x.2, equatorSouthSubset x.2⟩⟩ =
      radiusTwoSphereInPunctured n (equatorChart x)

/-- Hatcher's hemisphere package on `TopCat.sphere (n+1)`, with radius-two
stereographic targets and commuting inclusion squares. -/
noncomputable def hemisphereChartData (n : ℕ) : HemisphereChartData.{u} n where
  northHemisphere := Hatcher.Sphere.northHemisphere n
  southHemisphere := Hatcher.Sphere.southHemisphere n
  equator := Hatcher.Sphere.equator n
  northPole := Hatcher.Sphere.northPole n
  southPole := Hatcher.Sphere.southPole n
  northNeighborhood := Hatcher.Sphere.northNeighborhood n
  southNeighborhood := Hatcher.Sphere.southNeighborhood n
  northNeighborhood_eq := northNeighborhood_eq_compl_southPole n
  southNeighborhood_eq := southNeighborhood_eq_compl_northPole n
  northHemisphere_spec := mem_northHemisphere n
  southHemisphere_spec := mem_southHemisphere n
  equator_spec := mem_equator n
  cover := hemisphere_union n
  intersection := hemisphere_intersection n
  northOpen := isOpen_northNeighborhood n
  southOpen := isOpen_southNeighborhood n
  northSubset := northHemisphere_subset_northNeighborhood n
  southSubset := southHemisphere_subset_southNeighborhood n
  northInteriorSubset := northHemisphere_subset_interior_northNeighborhood n
  southInteriorSubset := southHemisphere_subset_interior_southNeighborhood n
  equatorNorthSubset := equator_subset_northNeighborhood n
  equatorSouthSubset := equator_subset_southNeighborhood n
  northChart := northStereographicHomeomorph n
  southChart := southStereographicHomeomorph n
  northHemisphereChart := northHemisphereHomeomorph n
  southHemisphereChart := southHemisphereHomeomorph n
  overlapChart := overlapStereographicHomeomorph n
  equatorChart := equatorStereographicHomeomorph n
  equatorSphere := equatorSphereHomeomorph n
  northSquare := by
    intro x
    exact northHemisphere_inclusion_square n x
  southSquare := by
    intro x
    exact southHemisphere_inclusion_square n x
  equatorSquare := by
    intro x
    exact equator_inclusion_square n x

end Hatcher.Sphere
