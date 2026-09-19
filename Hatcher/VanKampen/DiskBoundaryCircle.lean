import Hatcher.Circle.FundamentalGroup
import Mathlib.Topology.Category.TopCat.Sphere

/-!
# The boundary of the two-disk

This file identifies Mathlib's boundary of the two-disk with the complex unit
circle.  The identification fixes the standard basepoint and transports
Hatcher's positively oriented once-around loop back to the disk boundary.
-/

open Metric

namespace Hatcher

universe u

/-- The standard point `(1, 0)` on the boundary of the two-disk. -/
noncomputable def diskBoundaryTwoBasepoint :
    ((TopCat.diskBoundary.{u} 2 : TopCat.{u}) : Type u) :=
  ULift.up ⟨EuclideanSpace.single 0 1, by
    rw [mem_sphere_zero_iff_norm]
    simp⟩

private noncomputable def euclideanTwoSphereHomeomorphCircle :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ _root_.Circle :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype fun x => by
    change x ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖Complex.orthonormalBasisOneI.repr.symm x‖ = 1
    rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]

/-- The standard homeomorphism from the boundary of the two-disk to the
complex unit circle. -/
noncomputable def diskBoundaryTwoHomeomorphCircle :
    ((TopCat.diskBoundary.{u} 2 : TopCat.{u}) : Type u) ≃ₜ _root_.Circle :=
  (Homeomorph.ulift.{u, 0} :
      ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ≃ₜ
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).trans
    euclideanTwoSphereHomeomorphCircle

/-- The standard boundary homeomorphism sends `(1, 0)` to `1`. -/
@[simp] theorem diskBoundaryTwoHomeomorphCircle_basepoint :
    diskBoundaryTwoHomeomorphCircle.{u} diskBoundaryTwoBasepoint.{u} =
      (1 : _root_.Circle) := by
  apply Subtype.ext
  change Complex.orthonormalBasisOneI.repr.symm
      (EuclideanSpace.single 0 1) = (1 : ℂ)
  rw [Complex.orthonormalBasisOneI_repr_symm_apply]
  simp

/-- The inverse boundary homeomorphism sends `1` to `(1, 0)`. -/
@[simp] theorem diskBoundaryTwoHomeomorphCircle_symm_one :
    diskBoundaryTwoHomeomorphCircle.{u}.symm (1 : _root_.Circle) =
      diskBoundaryTwoBasepoint.{u} :=
  diskBoundaryTwoHomeomorphCircle.{u}.symm_apply_eq.mpr
    diskBoundaryTwoHomeomorphCircle_basepoint.{u}.symm

/-- The positively oriented once-around loop on the boundary of the two-disk. -/
noncomputable def diskBoundaryTwoLoop :
    Path diskBoundaryTwoBasepoint.{u} diskBoundaryTwoBasepoint.{u} :=
  ((Circle.loopOfInt 1).map diskBoundaryTwoHomeomorphCircle.{u}.symm.continuous).cast
    diskBoundaryTwoHomeomorphCircle_symm_one.{u}.symm
    diskBoundaryTwoHomeomorphCircle_symm_one.{u}.symm

/-- Mapping the standard disk-boundary loop to the circle recovers Hatcher's
positively oriented generator exactly. -/
theorem diskBoundaryTwoHomeomorphCircle_map_loop :
    (diskBoundaryTwoLoop.{u}.map diskBoundaryTwoHomeomorphCircle.{u}.continuous).cast
        diskBoundaryTwoHomeomorphCircle_basepoint.{u}.symm
        diskBoundaryTwoHomeomorphCircle_basepoint.{u}.symm =
      Circle.loopOfInt 1 := by
  apply Path.ext
  funext t
  simp only [diskBoundaryTwoLoop, Path.cast_coe, Path.map_coe,
    Function.comp_apply]
  simp

end Hatcher
