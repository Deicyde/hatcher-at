import Hatcher.Sphere.HemisphereCharts
import Mathlib.Data.Finset.SymmDiff

/-!
# Coordinate sign changes on spheres

Changing any finite set of ambient coordinates is a linear isometry, hence
restricts to a homeomorphism of the unit sphere.  This file keeps
`TopCat.sphere` as the public sphere model and passes through the existing raw
metric model only to perform coordinate calculations.
-/

noncomputable section

open CategoryTheory Metric Set
open scoped EuclideanSpace symmDiff

namespace Hatcher.Sphere

private noncomputable def ambientCoordinateSignChange
    (n : ℕ) (s : Finset (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) := by
  classical
  exact LinearIsometryEquiv.piLpCongrRight 2 fun i ↦
    if i ∈ s then LinearIsometryEquiv.neg ℝ
    else LinearIsometryEquiv.refl ℝ ℝ

@[simp]
private theorem ambientCoordinateSignChange_apply
    (n : ℕ) (s : Finset (Fin (n + 1)))
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    ambientCoordinateSignChange n s x i =
      if i ∈ s then -x i else x i := by
  classical
  simp only [ambientCoordinateSignChange,
    LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
  split_ifs <;> rfl

private noncomputable def rawCoordinateSignChangeHomeomorph
    (n : ℕ) (s : Finset (Fin (n + 1))) :
    RawSphere n ≃ₜ RawSphere n :=
  (ambientCoordinateSignChange n s).toHomeomorph.subtype fun x ↦ by
    simp only [mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖ambientCoordinateSignChange n s x‖ = 1
    rw [(ambientCoordinateSignChange n s).norm_map]

/-- The homeomorphism of `TopCat.sphere n` that negates exactly the ambient
coordinates in `s`. -/
noncomputable def coordinateSignChangeHomeomorph
    (n : ℕ) (s : Finset (Fin (n + 1))) :
    ((TopCat.sphere.{0} n : TopCat.{0}) : Type) ≃ₜ
      ((TopCat.sphere.{0} n : TopCat.{0}) : Type) :=
  (sphereULiftHomeomorph n).trans
    ((rawCoordinateSignChangeHomeomorph n s).trans
      (sphereULiftHomeomorph n).symm)

/-- The coordinate sign-change homeomorphism as an isomorphism in `TopCat`. -/
noncomputable def coordinateSignChangeIso
    (n : ℕ) (s : Finset (Fin (n + 1))) :
    TopCat.sphere.{0} n ≅ TopCat.sphere.{0} n :=
  TopCat.isoOfHomeo (coordinateSignChangeHomeomorph n s)

/-- A one-coordinate sign change. -/
noncomputable def coordinateReflectionIso
    (n : ℕ) (i : Fin (n + 1)) :
    TopCat.sphere.{0} n ≅ TopCat.sphere.{0} n :=
  coordinateSignChangeIso n {i}

/-- The all-coordinate sign change, namely the antipodal homeomorphism. -/
noncomputable def antipodalIso (n : ℕ) :
    TopCat.sphere.{0} n ≅ TopCat.sphere.{0} n :=
  coordinateSignChangeIso n Finset.univ

/-- Coordinate formula for a sign change after passing through the project's
single bridge to the raw metric sphere. -/
@[simp]
theorem sphereULiftHomeomorph_coordinateSignChangeIso_apply
    (n : ℕ) (s : Finset (Fin (n + 1)))
    (x : TopCat.sphere.{0} n) (i : Fin (n + 1)) :
    ((sphereULiftHomeomorph n ((coordinateSignChangeIso n s).hom x)).1 :
        EuclideanSpace ℝ (Fin (n + 1))) i =
      if i ∈ s then
        -((sphereULiftHomeomorph n x).1 :
          EuclideanSpace ℝ (Fin (n + 1))) i
      else
        ((sphereULiftHomeomorph n x).1 :
          EuclideanSpace ℝ (Fin (n + 1))) i := by
  classical
  change ambientCoordinateSignChange n s
      ((sphereULiftHomeomorph n x).1 :
        EuclideanSpace ℝ (Fin (n + 1))) i = _
  exact ambientCoordinateSignChange_apply n s _ i

/-- Coordinate formula for reflection in a coordinate hyperplane. -/
@[simp]
theorem sphereULiftHomeomorph_coordinateReflectionIso_apply
    (n : ℕ) (j : Fin (n + 1))
    (x : TopCat.sphere.{0} n) (i : Fin (n + 1)) :
    ((sphereULiftHomeomorph n ((coordinateReflectionIso n j).hom x)).1 :
        EuclideanSpace ℝ (Fin (n + 1))) i =
      if i = j then
        -((sphereULiftHomeomorph n x).1 :
          EuclideanSpace ℝ (Fin (n + 1))) i
      else
        ((sphereULiftHomeomorph n x).1 :
          EuclideanSpace ℝ (Fin (n + 1))) i := by
  classical
  simp [coordinateReflectionIso]

/-- Composing two coordinate sign changes changes precisely their symmetric
difference. -/
theorem coordinateSignChangeIso_hom_comp
    (n : ℕ) (s t : Finset (Fin (n + 1))) :
    (coordinateSignChangeIso n s).hom ≫
        (coordinateSignChangeIso n t).hom =
      (coordinateSignChangeIso n (s ∆ t)).hom := by
  classical
  ext x
  apply (sphereULiftHomeomorph n).injective
  apply Subtype.ext
  apply PiLp.ext
  intro i
  simp only [ConcreteCategory.comp_apply,
    sphereULiftHomeomorph_coordinateSignChangeIso_apply]
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
    simp [his, hit, Finset.mem_symmDiff]

/-- For disjoint coordinate sets, symmetric difference is ordinary union. -/
theorem coordinateSignChangeIso_hom_comp_of_disjoint
    (n : ℕ) {s t : Finset (Fin (n + 1))} (h : Disjoint s t) :
    (coordinateSignChangeIso n s).hom ≫
        (coordinateSignChangeIso n t).hom =
      (coordinateSignChangeIso n (s ∪ t)).hom := by
  rw [coordinateSignChangeIso_hom_comp,
    (Finset.symmDiff_eq_union_iff s t).2 h]

/-- The all-coordinate sign change is pointwise negation on the raw sphere. -/
theorem sphereULiftHomeomorph_antipodalIso_apply
    (n : ℕ) (x : TopCat.sphere.{0} n) :
    sphereULiftHomeomorph n ((antipodalIso n).hom x) =
      -(sphereULiftHomeomorph n x) := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  simp [antipodalIso]

/-- Reflection in the final coordinate fixes the equator pointwise. -/
theorem coordinateReflection_last_apply_of_mem_equator
    (n : ℕ) {x : TopCat.sphere.{0} (n + 1)}
    (hx : x ∈ equator n) :
    (coordinateReflectionIso (n + 1) (Fin.last (n + 1))).hom x = x := by
  apply (sphereULiftHomeomorph (n + 1)).injective
  apply Subtype.ext
  apply PiLp.ext
  intro i
  rw [sphereULiftHomeomorph_coordinateReflectionIso_apply]
  by_cases hi : i = Fin.last (n + 1)
  · subst i
    have hzero := (mem_equator n x).mp hx
    simp [hzero]
  · simp [hi]

/-- Reflection in the final coordinate carries the northern hemisphere to the
southern hemisphere. -/
@[simp]
theorem coordinateReflection_last_mem_northHemisphere_iff
    (n : ℕ) (x : TopCat.sphere.{0} (n + 1)) :
    (coordinateReflectionIso (n + 1) (Fin.last (n + 1))).hom x ∈
        northHemisphere n ↔
      x ∈ southHemisphere n := by
  rw [mem_northHemisphere, mem_southHemisphere]
  simp

/-- Reflection in the final coordinate carries the southern hemisphere to the
northern hemisphere. -/
@[simp]
theorem coordinateReflection_last_mem_southHemisphere_iff
    (n : ℕ) (x : TopCat.sphere.{0} (n + 1)) :
    (coordinateReflectionIso (n + 1) (Fin.last (n + 1))).hom x ∈
        southHemisphere n ↔
      x ∈ northHemisphere n := by
  rw [mem_southHemisphere, mem_northHemisphere]
  simp

end Hatcher.Sphere
