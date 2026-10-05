/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.DoubleSimplexSphere
import Hatcher.Sphere.DegreeProperties
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Degree of a reflection of a sphere

Reflection across the equator orthogonal to a unit vector is the restriction
of Mathlib's reflection in the corresponding codimension-one subspace.  An
explicit orthogonal reflection carries any unit normal to the final coordinate,
so the general reflection is conjugate to the coordinate reflection computed
by the ordered double-simplex model.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Metric Set
open scoped EuclideanSpace RealInnerProductSpace

namespace Hatcher.Sphere

private abbrev SphereAmbient (n : ℕ) :=
  EuclideanSpace ℝ (Fin (n + 1))

/-- The equatorial linear subspace orthogonal to a unit normal. -/
noncomputable def reflectionEquatorSubmodule
    (n : ℕ) (v : RawSphere n) : Submodule ℝ (SphereAmbient n) :=
  (ℝ ∙ (v : SphereAmbient n))ᗮ

/-- Ambient orthogonal reflection across the equator normal to `v`. -/
noncomputable def ambientReflection
    (n : ℕ) (v : RawSphere n) :
    SphereAmbient n ≃ₗᵢ[ℝ] SphereAmbient n :=
  (reflectionEquatorSubmodule n v).reflection

private noncomputable def rawReflectionHomeomorph
    (n : ℕ) (v : RawSphere n) : RawSphere n ≃ₜ RawSphere n :=
  (ambientReflection n v).toHomeomorph.subtype fun x ↦ by
    simp only [mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖ambientReflection n v x‖ = 1
    rw [(ambientReflection n v).norm_map]

/-- Reflection of the standard sphere across the equator normal to `v`. -/
noncomputable def reflectionIso (n : ℕ) (v : RawSphere n) :
    TopCat.sphere.{0} n ≅ TopCat.sphere.{0} n :=
  TopCat.isoOfHomeo <|
    (sphereULiftHomeomorph n).trans
      ((rawReflectionHomeomorph n v).trans
        (sphereULiftHomeomorph n).symm)

/-- The equator perpendicular to `v`. -/
def reflectionEquator (n : ℕ) (v : RawSphere n) :
    Set (TopCat.sphere.{0} n) :=
  {x | inner ℝ (v : SphereAmbient n)
    ((sphereULiftHomeomorph n x).1 : SphereAmbient n) = 0}

/-- The closed positive hemisphere determined by `v`. -/
def reflectionPositiveHemisphere (n : ℕ) (v : RawSphere n) :
    Set (TopCat.sphere.{0} n) :=
  {x | 0 ≤ inner ℝ (v : SphereAmbient n)
    ((sphereULiftHomeomorph n x).1 : SphereAmbient n)}

/-- The closed negative hemisphere determined by `v`. -/
def reflectionNegativeHemisphere (n : ℕ) (v : RawSphere n) :
    Set (TopCat.sphere.{0} n) :=
  {x | inner ℝ (v : SphereAmbient n)
    ((sphereULiftHomeomorph n x).1 : SphereAmbient n) ≤ 0}

@[simp]
theorem sphereULiftHomeomorph_reflectionIso_apply
    (n : ℕ) (v : RawSphere n) (x : TopCat.sphere.{0} n) :
    sphereULiftHomeomorph n ((reflectionIso n v).hom x) =
      rawReflectionHomeomorph n v (sphereULiftHomeomorph n x) :=
  rfl

private theorem ambientReflection_apply_formula
    (n : ℕ) (v : RawSphere n) (x : SphereAmbient n) :
    ambientReflection n v x =
      x - (2 * inner ℝ (v : SphereAmbient n) x) •
        (v : SphereAmbient n) := by
  unfold ambientReflection reflectionEquatorSubmodule
  rw [Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  have hv : ‖(v : SphereAmbient n)‖ = 1 :=
    norm_eq_of_mem_sphere v
  simp [hv]
  module

private theorem inner_ambientReflection
    (n : ℕ) (v : RawSphere n) (x : SphereAmbient n) :
    inner ℝ (v : SphereAmbient n) (ambientReflection n v x) =
      -inner ℝ (v : SphereAmbient n) x := by
  rw [ambientReflection_apply_formula, inner_sub_right, inner_smul_right]
  have hv : ‖(v : SphereAmbient n)‖ = 1 :=
    norm_eq_of_mem_sphere v
  have hvinner : inner ℝ (v : SphereAmbient n) v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  rw [hvinner]
  ring

/-- Reflection fixes its equator pointwise. -/
theorem reflectionIso_apply_of_mem_equator
    (n : ℕ) (v : RawSphere n) {x : TopCat.sphere.{0} n}
    (hx : x ∈ reflectionEquator n v) :
    (reflectionIso n v).hom x = x := by
  apply (sphereULiftHomeomorph n).injective
  apply Subtype.ext
  exact Submodule.reflection_mem_subspace_eq_self <|
    (Submodule.mem_orthogonal_singleton_iff_inner_right).2 hx

/-- Reflection interchanges the two closed hemispheres. -/
@[simp]
theorem reflectionIso_mem_positiveHemisphere_iff
    (n : ℕ) (v : RawSphere n) (x : TopCat.sphere.{0} n) :
    (reflectionIso n v).hom x ∈ reflectionPositiveHemisphere n v ↔
      x ∈ reflectionNegativeHemisphere n v := by
  change 0 ≤ inner ℝ (v : SphereAmbient n)
      (ambientReflection n v (sphereULiftHomeomorph n x).1) ↔ _
  rw [inner_ambientReflection]
  simp [reflectionNegativeHemisphere]

/-- Reflection also carries the negative hemisphere back to the positive one. -/
@[simp]
theorem reflectionIso_mem_negativeHemisphere_iff
    (n : ℕ) (v : RawSphere n) (x : TopCat.sphere.{0} n) :
    (reflectionIso n v).hom x ∈ reflectionNegativeHemisphere n v ↔
      x ∈ reflectionPositiveHemisphere n v := by
  change inner ℝ (v : SphereAmbient n)
      (ambientReflection n v (sphereULiftHomeomorph n x).1) ≤ 0 ↔ _
  rw [inner_ambientReflection]
  simp [reflectionPositiveHemisphere]

/-- The unit vector in coordinate `i`, bundled as a point of the raw sphere. -/
noncomputable def coordinateNormal (n : ℕ) (i : Fin (n + 1)) :
    RawSphere n :=
  ⟨EuclideanSpace.single i 1, by
    rw [mem_sphere_zero_iff_norm]
    simp⟩

private theorem ambientReflection_coordinateNormal_apply
    (n : ℕ) (j : Fin (n + 1)) (x : SphereAmbient n)
    (i : Fin (n + 1)) :
    ambientReflection n (coordinateNormal n j) x i =
      if i = j then -x i else x i := by
  unfold ambientReflection reflectionEquatorSubmodule
  rw [Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  simp [coordinateNormal, EuclideanSpace.inner_single_left]
  by_cases hij : i = j
  · subst i
    simp
    ring
  · simp [hij]

/-- Reflection normal to a coordinate vector is the corresponding coordinate
sign change. -/
theorem reflectionIso_coordinateNormal
    (n : ℕ) (i : Fin (n + 1)) :
    (reflectionIso n (coordinateNormal n i)).hom =
      (coordinateReflectionIso n i).hom := by
  ext x
  apply (sphereULiftHomeomorph n).injective
  apply Subtype.ext
  apply PiLp.ext
  intro j
  rw [sphereULiftHomeomorph_reflectionIso_apply]
  change ambientReflection n (coordinateNormal n i)
      (sphereULiftHomeomorph n x).1 j = _
  rw [ambientReflection_coordinateNormal_apply,
    sphereULiftHomeomorph_coordinateReflectionIso_apply]

/-- The last-coordinate reflection has degree `-1`, computed from the ordered
double-simplex generator. -/
theorem degree_coordinateReflection_last
    (n : ℕ) (hn : 0 < n) :
    degree n hn (coordinateReflectionIso n (Fin.last n)).hom = -1 := by
  let R := AddCommGrpCat.of ℤ
  let F := Hatcher.Reduced.homologyFunctor R n
  have hswap := Hatcher.Simplex.doubleSimplexFundamentalClass_map_swap R n
  have hcompat := doubleSimplexSwap_isoSphere n
  have hred :
      Hatcher.Simplex.doubleSimplexSphereFundamentalClass R n ≫
          F.map (coordinateReflectionIso n (Fin.last n)).hom =
        -Hatcher.Simplex.doubleSimplexSphereFundamentalClass R n := by
    rw [Hatcher.Simplex.doubleSimplexSphereFundamentalClass,
      Category.assoc, ← F.map_comp, ← hcompat, F.map_comp,
      ← Category.assoc, hswap, Preadditive.neg_comp]
  let e := Hatcher.Reduced.homologyIsoOfPositiveDegree
    (C := AddCommGrpCat.{0}) R n hn
  have hnat := e.hom.naturality
    (coordinateReflectionIso n (Fin.last n)).hom
  have hord :
      integralSphereFundamentalClass n hn ≫
          ((singularHomologyFunctor AddCommGrpCat n).obj R).map
            (coordinateReflectionIso n (Fin.last n)).hom =
        -integralSphereFundamentalClass n hn := by
    rw [integralSphereFundamentalClass, Category.assoc, ← hnat,
      ← Category.assoc, hred, Preadditive.neg_comp]
  have hdegree := integralSphereFundamentalClass_map n hn
    (coordinateReflectionIso n (Fin.last n)).hom
  rw [hord] at hdegree
  let _ : IsIso (integralSphereFundamentalClass n hn) :=
    integralSphereFundamentalClass_isIso n hn
  have hneg :
      AddCommGrpCat.asHom (G := AddCommGrpCat.of ℤ) (-1 : ℤ) ≫
          integralSphereFundamentalClass n hn =
        -integralSphereFundamentalClass n hn := by
    apply AddCommGrpCat.int_hom_ext
    rw [ConcreteCategory.comp_apply, AddCommGrpCat.asHom_hom_apply]
    simp
  have hasHom :
      AddCommGrpCat.asHom
          (degree n hn (coordinateReflectionIso n (Fin.last n)).hom) =
        AddCommGrpCat.asHom (G := AddCommGrpCat.of ℤ) (-1 : ℤ) := by
    rw [← cancel_mono (integralSphereFundamentalClass n hn)]
    rw [hneg]
    exact hdegree.symm
  have happ := ConcreteCategory.congr_hom hasHom (1 : ℤ)
  rw [AddCommGrpCat.asHom_hom_apply,
    AddCommGrpCat.asHom_hom_apply] at happ
  simpa using happ

/-- An orthogonal involution carrying `v` to the final coordinate vector. -/
noncomputable def reflectionConjugator
    (n : ℕ) (v : RawSphere n) :
    SphereAmbient n ≃ₗᵢ[ℝ] SphereAmbient n :=
  ((ℝ ∙ ((v : SphereAmbient n) -
    (coordinateNormal n (Fin.last n) : SphereAmbient n)))ᗮ).reflection

@[simp]
theorem reflectionConjugator_apply_normal
    (n : ℕ) (v : RawSphere n) :
    reflectionConjugator n v (v : SphereAmbient n) =
      (coordinateNormal n (Fin.last n) : SphereAmbient n) := by
  apply Submodule.reflection_sub
  simp [norm_eq_of_mem_sphere]

private theorem reflectionConjugator_symm_apply_last
    (n : ℕ) (v : RawSphere n) :
    (reflectionConjugator n v).symm
        (coordinateNormal n (Fin.last n) : SphereAmbient n) = v := by
  rw [← reflectionConjugator_apply_normal n v]
  exact (reflectionConjugator n v).symm_apply_apply v

private theorem ambientReflection_conjugacy
    (n : ℕ) (v : RawSphere n) :
    ambientReflection n v =
      (reflectionConjugator n v).trans
        ((ambientReflection n (coordinateNormal n (Fin.last n))).trans
          (reflectionConjugator n v).symm) := by
  let q := reflectionConjugator n v
  let e := coordinateNormal n (Fin.last n)
  apply LinearIsometryEquiv.ext
  intro x
  rw [ambientReflection_apply_formula,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply,
    ambientReflection_apply_formula]
  have hqv : q (v : SphereAmbient n) = (e : SphereAmbient n) :=
    reflectionConjugator_apply_normal n v
  have hinner : inner ℝ (e : SphereAmbient n) (q x) =
      inner ℝ (v : SphereAmbient n) x := by
    rw [← hqv, q.inner_map_map]
  rw [hinner, map_sub, map_smul, q.symm_apply_apply,
    reflectionConjugator_symm_apply_last n v]

private noncomputable def sphereIsoOfLinearIsometry
    (n : ℕ) (q : SphereAmbient n ≃ₗᵢ[ℝ] SphereAmbient n) :
    TopCat.sphere.{0} n ≅ TopCat.sphere.{0} n :=
  TopCat.isoOfHomeo <|
    (sphereULiftHomeomorph n).trans
      (((q.toHomeomorph.subtype fun x ↦ by
          simp only [mem_sphere_zero_iff_norm]
          change ‖x‖ = 1 ↔ ‖q x‖ = 1
          rw [q.norm_map])).trans
        (sphereULiftHomeomorph n).symm)

private theorem reflectionIso_conjugacy
    (n : ℕ) (v : RawSphere n) :
    (reflectionIso n v).hom =
      (sphereIsoOfLinearIsometry n (reflectionConjugator n v)).hom ≫
        (coordinateReflectionIso n (Fin.last n)).hom ≫
          (sphereIsoOfLinearIsometry n (reflectionConjugator n v)).inv := by
  rw [← reflectionIso_coordinateNormal]
  ext x
  apply (sphereULiftHomeomorph n).injective
  apply Subtype.ext
  change ambientReflection n v (sphereULiftHomeomorph n x).1 = _
  rw [ambientReflection_conjugacy]
  rfl

/-- **Hatcher, degree property (e), printed page 134.** Reflection across the
equator normal to any unit vector has degree `-1`. -/
theorem degree_reflection
    (n : ℕ) (hn : 0 < n) (v : RawSphere n) :
    degree n hn (reflectionIso n v).hom = -1 := by
  let q := sphereIsoOfLinearIsometry n (reflectionConjugator n v)
  have hq : degree n hn q.hom * degree n hn q.inv = 1 := by
    rw [← degree_comp, q.hom_inv_id, degree_id]
  rw [reflectionIso_conjugacy, degree_comp, degree_comp,
    degree_coordinateReflection_last]
  nlinarith

/-- Every coordinate reflection has degree `-1`. -/
theorem degree_coordinateReflection
    (n : ℕ) (hn : 0 < n) (i : Fin (n + 1)) :
    degree n hn (coordinateReflectionIso n i).hom = -1 := by
  rw [← reflectionIso_coordinateNormal]
  exact degree_reflection n hn (coordinateNormal n i)

end Hatcher.Sphere
