/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.AntipodalDegree
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Degree of fixed-point-free sphere maps

Hatcher's normalized straight-line formula gives a homotopy from every
fixed-point-free sphere map to the antipodal map.  The unnormalized vector can
vanish only when the parameter is one half and the original map fixes the
point, so normalization is continuous on the entire cylinder.
-/

noncomputable section

open CategoryTheory Metric Set unitInterval
open scoped EuclideanSpace

namespace Hatcher.Sphere

private abbrev SphereAmbient (n : ℕ) :=
  EuclideanSpace ℝ (Fin (n + 1))

private def sphereAmbientPoint (n : ℕ) (x : TopCat.sphere.{0} n) :
    SphereAmbient n :=
  (sphereULiftHomeomorph n x).1

@[simp]
private theorem norm_sphereAmbientPoint (n : ℕ)
    (x : TopCat.sphere.{0} n) :
    ‖sphereAmbientPoint n x‖ = 1 := by
  simpa only [sphereAmbientPoint, mem_sphere_zero_iff_norm] using
    (sphereULiftHomeomorph n x).2

/-- The unnormalized segment from `f(x)` to `-x`, parametrized by the unit
interval exactly as on Hatcher's printed page 134. -/
def fixedPointFreeSegment (n : ℕ)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (p : I × TopCat.sphere.{0} n) : SphereAmbient n :=
  (1 - (p.1 : ℝ)) • sphereAmbientPoint n (f p.2) -
    (p.1 : ℝ) • sphereAmbientPoint n p.2

private theorem continuous_fixedPointFreeSegment (n : ℕ)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    Continuous (fixedPointFreeSegment n f) := by
  let t : I × TopCat.sphere.{0} n → ℝ := fun p ↦ p.1
  have ht : Continuous t := continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : I × TopCat.sphere.{0} n ↦
      sphereAmbientPoint n p.2) :=
    continuous_subtype_val.comp <|
      (sphereULiftHomeomorph n).continuous.comp continuous_snd
  have hfx : Continuous (fun p : I × TopCat.sphere.{0} n ↦
      sphereAmbientPoint n (f p.2)) :=
    continuous_subtype_val.comp <|
      (sphereULiftHomeomorph n).continuous.comp <|
        f.hom.continuous.comp continuous_snd
  exact ((continuous_const.sub ht).smul hfx).sub (ht.smul hx)

private theorem fixedPointFreeSegment_ne_zero (n : ℕ)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (hf : ∀ x, f x ≠ x) (p : I × TopCat.sphere.{0} n) :
    fixedPointFreeSegment n f p ≠ 0 := by
  intro hzero
  let t : ℝ := p.1
  let y := sphereAmbientPoint n (f p.2)
  let x := sphereAmbientPoint n p.2
  have ht0 : 0 ≤ t := p.1.2.1
  have ht1 : t ≤ 1 := p.1.2.2
  have heq : (1 - t) • y = t • x := by
    apply sub_eq_zero.mp
    exact hzero
  have hnorm := congrArg norm heq
  have hy : ‖y‖ = 1 := norm_sphereAmbientPoint n (f p.2)
  have hx : ‖x‖ = 1 := norm_sphereAmbientPoint n p.2
  rw [norm_smul, norm_smul, hy, hx, mul_one, mul_one,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0] at hnorm
  have hcoeff : 1 - t = t := hnorm
  have htne : t ≠ 0 := by
    intro ht
    rw [ht] at hcoeff
    norm_num at hcoeff
  have hxy : y = x := by
    rw [hcoeff] at heq
    exact (smul_right_injective (SphereAmbient n) htne) heq
  apply hf p.2
  apply (sphereULiftHomeomorph n).injective
  exact Subtype.ext hxy

private noncomputable def fixedPointFreeHomotopyRaw (n : ℕ)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (hf : ∀ x, f x ≠ x)
    (p : I × TopCat.sphere.{0} n) : RawSphere n :=
  ⟨NormedSpace.normalize (fixedPointFreeSegment n f p), by
    rw [mem_sphere_zero_iff_norm]
    exact NormedSpace.norm_normalize
      (fixedPointFreeSegment_ne_zero n f hf p)⟩

private theorem continuous_fixedPointFreeHomotopyRaw (n : ℕ)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (hf : ∀ x, f x ≠ x) :
    Continuous (fixedPointFreeHomotopyRaw n f hf) := by
  apply Continuous.subtype_mk
  change Continuous (fun p ↦
    ‖fixedPointFreeSegment n f p‖⁻¹ • fixedPointFreeSegment n f p)
  have hsegment := continuous_fixedPointFreeSegment n f
  exact (hsegment.norm.inv₀ fun p ↦
    norm_ne_zero_iff.mpr (fixedPointFreeSegment_ne_zero n f hf p)).smul
      hsegment

@[simp]
private theorem fixedPointFreeSegment_zero (n : ℕ)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (x : TopCat.sphere.{0} n) :
    fixedPointFreeSegment n f (0, x) = sphereAmbientPoint n (f x) := by
  simp [fixedPointFreeSegment]

@[simp]
private theorem fixedPointFreeSegment_one (n : ℕ)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (x : TopCat.sphere.{0} n) :
    fixedPointFreeSegment n f (1, x) = -sphereAmbientPoint n x := by
  simp [fixedPointFreeSegment]

/-- **Hatcher, degree property (g), printed pages 134–135.** The normalized
segment from a fixed-point-free sphere map to the antipodal map. -/
noncomputable def fixedPointFreeHomotopy (n : ℕ)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (hf : ∀ x, f x ≠ x) :
    TopCat.Homotopy f (antipodalIso n).hom where
  toFun p := (sphereULiftHomeomorph n).symm
    (fixedPointFreeHomotopyRaw n f hf p)
  continuous_toFun := (sphereULiftHomeomorph n).symm.continuous.comp
    (continuous_fixedPointFreeHomotopyRaw n f hf)
  map_zero_left x := by
    apply (sphereULiftHomeomorph n).injective
    rw [(sphereULiftHomeomorph n).apply_symm_apply]
    apply Subtype.ext
    change NormedSpace.normalize (fixedPointFreeSegment n f (0, x)) =
      sphereAmbientPoint n (f x)
    rw [fixedPointFreeSegment_zero]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one
      (norm_sphereAmbientPoint n (f x))
  map_one_left x := by
    apply (sphereULiftHomeomorph n).injective
    rw [(sphereULiftHomeomorph n).apply_symm_apply,
      sphereULiftHomeomorph_antipodalIso_apply]
    apply Subtype.ext
    change NormedSpace.normalize (fixedPointFreeSegment n f (1, x)) =
      -sphereAmbientPoint n x
    rw [fixedPointFreeSegment_one]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one <| by
      rw [norm_neg, norm_sphereAmbientPoint]

/-- **Hatcher, degree property (g), printed pages 134–135.** A fixed-point-free
self-map of `Sⁿ` has the degree of the antipodal map. -/
theorem degree_eq_neg_one_pow_of_fixedPointFree
    (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (hf : ∀ x, f x ≠ x) :
    degree n hn f = (-1 : ℤ) ^ (n + 1) :=
  (degree_eq_of_homotopy n hn (fixedPointFreeHomotopy n f hf)).trans
    (degree_antipodal n hn)

end Hatcher.Sphere
