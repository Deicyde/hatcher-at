/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Mathlib.Topology.Category.TopCat.Sphere

/-!
# Fixed-point-free disk maps retract onto the boundary

The ray from `f(x)` through `x` meets the boundary sphere continuously when
`f` has no fixed points. This is the point-set-topological part of Hatcher's
proof of the Brouwer fixed-point theorem.
-/

noncomputable section

open CategoryTheory Real
open scoped InnerProductSpace

namespace Hatcher.Disc

private theorem quadratic_root_identity (a q c s : ℝ) (hq : q ≠ 0)
    (hs : s ^ 2 = a ^ 2 + q * c) :
    2 * ((-a + s) / q) * a + ((-a + s) / q) ^ 2 * q = c := by
  field_simp
  linear_combination hs

private noncomputable def rayRoot {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x u : E) : ℝ :=
  (-⟪x, u⟫_ℝ + Real.sqrt (⟪x, u⟫_ℝ ^ 2 + ‖u‖ ^ 2 * (1 - ‖x‖ ^ 2))) /
    ‖u‖ ^ 2

private theorem rayRoot_discrim_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x u : E) (hx : ‖x‖ ≤ 1) :
    0 ≤ ⟪x, u⟫_ℝ ^ 2 + ‖u‖ ^ 2 * (1 - ‖x‖ ^ 2) := by
  have h1 : (0 : ℝ) ≤ ⟪x, u⟫_ℝ ^ 2 := sq_nonneg _
  have h2 : 0 ≤ ‖u‖ ^ 2 * (1 - ‖x‖ ^ 2) :=
    mul_nonneg (sq_nonneg _) (by nlinarith [norm_nonneg x])
  linarith

private theorem norm_rayPoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x u : E) (hu : u ≠ 0) (hx : ‖x‖ ≤ 1) :
    ‖x + rayRoot x u • u‖ = 1 := by
  have hq : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  have hDnn := rayRoot_discrim_nonneg x u hx
  have hs2 :
      Real.sqrt (⟪x, u⟫_ℝ ^ 2 + ‖u‖ ^ 2 * (1 - ‖x‖ ^ 2)) ^ 2 =
        ⟪x, u⟫_ℝ ^ 2 + ‖u‖ ^ 2 * (1 - ‖x‖ ^ 2) :=
    Real.sq_sqrt hDnn
  have key := quadratic_root_identity ⟪x, u⟫_ℝ (‖u‖ ^ 2) (1 - ‖x‖ ^ 2)
    (Real.sqrt (⟪x, u⟫_ℝ ^ 2 + ‖u‖ ^ 2 * (1 - ‖x‖ ^ 2))) hq hs2
  have hsq : ‖x + rayRoot x u • u‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs]
    dsimp only [rayRoot]
    nlinarith [key]
  nlinarith [norm_nonneg (x + rayRoot x u • u)]

private theorem rayRoot_eq_zero_of_boundary {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x u : E) (hx : ‖x‖ = 1)
    (hip : 0 ≤ ⟪x, u⟫_ℝ) : rayRoot x u = 0 := by
  have hrw :
      ⟪x, u⟫_ℝ ^ 2 + ‖u‖ ^ 2 * (1 - ‖x‖ ^ 2) = ⟪x, u⟫_ℝ ^ 2 := by
    rw [hx]
    ring
  rw [rayRoot, hrw, Real.sqrt_sq hip]
  simp

/-- **Hatcher, Corollary 2.15 (pages 114–115), using the ray construction from
Theorem 1.9 (pages 31–32).** A fixed-point-free self-map of a
positive-dimensional disk gives a retraction onto its boundary. -/
theorem exists_diskBoundary_retraction_of_fixedPointFree (n : ℕ)
    (f : TopCat.disk.{0} (n + 1) ⟶ TopCat.disk.{0} (n + 1))
    (hf : ∀ x : TopCat.disk.{0} (n + 1), f x ≠ x) :
    ∃ r : TopCat.disk.{0} (n + 1) ⟶ TopCat.diskBoundary.{0} (n + 1),
      TopCat.diskBoundaryInclusion.{0} (n + 1) ≫ r = 𝟙 _ := by
  let coord : TopCat.disk.{0} (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun x => x.down.1
  have hcoord : Continuous coord := by
    exact (continuous_subtype_val.comp continuous_uliftDown).congr (fun _ => rfl)
  have hcoord_norm : ∀ x : TopCat.disk.{0} (n + 1), ‖coord x‖ ≤ 1 := by
    intro x
    simpa [coord] using (mem_closedBall_zero_iff.mp x.down.2)
  let u : TopCat.disk.{0} (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun x => coord x - coord (f x)
  have hu : ∀ x : TopCat.disk.{0} (n + 1), u x ≠ 0 := by
    intro x hzero
    apply hf x
    apply ULift.ext
    apply Subtype.ext
    simpa [u, coord] using (sub_eq_zero.mp hzero).symm
  have hucont : Continuous u := by
    exact (hcoord.sub (hcoord.comp f.hom.continuous)).congr (fun _ => rfl)
  let t : TopCat.disk.{0} (n + 1) → ℝ := fun x => rayRoot (coord x) (u x)
  have htcont : Continuous t := by
    have hip : Continuous fun x => ⟪coord x, u x⟫_ℝ := hcoord.inner hucont
    have hunorm : Continuous fun x => ‖u x‖ := hucont.norm
    have hxnorm : Continuous fun x => ‖coord x‖ := hcoord.norm
    exact (Continuous.div
        (hip.neg.add
          (((hip.pow 2).add
            ((hunorm.pow 2).mul (continuous_const.sub (hxnorm.pow 2)))).sqrt))
        (hunorm.pow 2)
        (fun x => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hu x)))).congr (fun _ => rfl)
  let p : TopCat.disk.{0} (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun x => coord x + t x • u x
  have hpcont : Continuous p := by
    exact (hcoord.add (htcont.smul hucont)).congr (fun _ => rfl)
  have hpnorm : ∀ x : TopCat.disk.{0} (n + 1), ‖p x‖ = 1 := by
    intro x
    simpa [p, t] using norm_rayPoint (coord x) (u x) (hu x) (hcoord_norm x)
  have hmem : ∀ x : TopCat.disk.{0} (n + 1),
      p x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    intro x
    exact mem_sphere_zero_iff_norm.mpr (hpnorm x)
  let r : TopCat.disk.{0} (n + 1) ⟶ TopCat.diskBoundary.{0} (n + 1) :=
    TopCat.ofHom
      ⟨fun x => ULift.up ⟨p x, hmem x⟩,
        continuous_uliftUp.comp (Continuous.subtype_mk hpcont hmem)⟩
  refine ⟨r, ?_⟩
  apply TopCat.ext
  intro z
  rw [TopCat.comp_app, TopCat.id_app]
  apply ULift.ext
  apply Subtype.ext
  let iz : TopCat.disk.{0} (n + 1) := TopCat.diskBoundaryInclusion.{0} (n + 1) z
  change p iz = z.down.1
  have hzNorm : ‖coord iz‖ = 1 := by
    change ‖z.down.1‖ = 1
    exact mem_sphere_zero_iff_norm.mp z.down.2
  have hinner : ⟪coord iz, coord (f iz)⟫_ℝ ≤ 1 := by
    calc
      ⟪coord iz, coord (f iz)⟫_ℝ ≤ ‖coord iz‖ * ‖coord (f iz)‖ :=
        real_inner_le_norm _ _
      _ ≤ 1 := by simpa [hzNorm] using hcoord_norm (f iz)
  have hip : 0 ≤ ⟪coord iz, u iz⟫_ℝ := by
    change 0 ≤ ⟪coord iz, coord iz - coord (f iz)⟫_ℝ
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hzNorm]
    nlinarith
  have hroot0 : t iz = 0 := by
    simpa [t] using rayRoot_eq_zero_of_boundary (coord iz) (u iz) hzNorm hip
  calc
    p iz = coord iz := by simp [p, hroot0]
    _ = z.down.1 := by rfl

end Hatcher.Disc
