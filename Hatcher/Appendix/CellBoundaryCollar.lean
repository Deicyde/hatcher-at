/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.UnitInterval

/-!
# A radial collar of the boundary of a classical cell

The characteristic maps in Mathlib's classical CW complexes use the closed
sup-norm ball in `Fin n → ℝ`.  This file equips the outer half of that ball
with radial normalization and with a scheduled deformation to its boundary.
The construction is cellwise: it does not descend through a characteristic
map or assemble maps belonging to different cells.
-/

noncomputable section

open Metric Set Topology
open scoped unitInterval

namespace Hatcher.ClassicalCW

private abbrev CellModel (n : ℕ) := Fin n → ℝ

/-- The fixed-width outer collar in the closed sup-norm cell.  Its width is
`1 / 2`, as fixed by the regular-neighborhood implementation specification. -/
def cellBoundaryCollar (n : ℕ) :
    Set (closedBall (0 : CellModel n) 1) :=
  {x | (1 / 2 : ℝ) < ‖(x : CellModel n)‖}

/-- The fixed-width collar is open relative to the closed cell. -/
theorem isOpen_cellBoundaryCollar (n : ℕ) :
    IsOpen (cellBoundaryCollar n) := by
  exact isOpen_lt continuous_const
    (continuous_norm.comp continuous_subtype_val)

/-- Inclusion of the sup-norm cell boundary in its outer collar. -/
def cellBoundaryCollarInclusion (n : ℕ) :
    C(sphere (0 : CellModel n) 1, cellBoundaryCollar n) where
  toFun x := by
    have hxball : (x : CellModel n) ∈ closedBall (0 : CellModel n) 1 :=
      Metric.sphere_subset_closedBall x.2
    exact ⟨⟨(x : CellModel n), hxball⟩, by
      have hx := x.2
      rw [mem_sphere, dist_zero_right] at hx
      change (1 / 2 : ℝ) < ‖(x : CellModel n)‖
      rw [hx]
      norm_num⟩
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem cellBoundaryCollar_norm_pos {n : ℕ}
    (x : cellBoundaryCollar n) : 0 < ‖((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)‖ :=
  (by norm_num : (0 : ℝ) < 1 / 2).trans x.2

private theorem continuous_cellBoundaryCollar_normalize (n : ℕ) :
    Continuous (fun x : cellBoundaryCollar n ↦
      NormedSpace.normalize
        ((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)) := by
  let v : cellBoundaryCollar n → CellModel n := fun x ↦
    ((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)
  have hv : Continuous v :=
    continuous_subtype_val.comp continuous_subtype_val
  have hnorm : Continuous (fun x : cellBoundaryCollar n ↦ ‖v x‖) := hv.norm
  have hinv : Continuous (fun x : cellBoundaryCollar n ↦ ‖v x‖⁻¹) :=
    hnorm.inv₀ fun x ↦ (cellBoundaryCollar_norm_pos x).ne'
  exact (hinv.smul hv).congr fun x ↦ by
    change ‖v x‖⁻¹ • v x = NormedSpace.normalize (v x)
    rfl

/-- Radial normalization retracts the collar onto the sup-norm cell boundary. -/
def cellBoundaryCollarRetraction (n : ℕ) :
    C(cellBoundaryCollar n, sphere (0 : CellModel n) 1) where
  toFun x :=
    ⟨NormedSpace.normalize
        ((x.1 : closedBall (0 : CellModel n) 1) : CellModel n), by
      rw [mem_sphere, dist_zero_right]
      exact NormedSpace.norm_normalize
        (norm_pos_iff.mp (cellBoundaryCollar_norm_pos x))⟩
  continuous_toFun :=
    (continuous_cellBoundaryCollar_normalize n).subtype_mk _

@[simp]
theorem cellBoundaryCollarRetraction_inclusion (n : ℕ)
    (x : sphere (0 : CellModel n) 1) :
    cellBoundaryCollarRetraction n (cellBoundaryCollarInclusion n x) = x := by
  apply Subtype.ext
  change NormedSpace.normalize (x : CellModel n) = (x : CellModel n)
  apply NormedSpace.normalize_eq_self_of_norm_eq_one
  have hx := x.2
  rw [mem_sphere, dist_zero_right] at hx
  exact hx

private def clippedAffineTime (start finish : I) (t : I) : ℝ :=
  max 0 (min 1
    (((t : ℝ) - (start : ℝ)) / ((finish : ℝ) - (start : ℝ))))

private theorem clippedAffineTime_nonneg (start finish t : I) :
    0 ≤ clippedAffineTime start finish t :=
  le_max_left _ _

private theorem clippedAffineTime_le_one (start finish t : I) :
    clippedAffineTime start finish t ≤ 1 := by
  apply max_le (by norm_num)
  exact min_le_left _ _

/-- The affine progress through the interval from `start` to `finish`, clipped
to the unit interval. -/
def cellBoundaryCollarSchedule (start finish : I) : C(I, I) where
  toFun t :=
    ⟨clippedAffineTime start finish t,
      clippedAffineTime_nonneg start finish t,
      clippedAffineTime_le_one start finish t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.max <|
      continuous_const.min <|
        (continuous_subtype_val.sub continuous_const).div_const _

private theorem cellBoundaryCollarSchedule_eq_zero
    {start finish t : I} (hstartFinish : (start : ℝ) < finish)
    (ht : (t : ℝ) ≤ start) :
    cellBoundaryCollarSchedule start finish t = 0 := by
  apply Subtype.ext
  change clippedAffineTime start finish t = 0
  have hden : 0 < (finish : ℝ) - start := sub_pos.mpr hstartFinish
  have hq : ((t : ℝ) - start) / ((finish : ℝ) - start) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hden.le
  rw [clippedAffineTime, min_eq_right (hq.trans (by norm_num)), max_eq_left hq]

private theorem cellBoundaryCollarSchedule_eq_one
    {start finish t : I} (hstartFinish : (start : ℝ) < finish)
    (ht : (finish : ℝ) ≤ t) :
    cellBoundaryCollarSchedule start finish t = 1 := by
  apply Subtype.ext
  change clippedAffineTime start finish t = 1
  have hden : 0 < (finish : ℝ) - start := sub_pos.mpr hstartFinish
  have hq : (1 : ℝ) ≤
      ((t : ℝ) - start) / ((finish : ℝ) - start) := by
    rw [le_div_iff₀ hden]
    linarith
  rw [clippedAffineTime, min_eq_left hq]
  simp

private def cellBoundaryRadialPoint {n : ℕ} (s : I)
    (x : cellBoundaryCollar n) : CellModel n :=
  (1 - (s : ℝ)) •
      ((x.1 : closedBall (0 : CellModel n) 1) : CellModel n) +
    (s : ℝ) • NormedSpace.normalize
      ((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)

private theorem norm_cellBoundaryRadialPoint {n : ℕ} (s : I)
    (x : cellBoundaryCollar n) :
    ‖cellBoundaryRadialPoint s x‖ =
      (1 - (s : ℝ)) *
          ‖((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)‖ +
        (s : ℝ) := by
  let v : CellModel n :=
    ((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)
  have hv : 0 < ‖v‖ := cellBoundaryCollar_norm_pos x
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have hfactor : 0 ≤ (1 - (s : ℝ)) + (s : ℝ) * ‖v‖⁻¹ :=
    add_nonneg (sub_nonneg.mpr hs1)
      (mul_nonneg hs0 (inv_nonneg.mpr (norm_nonneg v)))
  change ‖(1 - (s : ℝ)) • v +
    (s : ℝ) • NormedSpace.normalize v‖ =
      (1 - (s : ℝ)) * ‖v‖ + (s : ℝ)
  rw [NormedSpace.normalize, smul_smul, ← add_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hfactor]
  field_simp

private theorem cellBoundaryRadialPoint_mem_closedBall {n : ℕ}
    (s : I) (x : cellBoundaryCollar n) :
    cellBoundaryRadialPoint s x ∈ closedBall (0 : CellModel n) 1 := by
  rw [mem_closedBall, dist_zero_right, norm_cellBoundaryRadialPoint]
  have hx :
      ‖((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)‖ ≤ 1 := by
    have hx' := x.1.2
    rw [mem_closedBall, dist_zero_right] at hx'
    exact hx'
  nlinarith [mul_nonneg (sub_nonneg.mpr s.2.2) (sub_nonneg.mpr hx)]

private theorem cellBoundaryRadialPoint_mem_collar {n : ℕ}
    (s : I) (x : cellBoundaryCollar n) :
    (1 / 2 : ℝ) < ‖cellBoundaryRadialPoint s x‖ := by
  rw [norm_cellBoundaryRadialPoint]
  have hxle :
      ‖((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)‖ ≤ 1 := by
    have hx' := x.1.2
    rw [mem_closedBall, dist_zero_right] at hx'
    exact hx'
  have hnonneg : 0 ≤ (s : ℝ) *
      (1 - ‖((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)‖) :=
    mul_nonneg s.2.1 (sub_nonneg.mpr hxle)
  have hid :
      (1 - (s : ℝ)) *
          ‖((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)‖ +
        (s : ℝ) =
      ‖((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)‖ +
        (s : ℝ) *
          (1 - ‖((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)‖) := by
    ring
  rw [hid]
  exact x.2.trans_le (le_add_of_nonneg_right hnonneg)

private def cellBoundaryRadialDeformation (n : ℕ) :
    C(I × cellBoundaryCollar n, cellBoundaryCollar n) where
  toFun p :=
    ⟨⟨cellBoundaryRadialPoint p.1 p.2,
        cellBoundaryRadialPoint_mem_closedBall p.1 p.2⟩,
      cellBoundaryRadialPoint_mem_collar p.1 p.2⟩
  continuous_toFun := by
    let v : I × cellBoundaryCollar n → CellModel n := fun p ↦
      ((p.2.1 : closedBall (0 : CellModel n) 1) : CellModel n)
    have hs : Continuous (fun p : I × cellBoundaryCollar n ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hv : Continuous v :=
      continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd)
    have hnorm : Continuous (fun p : I × cellBoundaryCollar n ↦ ‖v p‖) := hv.norm
    have hinv : Continuous (fun p : I × cellBoundaryCollar n ↦ ‖v p‖⁻¹) :=
      hnorm.inv₀ fun p ↦ (cellBoundaryCollar_norm_pos p.2).ne'
    have hnormalize : Continuous (fun p : I × cellBoundaryCollar n ↦
        NormedSpace.normalize (v p)) := by
      exact (hinv.smul hv).congr fun p ↦ by
        change ‖v p‖⁻¹ • v p = NormedSpace.normalize (v p)
        rfl
    exact (((continuous_const.sub hs).smul hv).add (hs.smul hnormalize)).subtype_mk _
      |>.subtype_mk _

/-- The fixed-width radial deformation of a closed cell's boundary collar,
scheduled during the nondegenerate interval from `start` to `finish`.

Before `start` it is the identity.  From `finish` onward it is radial
normalization, and it fixes the boundary at every time. -/
def cellBoundaryCollarDeformation (n : ℕ) (start finish : I)
    (_hstartFinish : (start : ℝ) < finish) :
    C(I × cellBoundaryCollar n, cellBoundaryCollar n) :=
  (cellBoundaryRadialDeformation n).comp
    ⟨fun p ↦ (cellBoundaryCollarSchedule start finish p.1, p.2),
      (cellBoundaryCollarSchedule start finish).continuous.comp continuous_fst
        |>.prodMk continuous_snd⟩

/-- The scheduled collar deformation follows the radial coordinate linearly. -/
theorem norm_cellBoundaryCollarDeformation (n : ℕ)
    (start finish : I) (hstartFinish : (start : ℝ) < finish)
    (t : I) (x : cellBoundaryCollar n) :
    ‖(((cellBoundaryCollarDeformation n start finish hstartFinish (t, x)).1 :
        closedBall (0 : CellModel n) 1) : CellModel n)‖ =
      (1 - ((cellBoundaryCollarSchedule start finish t : I) : ℝ)) *
          ‖((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)‖ +
        ((cellBoundaryCollarSchedule start finish t : I) : ℝ) := by
  exact norm_cellBoundaryRadialPoint (cellBoundaryCollarSchedule start finish t) x

/-- The scheduled deformation is the identity before its assigned interval. -/
theorem cellBoundaryCollarDeformation_eq_self_of_le (n : ℕ)
    {start finish t : I} (hstartFinish : (start : ℝ) < finish)
    (ht : (t : ℝ) ≤ start) (x : cellBoundaryCollar n) :
    cellBoundaryCollarDeformation n start finish hstartFinish (t, x) = x := by
  rw [cellBoundaryCollarDeformation]
  change cellBoundaryRadialDeformation n
      (cellBoundaryCollarSchedule start finish t, x) = x
  rw [cellBoundaryCollarSchedule_eq_zero hstartFinish ht]
  apply Subtype.ext
  apply Subtype.ext
  simp [cellBoundaryRadialDeformation, cellBoundaryRadialPoint]

/-- At global time zero, the scheduled collar deformation is the identity. -/
@[simp]
theorem cellBoundaryCollarDeformation_zero (n : ℕ)
    {start finish : I} (hstartFinish : (start : ℝ) < finish)
    (x : cellBoundaryCollar n) :
    cellBoundaryCollarDeformation n start finish hstartFinish (0, x) = x :=
  cellBoundaryCollarDeformation_eq_self_of_le n hstartFinish start.2.1 x

/-- From the end of its assigned interval onward, the scheduled deformation
is stationary at radial normalization on the boundary. -/
theorem cellBoundaryCollarDeformation_eq_retraction_of_le (n : ℕ)
    {start finish t : I} (hstartFinish : (start : ℝ) < finish)
    (ht : (finish : ℝ) ≤ t) (x : cellBoundaryCollar n) :
    cellBoundaryCollarDeformation n start finish hstartFinish (t, x) =
      cellBoundaryCollarInclusion n (cellBoundaryCollarRetraction n x) := by
  rw [cellBoundaryCollarDeformation]
  change cellBoundaryRadialDeformation n
      (cellBoundaryCollarSchedule start finish t, x) = _
  rw [cellBoundaryCollarSchedule_eq_one hstartFinish ht]
  apply Subtype.ext
  apply Subtype.ext
  simp [cellBoundaryRadialDeformation, cellBoundaryRadialPoint,
    cellBoundaryCollarInclusion, cellBoundaryCollarRetraction]

/-- At global time one, the scheduled collar deformation has reached radial
normalization on the boundary. -/
@[simp]
theorem cellBoundaryCollarDeformation_one (n : ℕ)
    {start finish : I} (hstartFinish : (start : ℝ) < finish)
    (x : cellBoundaryCollar n) :
    cellBoundaryCollarDeformation n start finish hstartFinish (1, x) =
      cellBoundaryCollarInclusion n (cellBoundaryCollarRetraction n x) :=
  cellBoundaryCollarDeformation_eq_retraction_of_le n hstartFinish finish.2.2 x

/-- The scheduled collar deformation fixes every boundary point at every
time. -/
theorem cellBoundaryCollarDeformation_boundary (n : ℕ)
    (start finish : I) (hstartFinish : (start : ℝ) < finish)
    (t : I) (x : sphere (0 : CellModel n) 1) :
    cellBoundaryCollarDeformation n start finish hstartFinish
        (t, cellBoundaryCollarInclusion n x) =
      cellBoundaryCollarInclusion n x := by
  apply Subtype.ext
  apply Subtype.ext
  have hx := x.2
  rw [mem_sphere, dist_zero_right] at hx
  change cellBoundaryRadialPoint
      (cellBoundaryCollarSchedule start finish t)
      (cellBoundaryCollarInclusion n x) = (x : CellModel n)
  change
    (1 - (((cellBoundaryCollarSchedule start finish) t : I) : ℝ)) •
        (x : CellModel n) +
      (((cellBoundaryCollarSchedule start finish) t : I) : ℝ) •
        NormedSpace.normalize (x : CellModel n) = (x : CellModel n)
  rw [NormedSpace.normalize_eq_self_of_norm_eq_one hx, ← add_smul]
  simp

end Hatcher.ClassicalCW
