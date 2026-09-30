/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Topology.StrongDeformationRetract
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Radial deformation retraction onto a closed ball

For a positive radius, radial clamping gives a strong deformation retraction
of a real normed vector space onto the closed ball centered at the origin.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Hatcher.Sphere

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def closedBallRadialFactor (r : ℝ) (x : E) : ℝ :=
  r / max r ‖x‖

omit [NormedSpace ℝ E] in
private theorem continuous_closedBallRadialFactor (r : ℝ) (hr : 0 < r) :
    Continuous (closedBallRadialFactor (E := E) r) := by
  exact continuous_const.div (continuous_const.max continuous_norm) fun x ↦
    (hr.trans_le (le_max_left r ‖x‖)).ne'

private def closedBallRadialClamp (r : ℝ) (x : E) : E :=
  closedBallRadialFactor r x • x

private theorem continuous_closedBallRadialClamp (r : ℝ) (hr : 0 < r) :
    Continuous (closedBallRadialClamp (E := E) r) :=
  (continuous_closedBallRadialFactor r hr).smul continuous_id

private theorem closedBallRadialClamp_mem (r : ℝ) (hr : 0 < r) (x : E) :
    closedBallRadialClamp r x ∈ Metric.closedBall (0 : E) r := by
  have hd : 0 < max r ‖x‖ := hr.trans_le (le_max_left r ‖x‖)
  have hf : 0 ≤ r / max r ‖x‖ := div_nonneg hr.le hd.le
  rw [Metric.mem_closedBall, dist_zero_right, closedBallRadialClamp,
    closedBallRadialFactor, norm_smul, Real.norm_eq_abs, abs_of_nonneg hf]
  calc
    r / max r ‖x‖ * ‖x‖ ≤ r / max r ‖x‖ * max r ‖x‖ :=
      mul_le_mul_of_nonneg_left (le_max_right r ‖x‖) hf
    _ = r := div_mul_cancel₀ r hd.ne'

private theorem closedBallRadialClamp_eq_self (r : ℝ) (hr : 0 < r)
    {x : E} (hx : x ∈ Metric.closedBall (0 : E) r) :
    closedBallRadialClamp r x = x := by
  have hx' : ‖x‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  simp [closedBallRadialClamp, closedBallRadialFactor, max_eq_left hx', hr.ne']

private def closedBallRadialRetraction (r : ℝ) (hr : 0 < r) :
    C(E, Metric.closedBall (0 : E) r) where
  toFun x := ⟨closedBallRadialClamp r x, closedBallRadialClamp_mem r hr x⟩
  continuous_toFun := (continuous_closedBallRadialClamp r hr).subtype_mk _

private def closedBallRadialDeformationMap (r : ℝ) : I × E → E :=
  fun p ↦ (1 - (p.1 : ℝ)) • p.2 + (p.1 : ℝ) • closedBallRadialClamp r p.2

private theorem continuous_closedBallRadialDeformationMap (r : ℝ) (hr : 0 < r) :
    Continuous (closedBallRadialDeformationMap (E := E) r) := by
  exact
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul continuous_snd
      |>.add ((continuous_subtype_val.comp continuous_fst).smul
        ((continuous_closedBallRadialClamp r hr).comp continuous_snd))

private def closedBallRadialDeformation (r : ℝ) (hr : 0 < r) :
    (ContinuousMap.id E).HomotopyRel
      ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(Metric.closedBall (0 : E) r, E)).comp
        (closedBallRadialRetraction r hr))
      (Set.range (⟨Subtype.val, continuous_subtype_val⟩ :
        C(Metric.closedBall (0 : E) r, E))) where
  toFun := closedBallRadialDeformationMap r
  continuous_toFun := continuous_closedBallRadialDeformationMap r hr
  map_zero_left x := by
    simp [closedBallRadialDeformationMap]
  map_one_left x := by
    simp [closedBallRadialDeformationMap, closedBallRadialRetraction]
  prop' t x hx := by
    obtain ⟨y, rfl⟩ := hx
    change closedBallRadialDeformationMap r (t, (y : E)) = (y : E)
    rw [closedBallRadialDeformationMap,
      closedBallRadialClamp_eq_self r hr y.2]
    simp [← add_smul]

/-- For every positive radius, radial clamping is a strong deformation
retraction of a real normed vector space onto the closed ball centered at the
origin, along the canonical subtype inclusion. -/
def closedBallStrongDeformationRetract (r : ℝ) (hr : 0 < r) :
    Hatcher.StrongDeformationRetract
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(Metric.closedBall (0 : E) r, E)) where
  retract := closedBallRadialRetraction r hr
  retract_inclusion := by
    ext x
    exact closedBallRadialClamp_eq_self r hr x.2
  deformation := closedBallRadialDeformation r hr

end Hatcher.Sphere
