/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Topology.StrongDeformationRetract
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

/-!
# Radial deformation retractions

For a positive radius, radial clamping gives a strong deformation retraction
of a real normed vector space onto the closed ball centered at the origin.
Radial normalization similarly retracts the punctured space onto the sphere.
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

/-- The canonical inclusion of a positive-radius sphere into the punctured
ambient normed space. -/
noncomputable def spherePuncturedInclusion (r : ℝ) (hr : 0 < r) :
    C(Metric.sphere (0 : E) r, ({0}ᶜ : Set E)) :=
  ContinuousMap.inclusion fun x hx ↦ by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hzero
    subst x
    have : (0 : ℝ) = r := by
      simpa [Metric.mem_sphere, dist_zero_right] using hx
    exact hr.ne' this.symm

private noncomputable def spherePuncturedRadialRetraction (r : ℝ) (hr : 0 < r) :
    C(({0}ᶜ : Set E), Metric.sphere (0 : E) r) :=
  ContinuousMap.fst.comp
    ⟨homeomorphSphereProd E r hr, (homeomorphSphereProd E r hr).continuous⟩

@[simp]
private theorem homeomorphSphereProd_spherePuncturedInclusion
    (r : ℝ) (hr : 0 < r) (x : Metric.sphere (0 : E) r) :
    homeomorphSphereProd E r hr (spherePuncturedInclusion r hr x) =
      (x, (⟨1, by simp⟩ : Set.Ioi (0 : ℝ))) := by
  have hxnorm : ‖(x : E)‖ = r := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.2
  have hinclusion :
      ((spherePuncturedInclusion (E := E) r hr x : ({0}ᶜ : Set E)) : E) =
        (x : E) := rfl
  apply Prod.ext
  · apply Subtype.ext
    rw [homeomorphSphereProd_apply_fst_coe, hinclusion, hxnorm]
    simp [hr.ne']
  · apply Subtype.ext
    rw [homeomorphSphereProd_apply_snd_coe, hinclusion, hxnorm]
    exact div_self hr.ne'

@[simp]
private theorem spherePuncturedRadialRetraction_inclusion
    (r : ℝ) (hr : 0 < r) :
    (spherePuncturedRadialRetraction (E := E) r hr).comp
        (spherePuncturedInclusion r hr) =
      ContinuousMap.id (Metric.sphere (0 : E) r) := by
  ext x
  exact congrArg Subtype.val <| congrArg Prod.fst <|
    homeomorphSphereProd_spherePuncturedInclusion (E := E) r hr x

private def puncturedRadialRadius (r : ℝ) (hr : 0 < r)
    (p : I × ({0}ᶜ : Set E)) : Set.Ioi (0 : ℝ) :=
  ⟨(1 - (p.1 : ℝ)) *
        ((homeomorphSphereProd E r hr p.2).2 : ℝ) + (p.1 : ℝ), by
    rcases eq_or_lt_of_le p.1.2.1 with ht | ht
    · simpa [← ht] using (homeomorphSphereProd E r hr p.2).2.2
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr p.1.2.2)
          (homeomorphSphereProd E r hr p.2).2.2.le) ht⟩

private theorem continuous_puncturedRadialRadius (r : ℝ) (hr : 0 < r) :
    Continuous (puncturedRadialRadius (E := E) r hr) := by
  have ht : Continuous (fun p : I × ({0}ᶜ : Set E) ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hdIoi : Continuous (fun p : I × ({0}ᶜ : Set E) ↦
      (homeomorphSphereProd E r hr p.2).2) :=
    ((homeomorphSphereProd E r hr).continuous.comp continuous_snd).snd
  have hd : Continuous (fun p : I × ({0}ᶜ : Set E) ↦
      ((homeomorphSphereProd E r hr p.2).2 : ℝ)) :=
    continuous_subtype_val.comp hdIoi
  exact ((continuous_const.sub ht).mul hd).add ht |>.subtype_mk _

private def spherePuncturedRadialDeformationMap (r : ℝ) (hr : 0 < r) :
    I × ({0}ᶜ : Set E) → ({0}ᶜ : Set E) := fun p ↦
  (homeomorphSphereProd E r hr).symm
    ((homeomorphSphereProd E r hr p.2).1,
      puncturedRadialRadius r hr p)

private theorem continuous_spherePuncturedRadialDeformationMap
    (r : ℝ) (hr : 0 < r) :
    Continuous (spherePuncturedRadialDeformationMap (E := E) r hr) := by
  apply (homeomorphSphereProd E r hr).symm.continuous.comp
  exact Continuous.prodMk
    (((homeomorphSphereProd E r hr).continuous.comp continuous_snd).fst)
    (continuous_puncturedRadialRadius r hr)

private def spherePuncturedRadialDeformation (r : ℝ) (hr : 0 < r) :
    (ContinuousMap.id (({0}ᶜ : Set E))).HomotopyRel
      ((spherePuncturedInclusion r hr).comp
        (spherePuncturedRadialRetraction r hr))
      (Set.range (spherePuncturedInclusion r hr)) where
  toFun := spherePuncturedRadialDeformationMap r hr
  continuous_toFun := continuous_spherePuncturedRadialDeformationMap r hr
  map_zero_left x := by
    apply (homeomorphSphereProd E r hr).injective
    simp only [spherePuncturedRadialDeformationMap,
      Homeomorph.apply_symm_apply]
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [puncturedRadialRadius]
  map_one_left x := by
    apply (homeomorphSphereProd E r hr).injective
    simp only [spherePuncturedRadialDeformationMap,
      Homeomorph.apply_symm_apply, ContinuousMap.comp_apply]
    rw [homeomorphSphereProd_spherePuncturedInclusion]
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [puncturedRadialRadius]
  prop' t x hx := by
    obtain ⟨y, rfl⟩ := hx
    change spherePuncturedRadialDeformationMap r hr
        (t, spherePuncturedInclusion r hr y) =
      spherePuncturedInclusion r hr y
    apply (homeomorphSphereProd E r hr).injective
    simp only [spherePuncturedRadialDeformationMap,
      Homeomorph.apply_symm_apply]
    rw [homeomorphSphereProd_spherePuncturedInclusion]
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [puncturedRadialRadius]

/-- For every positive radius, normalization gives a strong deformation
retraction of the punctured ambient real normed vector space onto the sphere,
along the canonical subtype inclusion. -/
noncomputable def spherePuncturedStrongDeformationRetract [Nontrivial E]
    (r : ℝ) (hr : 0 < r) :
    Hatcher.StrongDeformationRetract (spherePuncturedInclusion (E := E) r hr) where
  retract := spherePuncturedRadialRetraction r hr
  retract_inclusion := spherePuncturedRadialRetraction_inclusion r hr
  deformation := spherePuncturedRadialDeformation r hr

end Hatcher.Sphere
