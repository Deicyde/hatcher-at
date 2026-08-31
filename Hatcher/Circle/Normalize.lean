import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Path

open Metric Set unitInterval

namespace Hatcher.Circle

/-- Radial projection from the punctured complex plane to the unit circle. -/
noncomputable def radialProjection : C(({0}ᶜ : Set ℂ), _root_.Circle) :=
  ⟨fun z => ((homeomorphUnitSphereProd ℂ) z).1,
    continuous_fst.comp (homeomorphUnitSphereProd ℂ).continuous⟩

@[simp]
theorem coe_radialProjection (z : ({0}ᶜ : Set ℂ)) :
    ((radialProjection z : _root_.Circle) : ℂ) = ‖(z : ℂ)‖⁻¹ • (z : ℂ) :=
  homeomorphUnitSphereProd_apply_fst_coe ℂ z

@[simp]
theorem radialProjection_one : radialProjection ⟨1, by simp⟩ = (1 : _root_.Circle) := by
  apply _root_.Circle.coe_injective
  simp

/-- Restrict a two-parameter continuous map to one value of its first parameter. -/
noncomputable def familySlice (F : C(I × I, ℂ)) (t : I) : C(I, ℂ) where
  toFun s := F (t, s)
  continuous_toFun := by fun_prop

/-- Turn a nonvanishing periodic complex-valued path into a circle loop based at one. -/
noncomputable def normalizedLoop (f : C(I, ℂ)) (hf : ∀ s, f s ≠ 0)
    (hperiodic : f 1 = f 0) : Path (1 : _root_.Circle) 1 where
  toFun s := radialProjection ⟨f s / f 0, div_ne_zero (hf s) (hf 0)⟩
  continuous_toFun := radialProjection.continuous.comp <|
    Continuous.subtype_mk (f.continuous.div continuous_const fun _ => hf 0) _
  source' := by
    apply _root_.Circle.coe_injective
    rw [coe_radialProjection]
    simp [hf 0]
  target' := by
    apply _root_.Circle.coe_injective
    rw [coe_radialProjection]
    simp [hperiodic, hf 0]

@[simp]
theorem coe_normalizedLoop (f : C(I, ℂ)) (hf : ∀ s, f s ≠ 0)
    (hperiodic : f 1 = f 0) (s : I) :
    ((normalizedLoop f hf hperiodic s : _root_.Circle) : ℂ) =
      ‖f s / f 0‖⁻¹ • (f s / f 0) :=
  coe_radialProjection _

/-- The based loop obtained by radially projecting one slice of a nonvanishing,
periodic family of complex-valued maps. -/
noncomputable def normalizedLoopFamily (F : C(I × I, ℂ))
    (hF : ∀ x, F x ≠ 0) (hperiodic : ∀ t, F (t, 1) = F (t, 0)) (t : I) :
    Path (1 : _root_.Circle) 1 :=
  normalizedLoop (familySlice F t) (fun s => hF (t, s)) (hperiodic t)

@[simp]
theorem coe_normalizedLoopFamily (F : C(I × I, ℂ))
    (hF : ∀ x, F x ≠ 0) (hperiodic : ∀ t, F (t, 1) = F (t, 0)) (t s : I) :
    ((normalizedLoopFamily F hF hperiodic t s : _root_.Circle) : ℂ) =
      ‖F (t, s) / F (t, 0)‖⁻¹ • (F (t, s) / F (t, 0)) :=
  coe_normalizedLoop _ _ _ _

/-- Radial projection turns a nonvanishing periodic family into a based path
homotopy between its endpoint loops. -/
noncomputable def normalizedLoopHomotopy (F : C(I × I, ℂ))
    (hF : ∀ x, F x ≠ 0) (hperiodic : ∀ t, F (t, 1) = F (t, 0)) :
    Path.Homotopy (normalizedLoopFamily F hF hperiodic 0)
      (normalizedLoopFamily F hF hperiodic 1) where
  toFun x := radialProjection
    ⟨F x / F (x.1, 0), div_ne_zero (hF x) (hF (x.1, 0))⟩
  continuous_toFun := radialProjection.continuous.comp <|
    Continuous.subtype_mk (F.continuous.div (F.continuous.comp <| by fun_prop)
      fun x => hF (x.1, 0)) _
  map_zero_left _ := rfl
  map_one_left _ := rfl
  prop' t s hs := by
    rcases hs with rfl | hs
    · calc
        radialProjection ⟨F (t, 0) / F (t, 0), _⟩ = 1 := by
          apply _root_.Circle.coe_injective
          rw [coe_radialProjection]
          simp [hF (t, 0)]
        _ = normalizedLoopFamily F hF hperiodic 0 0 :=
          (normalizedLoopFamily F hF hperiodic 0).source.symm
    · rw [Set.mem_singleton_iff] at hs
      subst s
      calc
        radialProjection ⟨F (t, 1) / F (t, 0), _⟩ = 1 := by
          apply _root_.Circle.coe_injective
          rw [coe_radialProjection]
          simp [hperiodic t, hF (t, 0)]
        _ = normalizedLoopFamily F hF hperiodic 0 1 :=
          (normalizedLoopFamily F hF hperiodic 0).target.symm

end Hatcher.Circle
