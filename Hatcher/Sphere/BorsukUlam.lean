/-
Hatcher, *Algebraic Topology*, Theorem 1.10 (pages 32–33).

The proof follows Hatcher's winding-number obstruction. Assuming that
`f x ≠ f (-x)` everywhere, normalize `f x - f (-x)` to obtain an odd map
from `S²` to `S¹`. Instead of choosing a coordinate equator, choose any path
from `x` to `-x` and follow it by its antipodal image. This is the same
equatorial geometry without coordinate bookkeeping. The resulting loop is
nullhomotopic because `S²` is simply connected, but its winding number is odd.
-/
import Hatcher.Circle.Normalize
import Hatcher.Circle.OddWinding
import Hatcher.Sphere.SimplyConnected

open Fin Function Path Set unitInterval
open scoped EuclideanSpace

namespace Hatcher.Sphere

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private theorem exists_eq_neg_complex (f : C(S2, ℂ)) : ∃ x, f x = f (-x) := by
  by_contra! h
  let d : C(S2, ℂ) := ⟨fun x => f x - f (-x), by fun_prop⟩
  have hd (x : S2) : d x ≠ 0 := sub_ne_zero.mpr (h x)
  have hdneg (x : S2) : d (-x) = -d x := by
    simp [d]
  let x0 : S2 := Classical.choice (inferInstance : Nonempty S2)
  let G : C(S2, _root_.Circle) :=
    ⟨fun x => Hatcher.Circle.radialProjection
        ⟨d x / d x0, div_ne_zero (hd x) (hd x0)⟩,
      Hatcher.Circle.radialProjection.continuous.comp <|
        Continuous.subtype_mk (d.continuous.div continuous_const fun _ => hd x0) _⟩
  have hG0 : G x0 = (1 : _root_.Circle) := by
    apply _root_.Circle.coe_injective
    rw [show ((G x0 : _root_.Circle) : ℂ) =
      ‖d x0 / d x0‖⁻¹ • (d x0 / d x0) by
        exact Hatcher.Circle.coe_radialProjection _]
    simp [hd x0]
  have hGneg (x : S2) : G (-x) = -G x := by
    apply _root_.Circle.coe_injective
    change ((G (-x) : _root_.Circle) : ℂ) = -((G x : _root_.Circle) : ℂ)
    rw [show ((G (-x) : _root_.Circle) : ℂ) =
      ‖d (-x) / d x0‖⁻¹ • (d (-x) / d x0) by
        exact Hatcher.Circle.coe_radialProjection _]
    rw [show ((G x : _root_.Circle) : ℂ) =
      ‖d x / d x0‖⁻¹ • (d x / d x0) by
        exact Hatcher.Circle.coe_radialProjection _]
    rw [hdneg]
    simp
    ring
  have hGneg0 : G (-x0) = (-1 : _root_.Circle) := by
    rw [hGneg, hG0]
  let α : Path x0 (-x0) := PathConnectedSpace.somePath x0 (-x0)
  let negS : C(S2, S2) := ⟨fun x => -x, by fun_prop⟩
  let β : Path (-x0) x0 :=
    (α.map negS.continuous).cast rfl (by simp [negS])
  have hβ (t : I) : β t = -α t := by
    rfl
  let a : Path (1 : _root_.Circle) (-1) :=
    (α.map G.continuous).cast hG0.symm hGneg0.symm
  let b : Path (-1 : _root_.Circle) 1 :=
    (β.map G.continuous).cast hGneg0.symm hG0.symm
  have hab (t : I) : b t = -a t := by
    change G (β t) = -G (α t)
    rw [hβ]
    exact hGneg (α t)
  let γ : Path x0 x0 := α.trans β
  have hγ : γ.Homotopic (Path.refl x0) :=
    (simply_connected_iff_loops_nullhomotopic.mp
      (Hatcher.Sphere.simplyConnectedSpace 0)).right x0 γ
  have hmap := Path.Homotopic.map hγ G
  have hleft :
      (γ.map G.continuous).cast hG0.symm hG0.symm = a.trans b := by
    ext t
    simp [γ, a, b]
    rfl
  have hright :
      ((Path.refl x0).map G.continuous).cast hG0.symm hG0.symm =
        Path.refl (1 : _root_.Circle) := by
    ext t
    simp [hG0]
  have hnull : (a.trans b).Homotopic (Path.refl (1 : _root_.Circle)) := by
    rw [← hleft, ← hright]
    exact hmap.pathCast hG0.symm hG0.symm
  have hnonzero :=
    Hatcher.Circle.windingNumberFun_ne_zero_of_antipodal_halves a b hab
  have hq :
      Path.Homotopic.Quotient.mk (a.trans b) =
        Path.Homotopic.Quotient.mk (Path.refl (1 : _root_.Circle)) :=
    Path.Homotopic.Quotient.eq.mpr hnull
  have hw := congr_arg
    (fun q : Path.Homotopic.Quotient (1 : _root_.Circle) 1 =>
      Hatcher.Circle.windingNumberFun (FundamentalGroup.fromPath q)) hq
  apply hnonzero
  calc
    Hatcher.Circle.windingNumberFun
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a.trans b))) =
      Hatcher.Circle.windingNumberFun
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (Path.refl (1 : _root_.Circle)))) := hw
    _ = 0 := by
      change Hatcher.Circle.windingNumberFun
        (1 : FundamentalGroup _root_.Circle 1) = 0
      exact Hatcher.Circle.windingNumberFun_one

/-- **Hatcher, Theorem 1.10 (pages 32–33).** Every continuous map from the
two-sphere to the real plane identifies an antipodal pair. -/
theorem exists_eq_neg (f : C(S2, EuclideanSpace ℝ (Fin 2))) :
    ∃ x, f x = f (-x) := by
  let fComplex : C(S2, ℂ) :=
    ⟨fun x => Complex.orthonormalBasisOneI.repr.symm (f x), by fun_prop⟩
  obtain ⟨x, hx⟩ := exists_eq_neg_complex fComplex
  refine ⟨x, ?_⟩
  exact Complex.orthonormalBasisOneI.repr.symm.injective hx

end Hatcher.Sphere
