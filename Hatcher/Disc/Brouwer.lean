/-
Hatcher, *Algebraic Topology*, Theorem 1.9 (pages 31–32).

Every continuous `h : D² → D²` has a fixed point.

Hatcher's proof: if `h x ≠ x` everywhere, send `x` to the point where the ray
from `h x` through `x` meets `S¹`. That is a retraction of `D²` onto `S¹`, and
`Hatcher.Disc.not_exists_retraction` says none exists.

The topology is already discharged by the no-retraction node, so what is left
here is the ray construction: solving a quadratic for the parameter, checking
the root is continuous, and checking it vanishes on the boundary so the map
really does fix `S¹` pointwise.
-/
import Hatcher.Disc.NoRetraction

open Real

namespace Hatcher.Disc

/-- The real inner product of two complex numbers, `⟪a, b⟫ = Re(a * conj b)`. -/
private noncomputable def ip (a b : ℂ) : ℝ := a.re * b.re + a.im * b.im

private theorem ip_self (a : ℂ) : ip a a = Complex.normSq a := by
  simp [ip, Complex.normSq_apply]

private theorem normSq_add_real_smul (a b : ℂ) (s : ℝ) :
    Complex.normSq (a + (s : ℂ) * b)
      = Complex.normSq a + 2 * s * ip a b + s ^ 2 * Complex.normSq b := by
  simp [Complex.normSq_apply, ip, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im]
  ring

private theorem ip_le_norm_mul (a b : ℂ) : ip a b ≤ ‖a‖ * ‖b‖ := by
  have h : ip a b = (a * (starRingEnd ℂ) b).re := by
    simp [ip, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  calc ip a b = (a * (starRingEnd ℂ) b).re := h
    _ ≤ ‖a * (starRingEnd ℂ) b‖ := Complex.re_le_norm _
    _ = ‖a‖ * ‖b‖ := by simp

/-- The algebra behind the ray: `t = (−a + s)/n` with `s² = a² + n·c` solves
`n t² + 2 a t = c`. -/
private theorem quadratic_root_identity (a n c s : ℝ) (hn : n ≠ 0)
    (hs : s ^ 2 = a ^ 2 + n * c) :
    2 * ((-a + s) / n) * a + ((-a + s) / n) ^ 2 * n = c := by
  field_simp
  linear_combination hs

/-- The quadratic root used as the parameter where the ray `x + t u` meets
the unit circle. The required disc and nonzero-direction hypotheses are supplied
by the lemmas below. -/
private noncomputable def rayRoot (x u : ℂ) : ℝ :=
  (-(ip x u) + Real.sqrt ((ip x u) ^ 2 + Complex.normSq u * (1 - Complex.normSq x)))
    / Complex.normSq u

private theorem rayRoot_discrim_nonneg (x u : ℂ) (hx : Complex.normSq x ≤ 1) :
    0 ≤ (ip x u) ^ 2 + Complex.normSq u * (1 - Complex.normSq x) := by
  have h1 : (0 : ℝ) ≤ (ip x u) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ Complex.normSq u * (1 - Complex.normSq x) :=
    mul_nonneg (Complex.normSq_nonneg u) (by linarith)
  linarith

/-- The ray really does land on the unit circle. -/
private theorem normSq_rayPoint (x u : ℂ) (hu : Complex.normSq u ≠ 0)
    (hx : Complex.normSq x ≤ 1) :
    Complex.normSq (x + (rayRoot x u : ℂ) * u) = 1 := by
  have hDnn := rayRoot_discrim_nonneg x u hx
  have hs2 : Real.sqrt ((ip x u) ^ 2 + Complex.normSq u * (1 - Complex.normSq x)) ^ 2
      = (ip x u) ^ 2 + Complex.normSq u * (1 - Complex.normSq x) := Real.sq_sqrt hDnn
  rw [normSq_add_real_smul, rayRoot]
  have key := quadratic_root_identity (ip x u) (Complex.normSq u) (1 - Complex.normSq x)
    (Real.sqrt ((ip x u) ^ 2 + Complex.normSq u * (1 - Complex.normSq x))) hu hs2
  linarith [key]

/-- On the boundary the parameter vanishes, so the map fixes `S¹` pointwise. -/
private theorem rayRoot_eq_zero_of_boundary (x u : ℂ) (hx : Complex.normSq x = 1)
    (hip : 0 ≤ ip x u) : rayRoot x u = 0 := by
  have hrw : (ip x u) ^ 2 + Complex.normSq u * (1 - Complex.normSq x) = (ip x u) ^ 2 := by
    rw [hx]; ring
  rw [rayRoot, hrw, Real.sqrt_sq hip]
  simp

private theorem ip_sub (a b c : ℂ) : ip a (b - c) = ip a b - ip a c := by
  simp [ip, Complex.sub_re, Complex.sub_im]; ring

/-- **Hatcher, Theorem 1.9 (pages 31–32).** Every continuous map `D² → D²`
has a fixed point. -/
theorem exists_fixed_point (h : C(unitDisc, unitDisc)) : ∃ x, h x = x := by
  by_contra hcon
  push Not at hcon
  -- the displacement never vanishes
  have hu : ∀ x : unitDisc, Complex.normSq ((x : ℂ) - (h x : ℂ)) ≠ 0 := by
    intro x hzero
    rw [Complex.normSq_eq_zero, sub_eq_zero] at hzero
    exact hcon x (Subtype.ext hzero.symm)
  have hnorm : ∀ x : unitDisc, ‖(x : ℂ)‖ ≤ 1 := by
    intro x
    have hx : (x : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := x.2
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact hx
  have hxle : ∀ x : unitDisc, Complex.normSq (x : ℂ) ≤ 1 := by
    intro x
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ((x : ℂ)), hnorm x]
  -- the ray retraction, as a function
  set f : unitDisc → ℂ := fun x =>
    (x : ℂ) +
      (rayRoot (x : ℂ) ((x : ℂ) - (h x : ℂ)) : ℂ) *
        ((x : ℂ) - (h x : ℂ)) with hf
  have hfnorm : ∀ x : unitDisc, ‖f x‖ = 1 := by
    intro x
    have hns := normSq_rayPoint (x : ℂ) ((x : ℂ) - (h x : ℂ)) (hu x) (hxle x)
    rw [Complex.normSq_eq_norm_sq] at hns
    nlinarith [norm_nonneg (f x), hns]
  have hcont : Continuous f := by
    have hv : Continuous fun x : unitDisc => (x : ℂ) := continuous_subtype_val
    have hw : Continuous fun x : unitDisc => (h x : ℂ) :=
      continuous_subtype_val.comp h.continuous
    have hd : Continuous fun x : unitDisc => (x : ℂ) - (h x : ℂ) := hv.sub hw
    have hipc : Continuous fun x : unitDisc => ip (x : ℂ) ((x : ℂ) - (h x : ℂ)) := by
      unfold ip; fun_prop
    have hns : Continuous fun x : unitDisc => Complex.normSq ((x : ℂ) - (h x : ℂ)) := by
      fun_prop
    have hnx : Continuous fun x : unitDisc => Complex.normSq (x : ℂ) := by fun_prop
    have hroot : Continuous fun x : unitDisc =>
        rayRoot (x : ℂ) ((x : ℂ) - (h x : ℂ)) := by
      unfold rayRoot
      exact Continuous.div
        (hipc.neg.add (((hipc.pow 2).add (hns.mul (continuous_const.sub hnx))).sqrt)) hns hu
    exact hv.add ((Complex.continuous_ofReal.comp hroot).mul hd)
  -- package it as a retraction onto the circle
  have hmem : ∀ x : unitDisc, f x ∈ Submonoid.unitSphere ℂ := by
    intro x
    show dist (f x) (0 : ℂ) = 1
    rw [dist_zero_right]; exact hfnorm x
  let r : C(unitDisc, _root_.Circle) :=
    ⟨fun x => ⟨f x, hmem x⟩, Continuous.subtype_mk hcont hmem⟩
  refine not_exists_retraction ⟨r, fun z => ?_⟩
  -- on the boundary the parameter is zero, so `r` fixes `S¹`
  have hz1 : Complex.normSq ((incl z : unitDisc) : ℂ) = 1 := by
    simp
  have hipnn : 0 ≤ ip ((incl z : unitDisc) : ℂ)
      (((incl z : unitDisc) : ℂ) - ((h (incl z) : unitDisc) : ℂ)) := by
    rw [ip_sub, ip_self, hz1]
    have := ip_le_norm_mul ((incl z : unitDisc) : ℂ) ((h (incl z) : unitDisc) : ℂ)
    have h1 : ‖((incl z : unitDisc) : ℂ)‖ = 1 := by
      simp
    have h2 : ‖((h (incl z) : unitDisc) : ℂ)‖ ≤ 1 := hnorm _
    nlinarith [this, h1, h2]
  have hroot0 : rayRoot ((incl z : unitDisc) : ℂ)
      (((incl z : unitDisc) : ℂ) - ((h (incl z) : unitDisc) : ℂ)) = 0 :=
    rayRoot_eq_zero_of_boundary _ _ hz1 hipnn
  apply Circle.coe_injective
  show f (incl z) = (z : ℂ)
  rw [hf]
  simp only [incl_coe] at hroot0 ⊢
  rw [hroot0]
  simp

end Hatcher.Disc
