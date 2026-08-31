import Hatcher.Circle.Normalize
import Hatcher.Circle.FundamentalGroup
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial

open Bornology Filter Metric Polynomial unitInterval

namespace Hatcher

private theorem leading_add_scaled_lower_ne_zero (a b : ℂ) (t : I)
    (h : ‖b‖ < ‖a‖) : a + (t : ℂ) * b ≠ 0 := by
  intro hab
  have heq : a = -((t : ℂ) * b) := eq_neg_of_add_eq_zero_left hab
  have hnorm := congr_arg norm heq
  simp only [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg t.2.1] at hnorm
  have hle : (t : ℝ) * ‖b‖ ≤ ‖b‖ := by
    nlinarith [t.2.2, norm_nonneg b]
  linarith

/-- Evaluate a polynomial along the circle of radius `R`. -/
noncomputable def polynomialCircleMap (p : ℂ[X]) (R : ℝ) : C(I, ℂ) where
  toFun s := p.eval ((R : ℂ) * (Circle.expMap s : ℂ))
  continuous_toFun := by fun_prop

@[simp]
theorem polynomialCircleMap_apply (p : ℂ[X]) (R : ℝ) (s : I) :
    polynomialCircleMap p R s = p.eval ((R : ℂ) * (Circle.expMap s : ℂ)) := rfl

@[simp]
theorem polynomialCircleMap_zero (p : ℂ[X]) (R : ℝ) :
    polynomialCircleMap p R 0 = p.eval (R : ℂ) := by
  simp [polynomialCircleMap]

@[simp]
theorem polynomialCircleMap_one (p : ℂ[X]) (R : ℝ) :
    polynomialCircleMap p R 1 = p.eval (R : ℂ) := by
  simp [polynomialCircleMap]

/-- The based circle loop obtained from a nonvanishing polynomial on a circle. -/
noncomputable def polynomialLoop (p : ℂ[X]) (hp : ∀ z, p.eval z ≠ 0) (R : ℝ) :
    Path (1 : _root_.Circle) 1 :=
  Circle.normalizedLoop (polynomialCircleMap p R) (fun s => hp _)
    (by simp)

@[simp]
theorem coe_polynomialLoop (p : ℂ[X]) (hp : ∀ z, p.eval z ≠ 0) (R : ℝ) (s : I) :
    ((polynomialLoop p hp R s : _root_.Circle) : ℂ) =
      ‖p.eval ((R : ℂ) * (Circle.expMap s : ℂ)) / p.eval (R : ℂ)‖⁻¹ •
        (p.eval ((R : ℂ) * (Circle.expMap s : ℂ)) / p.eval (R : ℂ)) := by
  rw [polynomialLoop, Circle.coe_normalizedLoop]
  rw [polynomialCircleMap_apply, polynomialCircleMap_apply]
  have he0 : ((Circle.expMap ((0 : I) : ℝ) : _root_.Circle) : ℂ) = 1 := by simp
  rw [he0, mul_one]

/-- Vary the radius of the circle on which the polynomial is evaluated. -/
noncomputable def radiusFamily (p : ℂ[X]) (R : ℝ) : C(I × I, ℂ) where
  toFun x := p.eval ((((x.1 : ℝ) * R : ℝ) : ℂ) * (Circle.expMap x.2 : ℂ))
  continuous_toFun := by fun_prop

theorem polynomialLoop_homotopic_refl (p : ℂ[X]) (hp : ∀ z, p.eval z ≠ 0) (R : ℝ) :
    (polynomialLoop p hp R).Homotopic (Path.refl 1) := by
  have hperiodic : ∀ t, radiusFamily p R (t, 1) = radiusFamily p R (t, 0) := by
    intro t
    simp [radiusFamily]
  let F := Circle.normalizedLoopHomotopy (radiusFamily p R) (fun x => hp _) hperiodic
  have hstart : Circle.normalizedLoopFamily (radiusFamily p R) (fun x => hp _)
      hperiodic 0 = Path.refl 1 := by
    ext s
    simp [Circle.normalizedLoopFamily, Circle.normalizedLoop, Circle.familySlice,
      radiusFamily, hp 0]
  have hend : Circle.normalizedLoopFamily (radiusFamily p R) (fun x => hp _)
      hperiodic 1 = polynomialLoop p hp R := by
    ext s
    simp [Circle.normalizedLoopFamily, Circle.normalizedLoop, Circle.familySlice,
      radiusFamily, polynomialLoop, polynomialCircleMap]
  exact ⟨(F.cast hstart hend).symm⟩

/-- Interpolate from the leading monomial to the original polynomial. -/
noncomputable def leadingFamily (p : ℂ[X]) (R : ℝ) : C(I × I, ℂ) where
  toFun x :=
    let z := ((R : ℂ) * (Circle.expMap x.2 : ℂ))
    p.leadingCoeff * z ^ p.natDegree + (x.1 : ℂ) * p.eraseLead.eval z
  continuous_toFun := by fun_prop

@[simp]
theorem leadingFamily_apply (p : ℂ[X]) (R : ℝ) (t s : I) :
    leadingFamily p R (t, s) =
      p.leadingCoeff * ((R : ℂ) * (Circle.expMap s : ℂ)) ^ p.natDegree +
        (t : ℂ) * p.eraseLead.eval ((R : ℂ) * (Circle.expMap s : ℂ)) := rfl

theorem leadingFamily_ne_zero {p : ℂ[X]} {R : ℝ} (hR : 0 < R)
    (hdom : ∀ z : ℂ, ‖z‖ = R →
      ‖p.eraseLead.eval z‖ < ‖p.leadingCoeff * z ^ p.natDegree‖) (x : I × I) :
    leadingFamily p R x ≠ 0 := by
  apply leading_add_scaled_lower_ne_zero
  apply hdom
  rw [norm_mul]
  have hnormR : ‖(R : ℂ)‖ = R := by simp [abs_of_pos hR]
  rw [hnormR, _root_.Circle.norm_coe, mul_one]

private theorem expMap_nat_mul (n : ℕ) (s : I) :
    Circle.expMap ((n : ℝ) * (s : ℝ)) = Circle.expMap (s : ℝ) ^ n := by
  change _root_.Circle.exp (2 * Real.pi * ((n : ℝ) * (s : ℝ))) =
    _root_.Circle.exp (2 * Real.pi * (s : ℝ)) ^ n
  rw [show 2 * Real.pi * ((n : ℝ) * (s : ℝ)) =
    (n : ℝ) * (2 * Real.pi * (s : ℝ)) by ring]
  exact _root_.Circle.exp_natCast_mul _ _

private theorem coe_loopOfInt_nat (n : ℕ) (s : I) :
    (((Circle.loopOfInt (n : ℤ)) s : _root_.Circle) : ℂ) =
      ((Circle.expMap s : _root_.Circle) : ℂ) ^ n := by
  change ((Circle.expMap ((n : ℝ) * (s : ℝ)) : _root_.Circle) : ℂ) = _
  rw [expMap_nat_mul]
  exact _root_.Circle.coe_pow _ _

private theorem leadingTerm_ratio (a : ℂ) (ha : a ≠ 0) (R : ℝ) (hR : 0 < R)
    (n : ℕ) (s : I) :
    (a * ((R : ℂ) * (Circle.expMap s : ℂ)) ^ n) /
        (a * (R : ℂ) ^ n) =
      (Circle.expMap s : ℂ) ^ n := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  rw [mul_pow]
  field_simp [ha, hRc]

private theorem leading_add_eraseLead_eval (p : ℂ[X]) (z : ℂ) :
    p.leadingCoeff * z ^ p.natDegree + p.eraseLead.eval z = p.eval z := by
  rw [add_comm, ← eval_X_pow, ← eval_C_mul, ← eval_add,
    p.eraseLead_add_C_mul_X_pow]

theorem polynomialLoop_homotopic_loopOfInt {p : ℂ[X]} (hp : ∀ z, p.eval z ≠ 0)
    {R : ℝ} (hR : 0 < R) (hdom : ∀ z : ℂ, ‖z‖ = R →
      ‖p.eraseLead.eval z‖ < ‖p.leadingCoeff * z ^ p.natDegree‖) :
    (polynomialLoop p hp R).Homotopic (Circle.loopOfInt p.natDegree) := by
  have hp0 : p ≠ 0 := by
    intro h
    subst p
    simpa using hp 0
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  let hnonzero : ∀ x, leadingFamily p R x ≠ 0 :=
    fun x => leadingFamily_ne_zero hR hdom x
  have hperiodic : ∀ t, leadingFamily p R (t, 1) = leadingFamily p R (t, 0) := by
    intro t
    simp [leadingFamily]
  let F := Circle.normalizedLoopHomotopy (leadingFamily p R) hnonzero hperiodic
  have hstart : Circle.normalizedLoopFamily (leadingFamily p R) hnonzero
      hperiodic 0 = Circle.loopOfInt p.natDegree := by
    ext s
    rw [Circle.coe_normalizedLoopFamily]
    have hratio : leadingFamily p R (0, s) / leadingFamily p R (0, 0) =
        (Circle.expMap s : ℂ) ^ p.natDegree := by
      rw [leadingFamily_apply, leadingFamily_apply]
      have hz : ((((0 : I) : ℝ) : ℂ)) = 0 := by norm_num
      simp only [hz, zero_mul, add_zero]
      have he0 : ((Circle.expMap ((0 : I) : ℝ) : _root_.Circle) : ℂ) = 1 := by simp
      rw [he0, mul_one]
      exact leadingTerm_ratio _ hlc _ hR _ _
    rw [hratio, coe_loopOfInt_nat]
    rw [norm_pow, _root_.Circle.norm_coe, one_pow, inv_one, one_smul]
  have hend : Circle.normalizedLoopFamily (leadingFamily p R) hnonzero
      hperiodic 1 = polynomialLoop p hp R := by
    ext s
    rw [Circle.coe_normalizedLoopFamily, coe_polynomialLoop]
    simp only [leadingFamily_apply]
    have ho : ((((1 : I) : ℝ) : ℂ)) = 1 := by norm_num
    simp only [ho, one_mul]
    rw [leading_add_eraseLead_eval, leading_add_eraseLead_eval]
    have he0 : ((Circle.expMap ((0 : I) : ℝ) : _root_.Circle) : ℂ) = 1 := by simp
    rw [he0, mul_one]
  exact ⟨(F.cast hstart hend).symm⟩

/-- Outside some positive radius, the leading term of a nonconstant complex
polynomial strictly dominates all lower terms. -/
theorem exists_radius_leading_dominates {p : ℂ[X]} (hp : 0 < p.degree) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, ‖z‖ = R →
      ‖p.eraseLead.eval z‖ < ‖p.leadingCoeff * z ^ p.natDegree‖ := by
  have hp0 : p ≠ 0 := ne_zero_of_degree_gt hp
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have hdeg : p.eraseLead.degree <
      (C p.leadingCoeff * X ^ p.natDegree).degree := by
    rw [degree_C_mul_X_pow _ hlc, ← degree_eq_natDegree hp0]
    exact degree_eraseLead_lt hp0
  have hsmall :=
    (Polynomial.isLittleO_cobounded_of_degree_lt hdeg).bound
      (show 0 < (1 / 2 : ℝ) by norm_num)
  rcases (Filter.hasBasis_cobounded_norm (E := ℂ)).mem_iff.mp hsmall with
    ⟨r, -, hr⟩
  refine ⟨max r 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun z hz => ?_⟩
  have hzlarge : r ≤ ‖z‖ := by rw [hz]; exact le_max_left _ _
  have hbound := hr hzlarge
  change ‖p.eraseLead.eval z‖ ≤
    (1 / 2 : ℝ) * ‖(C p.leadingCoeff * X ^ p.natDegree).eval z‖ at hbound
  simp only [eval_mul, eval_C, eval_pow, eval_X] at hbound
  have hzpos : 0 < ‖z‖ := by rw [hz]; exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hleadpos : 0 < ‖p.leadingCoeff * z ^ p.natDegree‖ := by
    exact norm_pos_iff.mpr (mul_ne_zero hlc (pow_ne_zero _ (norm_pos_iff.mp hzpos)))
  nlinarith

/-- **Hatcher, Theorem 1.8 (page 31).** Every nonconstant complex polynomial has
a root, proved using the winding number of its values on large circles. -/
theorem exists_root_of_degree_pos {p : ℂ[X]} (hp : 0 < p.degree) :
    ∃ z : ℂ, p.IsRoot z := by
  by_contra! hroot
  have hne : ∀ z, p.eval z ≠ 0 := fun z hz => hroot z (IsRoot.def.mpr hz)
  obtain ⟨R, hR, hdom⟩ := exists_radius_leading_dominates hp
  have hpoly0 := polynomialLoop_homotopic_refl p hne R
  have hpolyn := polynomialLoop_homotopic_loopOfInt hne hR hdom
  have hn0 : (Circle.loopOfInt p.natDegree).Homotopic (Path.refl 1) :=
    hpolyn.symm.trans hpoly0
  have hq :
      Path.Homotopic.Quotient.mk (Circle.loopOfInt p.natDegree) =
        Path.Homotopic.Quotient.mk (Path.refl (1 : _root_.Circle)) :=
    Path.Homotopic.Quotient.eq.mpr hn0
  have hw := congr_arg
    (fun q : Path.Homotopic.Quotient (1 : _root_.Circle) 1 =>
      Circle.windingNumberFun (FundamentalGroup.fromPath q)) hq
  have hnzero : (p.natDegree : ℤ) = 0 := by
    calc
      (p.natDegree : ℤ) = Circle.windingNumberFun
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (Circle.loopOfInt p.natDegree))) :=
        (Circle.windingNumberFun_loopOfInt _).symm
      _ = Circle.windingNumberFun
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (Path.refl (1 : _root_.Circle)))) := hw
      _ = 0 := by
        change Circle.windingNumberFun (1 : FundamentalGroup _root_.Circle 1) = 0
        exact Circle.windingNumberFun_one
  have hnpos : 0 < p.natDegree := natDegree_pos_iff_degree_pos.mpr hp
  exact hnpos.ne' (by exact_mod_cast hnzero)

end Hatcher
