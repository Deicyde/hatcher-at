/-
Hatcher, *Algebraic Topology*, Theorem 1.10 (pages 32–33).

The key circle calculation in Hatcher's proof of the Borsuk–Ulam theorem is
that an antipodally symmetric loop has odd winding number. We formulate the
symmetry using two path halves: a path `a` from `1` to `-1`, followed by a path
`b` from `-1` to `1` satisfying `b(t) = -a(t)`.

If the lift of `a` from `0` ends at `q`, then `expMap q = -1`, so
`q = k + 1/2` for some integer `k`. The lift of `b` from `q` is the translate
of the first lift by `q`; hence the full loop ends at `2q = 2k + 1`.
-/
import Hatcher.Circle.FundamentalGroup

open Real unitInterval

namespace Hatcher.Circle

/-- The normalized exponential sends addition in `ℝ` to multiplication on the circle. -/
theorem expMap_add (s t : ℝ) : expMap (s + t) = expMap s * expMap t := by
  rw [expMap_apply, expMap_apply, expMap_apply]
  rw [show 2 * π * (s + t) = 2 * π * s + 2 * π * t by ring]
  exact _root_.Circle.exp_add _ _

/-- A half-turn in the normalized covering map lands at the antipode of `1`. -/
@[simp]
theorem expMap_half : expMap (1 / 2 : ℝ) = (-1 : _root_.Circle) := by
  apply _root_.Circle.coe_injective
  rw [expMap_apply, show 2 * π * (1 / 2 : ℝ) = π by ring]
  simp [_root_.Circle.coe_exp]

/-- The fibre of `expMap` over `-1` consists of the half-integers. -/
theorem expMap_eq_neg_one {s : ℝ} :
    expMap s = (-1 : _root_.Circle) ↔ ∃ n : ℤ, s = n + 1 / 2 := by
  rw [← expMap_half]
  constructor
  · intro h
    rw [expMap_apply, expMap_apply, _root_.Circle.exp_eq_exp] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    have hpi : π ≠ 0 := ne_of_gt pi_pos
    field_simp at hn ⊢
    nlinarith
  · rintro ⟨n, rfl⟩
    rw [add_comm]
    exact expMap_add_intCast (1 / 2) n

/-- The antipodal image of a path from `1` to `-1`. -/
noncomputable def antipodalPath (a : Path (1 : _root_.Circle) (-1)) :
    Path (-1 : _root_.Circle) 1 where
  toFun t := -a t
  continuous_toFun := a.continuous.neg
  source' := by simp
  target' := by simp

@[simp]
theorem antipodalPath_apply (a : Path (1 : _root_.Circle) (-1)) (t : I) :
    antipodalPath a t = -a t := rfl

/-- A loop obtained by following a path from `1` to `-1` and then its
pointwise antipodal image has odd winding number. This is the key circle lemma
in Hatcher's proof of the Borsuk–Ulam theorem. -/
theorem windingNumberFun_odd_of_antipodal_halves
    (a : Path (1 : _root_.Circle) (-1)) (b : Path (-1 : _root_.Circle) 1)
    (hneg : ∀ t, b t = -a t) :
    Odd (windingNumberFun
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a.trans b)))) := by
  have ha0 : (a : C(I, _root_.Circle)) 0 = expMap (0 : ℝ) :=
    a.source.trans expMap_zero.symm
  let L : C(I, ℝ) := cov.liftPath a 0 ha0
  let q : ℝ := L 1
  have hLlifts : ∀ t, expMap (L t) = a t := fun t =>
    congr_fun (cov.liftPath_lifts a 0 ha0) t
  have hqexp : expMap q = (-1 : _root_.Circle) :=
    (hLlifts 1).trans a.target
  obtain ⟨k, hk⟩ := expMap_eq_neg_one.mp hqexp
  have hbq : (b : C(I, _root_.Circle)) 0 = expMap q :=
    b.source.trans hqexp.symm
  let B : C(I, ℝ) := ⟨fun t => L t + q, by fun_prop⟩
  have hB : B = cov.liftPath b q hbq := by
    rw [cov.eq_liftPath_iff']
    constructor
    · funext t
      change expMap (L t + q) = b t
      rw [expMap_add, hLlifts t, hqexp, hneg t]
      exact mul_neg_one _
    · change L 0 + q = q
      rw [show L 0 = 0 by exact cov.liftPath_zero a 0 ha0]
      exact zero_add q
  have hfull := cov.liftPath_trans expMap_zero.symm a b
  have hend := congr_arg (fun f : C(I, ℝ) => f 1) hfull
  have hend' : cov.liftPath (a.trans b) 0 (by simp) 1 = 2 * q := by
    simpa [L, q, ← hB, B, two_mul] using hend
  have hmono :
      ((cov.monodromy (Path.Homotopic.Quotient.mk (a.trans b)) fibreZero : Fibre) : ℝ) =
        2 * q := hend'
  refine ⟨k, ?_⟩
  have hcast := cast_fibreToInt
    (cov.monodromy (Path.Homotopic.Quotient.mk (a.trans b)) fibreZero)
  apply Int.cast_injective (α := ℝ)
  change ((windingNumberFun
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a.trans b))) : ℤ) : ℝ) =
      ((2 * k + 1 : ℤ) : ℝ)
  rw [show ((windingNumberFun
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a.trans b))) : ℤ) : ℝ) =
      ((cov.monodromy (Path.Homotopic.Quotient.mk (a.trans b)) fibreZero : Fibre) : ℝ) by
        exact hcast]
  rw [hmono, hk]
  push_cast
  ring

/-- The winding number in `windingNumberFun_odd_of_antipodal_halves` is nonzero. -/
theorem windingNumberFun_ne_zero_of_antipodal_halves
    (a : Path (1 : _root_.Circle) (-1)) (b : Path (-1 : _root_.Circle) 1)
    (hneg : ∀ t, b t = -a t) :
    windingNumberFun
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a.trans b))) ≠ 0 := by
  intro hzero
  have hodd := windingNumberFun_odd_of_antipodal_halves a b hneg
  rw [hzero] at hodd
  exact Int.not_odd_zero hodd

/-- The canonical loop formed by a path and its antipodal image has odd winding number. -/
theorem windingNumberFun_trans_antipodalPath_odd
    (a : Path (1 : _root_.Circle) (-1)) :
    Odd (windingNumberFun (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (a.trans (antipodalPath a))))) :=
  windingNumberFun_odd_of_antipodal_halves a (antipodalPath a) fun _ => rfl

end Hatcher.Circle
