/-
Hatcher, *Algebraic Topology*, §1.1, page 29.

Hatcher proves `π₁(S¹) ≅ ℤ` by comparing loops in `S¹` with paths in `ℝ` along
`p(s) = (cos 2πs, sin 2πs)`, and the only property of `p` the argument uses is
that it is a covering map.

Mathlib has `AddCircle.isCoveringMap_coe`, that `ℝ → AddCircle T` is a covering
map, and `AddCircle.homeomorphCircle'`, a homeomorphism `AddCircle (2 * π) ≃ₜ
Circle`. This file composes them and renormalizes to period one, so that the
generator of the fibre over `1` is Hatcher's degree-one loop rather than a loop
of period `2 * π`.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Covering.AddCircle

open Real

namespace Hatcher.Circle

/-- The exponential `ℝ → S¹` of period `2 * π` is a covering map.

This is `AddCircle.isCoveringMap_coe` transported along
`AddCircle.homeomorphCircle'`. -/
theorem isCoveringMap_exp : IsCoveringMap (_root_.Circle.exp : ℝ → _root_.Circle) := by
  have h := (AddCircle.isCoveringMap_coe (2 * π)).homeomorph_comp AddCircle.homeomorphCircle'
  convert h using 1
  funext x
  exact (AddCircle.homeomorphCircle'_apply_mk x).symm

/-- Hatcher's `p(s) = (cos 2πs, sin 2πs)`, as a map `ℝ → S¹` of period one. -/
noncomputable def expMap : C(ℝ, _root_.Circle) :=
  _root_.Circle.exp.comp ⟨fun s => 2 * π * s, by fun_prop⟩

@[simp]
theorem expMap_apply (s : ℝ) : expMap s = _root_.Circle.exp (2 * π * s) := rfl

/-- **Hatcher, §1.1, page 29.** The map `p(s) = (cos 2πs, sin 2πs)` is a
covering map `ℝ → S¹`. This is the only fact about `p` that the computation of
`π₁(S¹)` uses. -/
theorem isCoveringMap_expMap : IsCoveringMap (expMap : ℝ → _root_.Circle) := by
  have key : (expMap : ℝ → _root_.Circle)
      = (_root_.Circle.exp : ℝ → _root_.Circle)
        ∘ (Homeomorph.mulLeft₀ (2 * π) two_pi_pos.ne') := by
    funext s; rfl
  rw [key]
  exact isCoveringMap_exp.comp_homeomorph _

/-- The fibre of `expMap` over the basepoint is exactly `ℤ`.

This is the normalization that makes the period-one map the right one: a loop
lifting to a path from `0` to `n` has winding number `n` on the nose, with no
factor of `2 * π` to divide out. -/
@[simp]
theorem expMap_eq_one {s : ℝ} : expMap s = 1 ↔ ∃ n : ℤ, s = n := by
  rw [expMap_apply, _root_.Circle.exp_eq_one]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by field_simp at hn; linarith⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

@[simp]
theorem expMap_zero : expMap 0 = 1 := by simp

theorem expMap_intCast (n : ℤ) : expMap (n : ℝ) = 1 := expMap_eq_one.2 ⟨n, rfl⟩

end Hatcher.Circle
