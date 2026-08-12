/-
Hatcher, *Algebraic Topology*, §1.1, page 29.

The winding number of a loop in `S¹`: lift it to a path in `ℝ` starting at `0`
and read off the endpoint, which lies in the fibre `ℤ`. Homotopic loops have
equal winding numbers because path homotopies lift, and Mathlib packages both
facts as `IsCoveringMap.monodromy`, which is already well defined on homotopy
classes.

What is left is that monodromy translates: moving the starting lift by an
integer moves the endpoint by the same integer. That is what makes the winding
number additive, and it is proved here from uniqueness of lifts, using that
`s ↦ s + n` is a deck transformation of `expMap`.
-/
import Hatcher.Circle.Covering
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

open Real unitInterval

namespace Hatcher.Circle

/-- The fibre of `expMap` over the basepoint. -/
def Fibre : Set ℝ := (expMap : ℝ → _root_.Circle) ⁻¹' {1}

theorem mem_fibre {s : ℝ} : s ∈ Fibre ↔ ∃ n : ℤ, s = n := expMap_eq_one

theorem zero_mem_fibre : (0 : ℝ) ∈ Fibre := mem_fibre.2 ⟨0, by simp⟩

theorem intCast_mem_fibre (n : ℤ) : (n : ℝ) ∈ Fibre := mem_fibre.2 ⟨n, rfl⟩

/-- The basepoint of the fibre, Hatcher's starting lift `0`. -/
def fibreZero : Fibre := ⟨0, zero_mem_fibre⟩

@[simp] theorem coe_fibreZero : (fibreZero : ℝ) = 0 := rfl

/-- The integer labelling a point of the fibre. -/
noncomputable def fibreToInt (s : Fibre) : ℤ := (mem_fibre.1 s.2).choose

@[simp]
theorem cast_fibreToInt (s : Fibre) : ((fibreToInt s : ℤ) : ℝ) = (s : ℝ) :=
  ((mem_fibre.1 s.2).choose_spec).symm

theorem fibreToInt_injective : Function.Injective fibreToInt := fun a b h =>
  Subtype.ext (by rw [← cast_fibreToInt a, ← cast_fibreToInt b, h])

@[simp]
theorem fibreToInt_zero : fibreToInt fibreZero = 0 := by
  have := cast_fibreToInt fibreZero
  rw [coe_fibreZero] at this
  exact_mod_cast this

/-- Translation by an integer is a deck transformation of `expMap`. -/
theorem expMap_add_intCast (s : ℝ) (n : ℤ) : expMap (s + n) = expMap s := by
  rw [expMap_apply, expMap_apply, mul_add]
  exact _root_.Circle.exp_eq_exp.2 ⟨n, by ring⟩

/-- Shorthand for the covering `p : ℝ → S¹`. -/
theorem cov : IsCoveringMap (expMap : ℝ → _root_.Circle) := isCoveringMap_expMap

/-- Lifting a loop from a translated starting point translates the endpoint.

Uniqueness of lifts applied to the deck transformation `s ↦ s + n`: if `L`
lifts `γ` from `0`, then `L + n` lifts `γ` from `n`, so the two endpoints
differ by `n`. -/
theorem liftPath_one_add (γ : Path (1 : _root_.Circle) 1) (a : ℝ) (ha : a ∈ Fibre)
    (h0 : (γ : C(I, _root_.Circle)) 0 = expMap (0 : ℝ))
    (ha' : (γ : C(I, _root_.Circle)) 0 = expMap a) :
    cov.liftPath γ a ha' 1 = cov.liftPath γ 0 h0 1 + a := by
  obtain ⟨n, rfl⟩ := mem_fibre.1 ha
  set L : C(I, ℝ) := cov.liftPath (γ : C(I, _root_.Circle)) 0 h0 with hL
  have hlifts : ∀ t, expMap (L t) = (γ : C(I, _root_.Circle)) t := fun t =>
    congr_fun (cov.liftPath_lifts (γ := (γ : C(I, _root_.Circle))) (e := 0) (γ_0 := h0)) t
  have hzero : L 0 = 0 :=
    cov.liftPath_zero (γ := (γ : C(I, _root_.Circle))) (e := 0) (γ_0 := h0)
  have hkey : (⟨fun t => L t + (n : ℝ), by fun_prop⟩ : C(I, ℝ))
      = cov.liftPath (γ : C(I, _root_.Circle)) ((n : ℝ)) ha' := by
    rw [cov.eq_liftPath_iff']
    refine ⟨funext fun t => ?_, ?_⟩
    · show expMap (L t + (n : ℝ)) = _
      rw [expMap_add_intCast]
      exact hlifts t
    · show L 0 + (n : ℝ) = (n : ℝ)
      rw [hzero, zero_add]
  have := congr_arg (fun f : C(I, ℝ) => f 1) hkey
  simpa using this.symm

/-- **Monodromy translates.** Moving the starting lift by a point of the fibre moves
the endpoint by the same amount. -/
theorem monodromy_translate (γ : Path.Homotopic.Quotient (1 : _root_.Circle) 1) (a : Fibre) :
    ((cov.monodromy γ a : Fibre) : ℝ)
      = ((cov.monodromy γ fibreZero : Fibre) : ℝ) + (a : ℝ) := by
  obtain ⟨γ⟩ := γ
  exact liftPath_one_add γ (a : ℝ) a.2 _ _

/-- The winding number of a loop class in `S¹`, as an integer. -/
noncomputable def windingNumberFun (γ : FundamentalGroup _root_.Circle 1) : ℤ :=
  fibreToInt (cov.monodromy γ.toPath fibreZero)

@[simp]
theorem windingNumberFun_one : windingNumberFun (1 : FundamentalGroup _root_.Circle 1) = 0 := by
  have h : cov.monodromy (1 : FundamentalGroup _root_.Circle 1).toPath fibreZero = fibreZero :=
    congr_fun cov.monodromy_refl fibreZero
  rw [windingNumberFun, h, fibreToInt_zero]

theorem windingNumberFun_mul (γ δ : FundamentalGroup _root_.Circle 1) :
    windingNumberFun (γ * δ) = windingNumberFun γ + windingNumberFun δ := by
  have hmul : (γ * δ).toPath = δ.toPath.trans γ.toPath := rfl
  have h := monodromy_translate γ.toPath (cov.monodromy δ.toPath fibreZero)
  have hcast : ((windingNumberFun (γ * δ) : ℤ) : ℝ)
      = ((windingNumberFun γ + windingNumberFun δ : ℤ) : ℝ) := by
    unfold windingNumberFun
    rw [hmul, cov.monodromy_trans_apply]
    push_cast
    rw [cast_fibreToInt, cast_fibreToInt, cast_fibreToInt]
    linarith [h]
  exact_mod_cast hcast

/-- **Hatcher, §1.1, page 29.** The winding number, as a group homomorphism
`π₁(S¹) → ℤ`. -/
noncomputable def windingNumber :
    FundamentalGroup _root_.Circle 1 →* Multiplicative ℤ where
  toFun γ := Multiplicative.ofAdd (windingNumberFun γ)
  map_one' := by simp
  map_mul' γ δ := by
    simp only [windingNumberFun_mul]
    rfl

@[simp]
theorem windingNumber_apply (γ : FundamentalGroup _root_.Circle 1) :
    windingNumber γ = Multiplicative.ofAdd (windingNumberFun γ) := rfl

end Hatcher.Circle
