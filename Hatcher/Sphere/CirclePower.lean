/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.VanKampen.DiskBoundaryCircle
import Hatcher.VanKampen.CyclicPresentationAlgebra
import Mathlib.Topology.Algebra.Group.ZPow

/-!
# Integer powers on the standard circle

The fixed disk-boundary homeomorphism transports the continuous integer-power
operation on the complex unit circle to the standard one-sphere. Natural powers
agree with the existing circle map, and negative powers factor through inversion.
-/

noncomputable section

open CategoryTheory

namespace Hatcher.Sphere

/-- The actual integer-power self-map of the standard one-sphere. -/
noncomputable def circlePowerMap (d : ℤ) :
    TopCat.sphere.{0} 1 ⟶ TopCat.sphere.{0} 1 :=
  TopCat.ofHom
    { toFun := fun x ↦
        diskBoundaryTwoHomeomorphCircle.{0}.symm
          ((diskBoundaryTwoHomeomorphCircle.{0} x) ^ d)
      continuous_toFun :=
        diskBoundaryTwoHomeomorphCircle.{0}.symm.continuous.comp
          ((continuous_zpow d).comp diskBoundaryTwoHomeomorphCircle.{0}.continuous) }

/-- The integer-power map in the fixed circle coordinates. -/
theorem circlePowerMap_apply (d : ℤ) (x : TopCat.sphere.{0} 1) :
    circlePowerMap d x =
      diskBoundaryTwoHomeomorphCircle.{0}.symm
        ((diskBoundaryTwoHomeomorphCircle.{0} x) ^ d) :=
  rfl

/-- Transport to the unit circle recovers the integer-power operation. -/
@[simp]
theorem circlePowerMap_coordinate (d : ℤ) (x : TopCat.sphere.{0} 1) :
    diskBoundaryTwoHomeomorphCircle.{0} (circlePowerMap d x) =
      (diskBoundaryTwoHomeomorphCircle.{0} x) ^ d := by
  simp [circlePowerMap_apply]

/-- In complex coordinates the map is exactly `z ↦ z ^ d`. -/
theorem circlePowerMap_complex_coordinate (d : ℤ) (x : TopCat.sphere.{0} 1) :
    (diskBoundaryTwoHomeomorphCircle.{0} (circlePowerMap d x) : ℂ) =
      (diskBoundaryTwoHomeomorphCircle.{0} x : ℂ) ^ d := by
  rw [circlePowerMap_coordinate, _root_.Circle.coe_zpow]

/-- The zero power is the constant map at the standard circle basepoint. -/
@[simp]
theorem circlePowerMap_zero :
    circlePowerMap 0 = TopCat.const diskBoundaryTwoBasepoint.{0} := by
  apply TopCat.ext
  intro x
  change circlePowerMap 0 x = diskBoundaryTwoBasepoint.{0}
  simp [circlePowerMap_apply]
  rfl

/-- Natural powers reuse the previously constructed natural circle map. -/
theorem circlePowerMap_natCast (k : ℕ) :
    circlePowerMap (k : ℤ) =
      (TopCat.isoOfHomeo diskBoundaryTwoHomeomorphCircle.{0}).hom ≫
        TopCat.ofHom (Hatcher.Circle.degreeMap k) ≫
          (TopCat.isoOfHomeo diskBoundaryTwoHomeomorphCircle.{0}).inv := by
  apply TopCat.ext
  intro x
  change circlePowerMap (k : ℤ) x =
    diskBoundaryTwoHomeomorphCircle.{0}.symm
      (Hatcher.Circle.degreeMap k (diskBoundaryTwoHomeomorphCircle.{0} x))
  simp [circlePowerMap_apply, Hatcher.Circle.degreeMap_apply]
  rfl

/-- Negative natural powers are a natural power followed by inversion. -/
theorem circlePowerMap_neg_natCast (k : ℕ) :
    circlePowerMap (-(k : ℤ)) = circlePowerMap (k : ℤ) ≫ circlePowerMap (-1) := by
  apply TopCat.ext
  intro x
  change circlePowerMap (-(k : ℤ)) x = circlePowerMap (-1) (circlePowerMap (k : ℤ) x)
  apply diskBoundaryTwoHomeomorphCircle.{0}.injective
  simp only [circlePowerMap_coordinate, zpow_neg, zpow_one]

/-- A positive circle power is the actual homeomorphism between short centered
angular arcs obtained by scaling their coordinates by its exponent. The source
radius is `π / (2k)`, and the central fiber in that open arc is a singleton. -/
theorem circlePowerMap_positive_arcChart (k : ℕ) (hk : 0 < k)
    (x : TopCat.sphere.{0} 1) :
    let e := diskBoundaryTwoHomeomorphCircle.{0}
    let P : TopCat.sphere.{0} 1 → TopCat.sphere.{0} 1 := circlePowerMap (k : ℤ)
    let ε : ℝ := Real.pi / (2 * (k : ℝ))
    let β : ℝ := Real.pi / 2
    ∃ (U V : Set (TopCat.sphere.{0} 1))
      (φ : Set.Ioo (-ε) ε ≃ₜ U)
      (ψ : Set.Ioo (-β) β ≃ₜ V)
      (σ : Set.Ioo (-ε) ε ≃ₜ Set.Ioo (-β) β)
      (h : U ≃ₜ V),
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ P x ∈ V ∧
      (∀ t, e (φ t : TopCat.sphere.{0} 1) =
        e x * _root_.Circle.exp (t : ℝ)) ∧
      (∀ s, e (ψ s : TopCat.sphere.{0} 1) =
        (e x) ^ k * _root_.Circle.exp (s : ℝ)) ∧
      (∀ t, (σ t : ℝ) = (k : ℝ) * (t : ℝ)) ∧
      (∀ t, h (φ t) = ψ (σ t)) ∧
      (∀ u : U, (h u : TopCat.sphere.{0} 1) = P (u : TopCat.sphere.{0} 1)) ∧
      (∀ t, (e (P (φ t : TopCat.sphere.{0} 1)) : ℂ) =
        (e x : ℂ) ^ k * Complex.exp (((k : ℝ) * (t : ℝ) : ℝ) * Complex.I)) ∧
      U ∩ P ⁻¹' {P x} = {x} := by
  classical
  dsimp only
  let S : Type := TopCat.sphere.{0} 1
  let e : S ≃ₜ _root_.Circle := diskBoundaryTwoHomeomorphCircle.{0}
  let P : S → S := circlePowerMap (k : ℤ)
  let a : ℝ := k
  let ε : ℝ := Real.pi / (2 * a)
  let β : ℝ := Real.pi / 2
  have ha_pos : 0 < a := by
    dsimp [a]
    exact (Nat.cast_pos (α := ℝ)).mpr hk
  have ha_one : 1 ≤ a := by
    dsimp [a]
    exact (Nat.one_le_cast (α := ℝ)).mpr (Nat.succ_le_of_lt hk)
  have hβ_pos : 0 < β := by
    dsimp [β]
    exact div_pos Real.pi_pos (by norm_num)
  have hβ_pi : β ≤ Real.pi := by
    dsimp [β]
    exact div_le_self Real.pi_nonneg (by norm_num)
  have hε_eq : ε = β / a := by
    dsimp [ε, β]
    rw [div_div]
  have hε_pos : 0 < ε := by
    rw [hε_eq]
    exact div_pos hβ_pos ha_pos
  have hε_β : ε ≤ β := by
    rw [hε_eq]
    exact div_le_self hβ_pos.le ha_one
  have hε_pi : ε ≤ Real.pi := hε_β.trans hβ_pi
  have haε : a * ε = β := by
    rw [hε_eq, div_eq_mul_inv, mul_left_comm,
      mul_inv_cancel₀ ha_pos.ne', mul_one]
  let E : ∀ (r : ℝ), r ≤ Real.pi →
      Set.Ioo (-r) r ≃ₜ _root_.Circle.centeredArc r := fun r hr =>
    let hb := _root_.Circle.bijOn_exp_Ioo_centeredArc hr
    (Set.BijOn.equiv _root_.Circle.exp hb).toHomeomorphOfContinuousOpen
      (by
        change Continuous (Subtype.map _root_.Circle.exp hb.mapsTo)
        exact _root_.Circle.exp.continuous.subtype_map hb.mapsTo)
      (by
        change IsOpenMap (Subtype.map _root_.Circle.exp hb.mapsTo)
        exact _root_.Circle.isCoveringMap_exp.isOpenMap.subtype_map
          isOpen_Ioo hb.mapsTo)
  have hE (r : ℝ) (hr : r ≤ Real.pi) (t : Set.Ioo (-r) r) :
      (E r hr t : _root_.Circle) = _root_.Circle.exp (t : ℝ) :=
    rfl
  let A : _root_.Circle → ℝ → Set S := fun c r =>
    {z | c⁻¹ * e z ∈ _root_.Circle.centeredArc r}
  have hA_open (c : _root_.Circle) (r : ℝ) : IsOpen (A c r) := by
    change IsOpen ((fun z : S => c⁻¹ * e z) ⁻¹' _root_.Circle.centeredArc r)
    exact (_root_.Circle.isOpen_centeredArc r).preimage
      (continuous_const.mul e.continuous)
  let G : ∀ (c : _root_.Circle) (r : ℝ), r ≤ Real.pi →
      Set.Ioo (-r) r ≃ₜ A c r := fun c r hr =>
    (E r hr).trans
      (((Homeomorph.mulLeft c).trans e.symm).subtype
        (p := fun z : _root_.Circle => z ∈ _root_.Circle.centeredArc r)
        (q := fun z : S => z ∈ A c r)
        (by
          intro z
          change z ∈ _root_.Circle.centeredArc r ↔
            c⁻¹ * e (e.symm (c * z)) ∈ _root_.Circle.centeredArc r
          simp only [e.apply_symm_apply, ← mul_assoc, inv_mul_cancel, one_mul]))
  have hG (c : _root_.Circle) (r : ℝ) (hr : r ≤ Real.pi)
      (t : Set.Ioo (-r) r) :
      e (G c r hr t : S) = c * _root_.Circle.exp (t : ℝ) := by
    change e (e.symm (c * (E r hr t : _root_.Circle))) =
      c * _root_.Circle.exp (t : ℝ)
    rw [e.apply_symm_apply, hE r hr t]
  have hscale (t : ℝ) :
      t ∈ Set.Ioo (-ε) ε ↔ a * t ∈ Set.Ioo (-β) β := by
    change (-ε < t ∧ t < ε) ↔ (-β < a * t ∧ a * t < β)
    constructor
    · intro ht
      constructor
      · have hlt := mul_lt_mul_of_pos_left ht.1 ha_pos
        simpa only [mul_neg, haε] using hlt
      · have hlt := mul_lt_mul_of_pos_left ht.2 ha_pos
        simpa only [haε] using hlt
    · intro ht
      constructor
      · apply (mul_lt_mul_iff_of_pos_left ha_pos).mp
        simpa only [mul_neg, haε] using ht.1
      · apply (mul_lt_mul_iff_of_pos_left ha_pos).mp
        simpa only [haε] using ht.2
  let σ : Set.Ioo (-ε) ε ≃ₜ Set.Ioo (-β) β :=
    (Homeomorph.mulLeft₀ a ha_pos.ne').subtype
      (p := fun t : ℝ => t ∈ Set.Ioo (-ε) ε)
      (q := fun s : ℝ => s ∈ Set.Ioo (-β) β)
      hscale
  have hσ (t : Set.Ioo (-ε) ε) : (σ t : ℝ) = a * (t : ℝ) := rfl
  let U : Set S := A (e x) ε
  let V : Set S := A ((e x) ^ k) β
  let φ : Set.Ioo (-ε) ε ≃ₜ U := G (e x) ε hε_pi
  let ψ : Set.Ioo (-β) β ≃ₜ V := G ((e x) ^ k) β hβ_pi
  let h : U ≃ₜ V := (φ.symm.trans σ).trans ψ
  have hP_coordinate (z : S) : e (P z) = (e z) ^ k := by
    change diskBoundaryTwoHomeomorphCircle.{0} (circlePowerMap (k : ℤ) z) =
      (diskBoundaryTwoHomeomorphCircle.{0} z) ^ k
    rw [circlePowerMap_coordinate, zpow_natCast]
  have hU_mem : x ∈ U := by
    change (e x)⁻¹ * e x ∈ _root_.Circle.centeredArc ε
    have ht : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε_pos, hε_pos⟩
    simpa only [inv_mul_cancel, _root_.Circle.exp_zero] using
      (_root_.Circle.bijOn_exp_Ioo_centeredArc hε_pi).mapsTo ht
  have hV_mem : P x ∈ V := by
    change ((e x) ^ k)⁻¹ * e (P x) ∈ _root_.Circle.centeredArc β
    rw [hP_coordinate x]
    have ht : (0 : ℝ) ∈ Set.Ioo (-β) β := ⟨neg_lt_zero.mpr hβ_pos, hβ_pos⟩
    simpa only [inv_mul_cancel, _root_.Circle.exp_zero] using
      (_root_.Circle.bijOn_exp_Ioo_centeredArc hβ_pi).mapsTo ht
  have hφ (t : Set.Ioo (-ε) ε) :
      e (φ t : S) = e x * _root_.Circle.exp (t : ℝ) :=
    hG (e x) ε hε_pi t
  have hψ (s : Set.Ioo (-β) β) :
      e (ψ s : S) = (e x) ^ k * _root_.Circle.exp (s : ℝ) :=
    hG ((e x) ^ k) β hβ_pi s
  have hcomm (t : Set.Ioo (-ε) ε) : h (φ t) = ψ (σ t) := by
    change ψ (σ (φ.symm (φ t))) = ψ (σ t)
    rw [φ.symm_apply_apply]
  have hpower (t : Set.Ioo (-ε) ε) :
      e (P (φ t : S)) = (e x) ^ k * _root_.Circle.exp (a * (t : ℝ)) := by
    rw [hP_coordinate (φ t : S), hφ t, mul_pow,
      ← _root_.Circle.exp_natCast_mul (t : ℝ) k]
  have hactual (u : U) : (h u : S) = P (u : S) := by
    obtain ⟨t, ht⟩ := φ.surjective u
    rw [← ht, hcomm t]
    apply e.injective
    rw [hψ (σ t), hσ t, hpower t]
  have hcomplex (t : Set.Ioo (-ε) ε) :
      (e (P (φ t : S)) : ℂ) =
        (e x : ℂ) ^ k * Complex.exp (((k : ℝ) * (t : ℝ) : ℝ) * Complex.I) := by
    rw [hpower t]
    simp only [_root_.Circle.coe_mul, _root_.Circle.coe_pow, _root_.Circle.coe_exp, a]
  have hfiber : U ∩ P ⁻¹' {P x} = {x} := by
    ext z
    constructor
    · intro hz
      have hEq : P z = P x := Set.mem_singleton_iff.mp hz.2
      have hu : (⟨z, hz.1⟩ : U) = ⟨x, hU_mem⟩ := by
        apply h.injective
        apply Subtype.ext
        calc
          (h ⟨z, hz.1⟩ : S) = P z := hactual ⟨z, hz.1⟩
          _ = P x := hEq
          _ = (h ⟨x, hU_mem⟩ : S) := (hactual ⟨x, hU_mem⟩).symm
      exact Set.mem_singleton_iff.mpr (congrArg Subtype.val hu)
    · intro hz
      have hzx : z = x := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨hU_mem, rfl⟩
  exact ⟨U, V, φ, ψ, σ, h, hA_open (e x) ε, hA_open ((e x) ^ k) β,
    hU_mem, hV_mem, hφ, hψ, hσ, hcomm, hactual, hcomplex, hfiber⟩

/-- Positive angular stretching deforms to the rotation sending the center to
its image, on the full open arc of radius `π / (2k)`. The homotopy fixes that
image and avoids it at every other point of the arc throughout the deformation. -/
theorem circlePowerMap_positive_localStretchDeformation
    (k : ℕ) (hk : 0 < k) (x : TopCat.sphere.{0} 1) :
    let e := diskBoundaryTwoHomeomorphCircle.{0}
    let P : TopCat.sphere.{0} 1 → TopCat.sphere.{0} 1 := circlePowerMap (k : ℤ)
    let y := P x
    let ε : ℝ := Real.pi / (2 * (k : ℝ))
    ∃ (U : Set (TopCat.sphere.{0} 1)) (hx : x ∈ U)
      (φ : Set.Ioo (-ε) ε ≃ₜ U)
      (H : C(unitInterval × U, TopCat.sphere.{0} 1)),
      IsOpen U ∧
      (∀ t, e (φ t : TopCat.sphere.{0} 1) =
        e x * _root_.Circle.exp (t : ℝ)) ∧
      (∀ (s : unitInterval) (t : Set.Ioo (-ε) ε),
        e (H (s, φ t)) = e y * _root_.Circle.exp
          (((1 - (s : ℝ)) * (k : ℝ) + (s : ℝ)) * (t : ℝ))) ∧
      (∀ (s : unitInterval) (t : Set.Ioo (-ε) ε),
        (e (H (s, φ t)) : ℂ) = (e y : ℂ) * Complex.exp (
          ((((1 - (s : ℝ)) * (k : ℝ) + (s : ℝ)) * (t : ℝ) : ℝ) : ℂ) *
            Complex.I)) ∧
      (∀ u : U, H (0, u) = P (u : TopCat.sphere.{0} 1)) ∧
      (∀ u : U, H (1, u) =
        e.symm ((e y * (e x)⁻¹) * e (u : TopCat.sphere.{0} 1))) ∧
      (∀ s : unitInterval, H (s, ⟨x, hx⟩) = y) ∧
      (∀ (s : unitInterval) (u : U),
        (u : TopCat.sphere.{0} 1) ≠ x → H (s, u) ≠ y) := by
  classical
  dsimp only
  let S : Type := TopCat.sphere.{0} 1
  let e : S ≃ₜ _root_.Circle := diskBoundaryTwoHomeomorphCircle.{0}
  let P : S → S := circlePowerMap (k : ℤ)
  let y : S := P x
  let a : ℝ := k
  let ε : ℝ := Real.pi / (2 * a)
  let β : ℝ := Real.pi / 2
  rcases circlePowerMap_positive_arcChart k hk x with
    ⟨U, _, φ, _, _, _, hU, _, hx, _, hφ, _, _, _, _, hPk, _⟩
  change ∀ t : Set.Ioo (-ε) ε,
    e (φ t : S) = e x * _root_.Circle.exp (t : ℝ) at hφ
  change ∀ t : Set.Ioo (-ε) ε,
    (e (P (φ t : S)) : ℂ) = (e x : ℂ) ^ k *
      Complex.exp (((k : ℝ) * (t : ℝ) : ℝ) * Complex.I) at hPk
  have ha_one : 1 ≤ a := by
    dsimp [a]
    exact (Nat.one_le_cast (α := ℝ)).mpr (Nat.succ_le_of_lt hk)
  have ha_pos : 0 < a := zero_lt_one.trans_le ha_one
  have hβ_pos : 0 < β := by
    dsimp [β]
    exact div_pos Real.pi_pos (by norm_num)
  have hβ_pi : β ≤ Real.pi := by
    dsimp [β]
    exact div_le_self Real.pi_nonneg (by norm_num)
  have hε_eq : ε = β / a := by
    dsimp [ε, β]
    rw [div_div]
  have hε_pos : 0 < ε := by
    rw [hε_eq]
    exact div_pos hβ_pos ha_pos
  have haε : a * ε = β := by
    rw [hε_eq, div_eq_mul_inv, mul_left_comm,
      mul_inv_cancel₀ ha_pos.ne', mul_one]
  let ka : Set.Icc (1 : ℝ) a := ⟨a, ⟨ha_one, le_rfl⟩⟩
  let k1 : Set.Icc (1 : ℝ) a := ⟨1, ⟨le_rfl, ha_one⟩⟩
  let scaleI : unitInterval → Set.Icc (1 : ℝ) a :=
    Set.Icc.convexComb ka k1
  let scale : unitInterval → ℝ := fun s => (scaleI s : ℝ)
  have hscale : Continuous scale :=
    continuous_subtype_val.comp (Set.Icc.continuous_convexComb ka k1)
  have hscale_formula (s : unitInterval) :
      scale s = (1 - (s : ℝ)) * a + (s : ℝ) := by
    change (Set.Icc.convexComb ka k1 s : ℝ) =
      (1 - (s : ℝ)) * a + (s : ℝ)
    rw [Set.Icc.coe_convexComb]
    change (1 - (s : ℝ)) * a + (s : ℝ) * 1 =
      (1 - (s : ℝ)) * a + (s : ℝ)
    rw [mul_one]
  have hscale_zero : scale (0 : unitInterval) = a := by
    change (Set.Icc.convexComb ka k1 0 : ℝ) = a
    rw [Set.Icc.convexComb_zero]
  have hscale_one : scale (1 : unitInterval) = 1 := by
    change (Set.Icc.convexComb ka k1 1 : ℝ) = 1
    rw [Set.Icc.convexComb_one]
  have hscale_lower (s : unitInterval) : 1 ≤ scale s := (scaleI s).property.1
  have hscale_upper (s : unitInterval) : scale s ≤ a := (scaleI s).property.2
  have hscale_pos (s : unitInterval) : 0 < scale s :=
    zero_lt_one.trans_le (hscale_lower s)
  let θ : U → ℝ := fun u => (φ.symm u : ℝ)
  have hθ : Continuous θ := continuous_subtype_val.comp φ.symm.continuous
  have hθφ (t : Set.Ioo (-ε) ε) : θ (φ t) = (t : ℝ) := by
    change (φ.symm (φ t) : ℝ) = (t : ℝ)
    rw [φ.symm_apply_apply]
  let H : C(unitInterval × U, S) :=
    { toFun := fun p => e.symm (e y * _root_.Circle.exp (scale p.1 * θ p.2))
      continuous_toFun := e.symm.continuous.comp
        (continuous_const.mul
          (_root_.Circle.exp.continuous.comp
            ((hscale.comp continuous_fst).mul (hθ.comp continuous_snd)))) }
  have hHφ (s : unitInterval) (t : Set.Ioo (-ε) ε) :
      e (H (s, φ t)) = e y * _root_.Circle.exp (scale s * (t : ℝ)) := by
    change e (e.symm (e y * _root_.Circle.exp (scale s * θ (φ t)))) =
      e y * _root_.Circle.exp (scale s * (t : ℝ))
    rw [e.apply_symm_apply, hθφ t]
  have hformula (s : unitInterval) (t : Set.Ioo (-ε) ε) :
      e (H (s, φ t)) = e y * _root_.Circle.exp
        (((1 - (s : ℝ)) * a + (s : ℝ)) * (t : ℝ)) := by
    rw [hHφ s t, hscale_formula s]
  have hcomplex (s : unitInterval) (t : Set.Ioo (-ε) ε) :
      (e (H (s, φ t)) : ℂ) = (e y : ℂ) * Complex.exp (
        ((((1 - (s : ℝ)) * (k : ℝ) + (s : ℝ)) * (t : ℝ) : ℝ) : ℂ) *
          Complex.I) := by
    rw [hformula s t]
    simp only [_root_.Circle.coe_mul, _root_.Circle.coe_exp, a]
  have hy_coordinate : e y = (e x) ^ k := by
    change diskBoundaryTwoHomeomorphCircle.{0} (circlePowerMap (k : ℤ) x) =
      (diskBoundaryTwoHomeomorphCircle.{0} x) ^ k
    rw [circlePowerMap_coordinate, zpow_natCast]
  have hzero (u : U) : H (0, u) = P (u : S) := by
    obtain ⟨t, ht⟩ := φ.surjective u
    rw [← ht]
    apply e.injective
    apply _root_.Circle.coe_injective
    rw [hHφ (0 : unitInterval) t, hscale_zero, hy_coordinate]
    simpa only [_root_.Circle.coe_mul, _root_.Circle.coe_pow,
      _root_.Circle.coe_exp, a] using (hPk t).symm
  have hone (u : U) :
      H (1, u) = e.symm ((e y * (e x)⁻¹) * e (u : S)) := by
    obtain ⟨t, ht⟩ := φ.surjective u
    rw [← ht]
    apply e.injective
    rw [hHφ (1 : unitInterval) t, hscale_one, e.apply_symm_apply, hφ t, one_mul]
    calc
      e y * _root_.Circle.exp (t : ℝ) =
          (e y * ((e x)⁻¹ * e x)) * _root_.Circle.exp (t : ℝ) := by
        rw [inv_mul_cancel, mul_one]
      _ = (e y * (e x)⁻¹) * (e x * _root_.Circle.exp (t : ℝ)) := by
        simp only [mul_assoc]
  let t0 : Set.Ioo (-ε) ε := ⟨0, ⟨neg_lt_zero.mpr hε_pos, hε_pos⟩⟩
  have hφzero : φ t0 = ⟨x, hx⟩ := by
    apply Subtype.ext
    apply e.injective
    rw [hφ t0]
    simp only [t0, _root_.Circle.exp_zero, mul_one]
  have hθcenter : θ ⟨x, hx⟩ = 0 := by
    rw [← hφzero, hθφ t0]
  have hcenter (s : unitInterval) : H (s, ⟨x, hx⟩) = y := by
    change e.symm (e y * _root_.Circle.exp (scale s * θ ⟨x, hx⟩)) = y
    rw [hθcenter, mul_zero, _root_.Circle.exp_zero, mul_one, e.symm_apply_apply]
  have hbound (s : unitInterval) (t : Set.Ioo (-ε) ε) :
      |scale s * (t : ℝ)| < β := by
    calc
      |scale s * (t : ℝ)| = scale s * |(t : ℝ)| := by
        rw [abs_mul, abs_of_pos (hscale_pos s)]
      _ < scale s * ε :=
        mul_lt_mul_of_pos_left (abs_lt.mpr t.property) (hscale_pos s)
      _ ≤ a * ε := mul_le_mul_of_nonneg_right (hscale_upper s) hε_pos.le
      _ = β := haε
  have hβ_zero : (0 : ℝ) ∈ Set.Ioo (-β) β := ⟨neg_lt_zero.mpr hβ_pos, hβ_pos⟩
  have hpoint (s : unitInterval) (t : Set.Ioo (-ε) ε)
      (htarget : H (s, φ t) = y) : (t : ℝ) = 0 := by
    have hEq : e y * _root_.Circle.exp (scale s * (t : ℝ)) = e y :=
      (hHφ s t).symm.trans (congrArg e htarget)
    have hEq_mul : e y * _root_.Circle.exp (scale s * (t : ℝ)) =
        e y * _root_.Circle.exp 0 := by
      simpa only [_root_.Circle.exp_zero, mul_one] using hEq
    have hexp : _root_.Circle.exp (scale s * (t : ℝ)) = _root_.Circle.exp 0 :=
      mul_left_cancel hEq_mul
    have hprod : scale s * (t : ℝ) = 0 :=
      (_root_.Circle.bijOn_exp_Ioo_centeredArc hβ_pi).injOn
        (abs_lt.mp (hbound s t)) hβ_zero hexp
    exact (mul_eq_zero.mp hprod).resolve_left (hscale_pos s).ne'
  have havoid (s : unitInterval) (u : U) (hu : (u : S) ≠ x) : H (s, u) ≠ y := by
    intro htarget
    let t : Set.Ioo (-ε) ε := φ.symm u
    have hut : φ t = u := φ.apply_symm_apply u
    have hy' : H (s, φ t) = y := by
      rw [hut]
      exact htarget
    have htzero : (t : ℝ) = 0 := hpoint s t hy'
    have ht0 : t = t0 := Subtype.ext htzero
    have hueq : u = ⟨x, hx⟩ := by
      calc
        u = φ t := hut.symm
        _ = φ t0 := congrArg φ ht0
        _ = ⟨x, hx⟩ := hφzero
    exact hu (congrArg Subtype.val hueq)
  exact ⟨U, hx, φ, H, hU, hφ, hformula, hcomplex, hzero, hone, hcenter, havoid⟩

end Hatcher.Sphere
