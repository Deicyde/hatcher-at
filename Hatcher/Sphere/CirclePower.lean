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

end Hatcher.Sphere
