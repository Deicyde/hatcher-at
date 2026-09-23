import Hatcher.VanKampen.ConeAttachmentDisk
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A one-cell attached to a point is a circle

This module identifies the cone attachment of the unique map from the
boundary of the standard one-disk to a point with the circle, preserving the
chosen basepoint.
-/

noncomputable section

open Metric Set Topology
open scoped unitInterval

namespace Hatcher.VanKampen

namespace ConeAttachment

universe u

local instance : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩

private abbrev BoundaryOne :=
  ((TopCat.diskBoundary.{u} 1 : TopCat.{u}) : Type u)

private abbrev pointAttachingMap : BoundaryOne.{u} → PUnit :=
  fun _ ↦ PUnit.unit

private abbrev CirclePrequotient := Prequotient PUnit BoundaryOne.{u}

private abbrev CircleInterval := Set.Icc (0 : ℝ) (0 + 2)

private def boundaryCoordinate (x : BoundaryOne.{u}) : ℝ :=
  (x.down : EuclideanSpace ℝ (Fin 1)) 0

private theorem abs_boundaryCoordinate (x : BoundaryOne.{u}) :
    |boundaryCoordinate x| = 1 := by
  have h := mem_sphere_zero_iff_norm.mp x.down.2
  have hxvec : (x.down : EuclideanSpace ℝ (Fin 1)) =
      EuclideanSpace.single 0 (boundaryCoordinate x) := by
    ext i
    fin_cases i
    simp [boundaryCoordinate]
  rw [hxvec, PiLp.norm_single, Real.norm_eq_abs] at h
  exact h

private theorem boundaryCoordinate_eq_neg_one_or_one (x : BoundaryOne.{u}) :
    boundaryCoordinate x = -1 ∨ boundaryCoordinate x = 1 := by
  simpa [or_comm] using
    (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp (abs_boundaryCoordinate x)

private def negativeBoundary : BoundaryOne.{u} :=
  ULift.up ⟨EuclideanSpace.single 0 (-1), by
    rw [mem_sphere_zero_iff_norm, PiLp.norm_single]
    norm_num⟩

private def positiveBoundary : BoundaryOne.{u} :=
  ULift.up ⟨EuclideanSpace.single 0 1, by
    rw [mem_sphere_zero_iff_norm, PiLp.norm_single]
    norm_num⟩

@[simp] private theorem boundaryCoordinate_negative :
    boundaryCoordinate negativeBoundary.{u} = -1 := by
  simp [boundaryCoordinate, negativeBoundary]

@[simp] private theorem boundaryCoordinate_positive :
    boundaryCoordinate positiveBoundary.{u} = 1 := by
  simp [boundaryCoordinate, positiveBoundary]

private theorem continuous_boundaryCoordinate :
    Continuous boundaryCoordinate.{u} := by
  exact (EuclideanSpace.proj (𝕜 := ℝ) (i := 0)).continuous.comp
    (continuous_subtype_val.comp continuous_uliftDown)

private theorem boundary_eq_negative_of_coordinate_eq
    (x : BoundaryOne.{u}) (h : boundaryCoordinate x = -1) :
    x = negativeBoundary := by
  apply ULift.ext
  apply Subtype.ext
  ext i
  fin_cases i
  simpa [boundaryCoordinate, negativeBoundary] using h

private theorem boundary_eq_positive_of_coordinate_eq
    (x : BoundaryOne.{u}) (h : boundaryCoordinate x = 1) :
    x = positiveBoundary := by
  apply ULift.ext
  apply Subtype.ext
  ext i
  fin_cases i
  simpa [boundaryCoordinate, positiveBoundary] using h

private def intervalRaw : CirclePrequotient.{u} → CircleInterval
  | Sum.inl _ => ⟨0, by norm_num⟩
  | Sum.inr (Sum.inl _) => ⟨1, by norm_num⟩
  | Sum.inr (Sum.inr (x, t)) =>
      ⟨1 + (t : ℝ) * boundaryCoordinate x, by
        rcases boundaryCoordinate_eq_neg_one_or_one x with hx | hx
        · rw [hx]
          constructor <;> simp only [mul_neg, mul_one]
          · linarith [t.2.2]
          · linarith [t.2.1]
        · rw [hx]
          constructor <;> simp only [mul_one]
          · linarith [t.2.1]
          · linarith [t.2.2]⟩

private theorem continuous_intervalRaw : Continuous intervalRaw.{u} := by
  rw [continuous_sum_dom]
  constructor
  · exact continuous_const
  · rw [continuous_sum_dom]
    constructor
    · exact continuous_const
    · apply Continuous.subtype_mk
      exact continuous_const.add
        ((continuous_subtype_val.comp continuous_snd).mul
          (continuous_boundaryCoordinate.comp continuous_fst))

private theorem intervalRaw_normalForm (p : CirclePrequotient.{u}) :
    Quot.mk (AddCircle.EndpointIdent (2 : ℝ) 0)
        (intervalRaw (normalForm pointAttachingMap p)) =
      Quot.mk (AddCircle.EndpointIdent (2 : ℝ) 0) (intervalRaw p) := by
  rcases p with _ | (_ | ⟨x, t⟩)
  · rfl
  · rfl
  · by_cases h0 : t = 0
    · subst t
      simp [normalForm, intervalRaw]
    · by_cases h1 : t = 1
      · subst t
        rcases boundaryCoordinate_eq_neg_one_or_one x with hx | hx
        · simp [normalForm, intervalRaw, hx]
        · have hxp := boundary_eq_positive_of_coordinate_eq x hx
          subst x
          rw [show normalForm pointAttachingMap
              (Sum.inr (Sum.inr (positiveBoundary, (1 : I)))) =
              Sum.inl PUnit.unit by simp [normalForm]]
          simp only [intervalRaw, boundaryCoordinate_positive]
          refine (Quot.sound
            (AddCircle.EndpointIdent.mk (p := (2 : ℝ)) (a := 0))).trans ?_
          apply congrArg (Quot.mk (AddCircle.EndpointIdent (2 : ℝ) 0))
          apply Subtype.ext
          norm_num
      · simp [normalForm, intervalRaw, h0, h1]

private def coneToIntervalQuot :
    Hatcher.VanKampen.ConeAttachment pointAttachingMap.{u} →
      Quot (AddCircle.EndpointIdent (2 : ℝ) 0) :=
  Quotient.lift
    (fun p ↦ Quot.mk _ (intervalRaw p))
    (fun a b h ↦ by
      change normalForm pointAttachingMap a = normalForm pointAttachingMap b at h
      rw [← intervalRaw_normalForm a, ← intervalRaw_normalForm b, h])

private theorem continuous_coneToIntervalQuot :
    Continuous coneToIntervalQuot.{u} := by
  apply Continuous.quotient_lift
  exact continuous_quot_mk.comp continuous_intervalRaw

@[simp] private theorem coneToIntervalQuot_basepoint :
    coneToIntervalQuot.{u} (base pointAttachingMap PUnit.unit) =
      Quot.mk (AddCircle.EndpointIdent (2 : ℝ) 0)
        (⟨0, by norm_num⟩ : CircleInterval) :=
  rfl

private def leftHeight (y : CircleInterval) (hy : (y : ℝ) ≤ 1) : I :=
  ⟨1 - (y : ℝ), sub_nonneg.mpr hy, by linarith [y.2.1]⟩

private def rightHeight (y : CircleInterval) (hy : ¬ (y : ℝ) ≤ 1) : I :=
  ⟨(y : ℝ) - 1, sub_nonneg.mpr (le_of_not_ge hy), by linarith [y.2.2]⟩

private def intervalSection (y : CircleInterval) :
    Hatcher.VanKampen.ConeAttachment pointAttachingMap.{u} :=
  if hy : (y : ℝ) ≤ 1 then
    cylinder pointAttachingMap negativeBoundary (leftHeight y hy)
  else
    cylinder pointAttachingMap positiveBoundary (rightHeight y hy)

private theorem intervalSection_left_endpoint :
    intervalSection (⟨0, by norm_num⟩ : CircleInterval) =
      base pointAttachingMap PUnit.unit := by
  rw [show intervalSection (⟨0, by norm_num⟩ : CircleInterval) =
      cylinder pointAttachingMap negativeBoundary
        (leftHeight (⟨0, by norm_num⟩ : CircleInterval) (by norm_num)) by
      simp [intervalSection]]
  rw [show leftHeight (⟨0, by norm_num⟩ : CircleInterval) (by norm_num) = 1 by
    apply Subtype.ext
    simp [leftHeight]]
  exact cylinder_one pointAttachingMap negativeBoundary

private theorem intervalSection_midpoint :
    intervalSection (⟨1, by norm_num⟩ : CircleInterval) =
      apex pointAttachingMap := by
  rw [show intervalSection (⟨1, by norm_num⟩ : CircleInterval) =
      cylinder pointAttachingMap negativeBoundary
        (leftHeight (⟨1, by norm_num⟩ : CircleInterval) (by norm_num)) by
      simp [intervalSection]]
  rw [show leftHeight (⟨1, by norm_num⟩ : CircleInterval) (by norm_num) = 0 by
    apply Subtype.ext
    simp [leftHeight]]
  exact cylinder_zero pointAttachingMap negativeBoundary

private theorem intervalSection_right_endpoint :
    intervalSection (⟨0 + 2, by norm_num⟩ : CircleInterval) =
      base pointAttachingMap PUnit.unit := by
  rw [show intervalSection (⟨0 + 2, by norm_num⟩ : CircleInterval) =
      cylinder pointAttachingMap positiveBoundary
        (rightHeight (⟨0 + 2, by norm_num⟩ : CircleInterval) (by norm_num)) by
        simp [intervalSection]]
  rw [show rightHeight (⟨0 + 2, by norm_num⟩ : CircleInterval) (by norm_num) = 1 by
    apply Subtype.ext
    norm_num [rightHeight]]
  exact cylinder_one pointAttachingMap positiveBoundary

private def intervalQuotToCone :
    Quot (AddCircle.EndpointIdent (2 : ℝ) 0) →
      Hatcher.VanKampen.ConeAttachment pointAttachingMap.{u} :=
  Quot.lift intervalSection (by
    rintro _ _ ⟨_⟩
    exact intervalSection_left_endpoint.trans intervalSection_right_endpoint.symm)

private theorem intervalSection_intervalRaw (p : CirclePrequotient.{u}) :
    intervalSection (intervalRaw p) = quotientMk pointAttachingMap p := by
  rcases p with x | (_ | ⟨x, t⟩)
  · rcases x with ⟨⟩
    exact intervalSection_left_endpoint
  · exact intervalSection_midpoint
  · rcases boundaryCoordinate_eq_neg_one_or_one x with hx | hx
    · have hxn := boundary_eq_negative_of_coordinate_eq x hx
      subst x
      change intervalSection (intervalRaw
          (Sum.inr (Sum.inr (negativeBoundary, t)))) =
        cylinder pointAttachingMap negativeBoundary t
      have hy : ((intervalRaw
          (Sum.inr (Sum.inr (negativeBoundary, t)))) : ℝ) ≤ 1 := by
        simp [intervalRaw]
        exact t.2.1
      rw [show intervalSection (intervalRaw
          (Sum.inr (Sum.inr (negativeBoundary, t)))) =
        cylinder pointAttachingMap negativeBoundary
          (leftHeight (intervalRaw
            (Sum.inr (Sum.inr (negativeBoundary, t)))) hy) by
          unfold intervalSection
          rw [dif_pos hy]]
      congr 1
      apply Subtype.ext
      simp [leftHeight, intervalRaw]
    · have hxp := boundary_eq_positive_of_coordinate_eq x hx
      subst x
      by_cases h0 : t = 0
      · subst t
        have hright : quotientMk pointAttachingMap
            (Sum.inr (Sum.inr (positiveBoundary, (0 : I)))) =
            apex pointAttachingMap :=
          cylinder_zero pointAttachingMap positiveBoundary
        rw [hright]
        convert intervalSection_midpoint using 1
        apply congrArg intervalSection
        apply Subtype.ext
        simp [intervalRaw]
      · have ht0 : (0 : ℝ) < (t : ℝ) := by
          exact lt_of_le_of_ne t.2.1 (fun ht ↦ h0 (Subtype.ext ht.symm))
        have hy : ¬ ((intervalRaw
            (Sum.inr (Sum.inr (positiveBoundary, t)))) : ℝ) ≤ 1 := by
          have hcoord : ((intervalRaw
              (Sum.inr (Sum.inr (positiveBoundary, t)))) : ℝ) =
              1 + (t : ℝ) := by
            simp [intervalRaw]
          rw [hcoord]
          linarith
        change intervalSection (intervalRaw
            (Sum.inr (Sum.inr (positiveBoundary, t)))) =
          cylinder pointAttachingMap positiveBoundary t
        rw [show intervalSection (intervalRaw
            (Sum.inr (Sum.inr (positiveBoundary, t)))) =
          cylinder pointAttachingMap positiveBoundary
            (rightHeight (intervalRaw
              (Sum.inr (Sum.inr (positiveBoundary, t)))) hy) by
            unfold intervalSection
            rw [dif_neg hy]]
        congr 1
        apply Subtype.ext
        simp [rightHeight, intervalRaw]

private theorem coneToIntervalQuot_intervalSection
    (y : CircleInterval) :
    coneToIntervalQuot (intervalSection y) =
      Quot.mk (AddCircle.EndpointIdent (2 : ℝ) 0) y := by
  simp only [intervalSection]
  split_ifs with hy
  · change Quot.mk _ (intervalRaw
        (Sum.inr (Sum.inr (negativeBoundary,
          leftHeight y hy)))) = _
    apply congrArg (Quot.mk (AddCircle.EndpointIdent (2 : ℝ) 0))
    apply Subtype.ext
    simp [intervalRaw, leftHeight]
  · change Quot.mk _ (intervalRaw
        (Sum.inr (Sum.inr (positiveBoundary,
          rightHeight y hy)))) = _
    apply congrArg (Quot.mk (AddCircle.EndpointIdent (2 : ℝ) 0))
    apply Subtype.ext
    simp [intervalRaw, rightHeight]

private noncomputable def coneIntervalEquiv :
    Hatcher.VanKampen.ConeAttachment pointAttachingMap.{u} ≃
      Quot (AddCircle.EndpointIdent (2 : ℝ) 0) where
  toFun := coneToIntervalQuot
  invFun := intervalQuotToCone
  left_inv z := Quotient.inductionOn' z fun p ↦ by
    change intervalSection (intervalRaw p) = quotientMk pointAttachingMap p
    exact intervalSection_intervalRaw p
  right_inv z := by
    induction z using Quot.ind with
    | _ y =>
      change coneToIntervalQuot (intervalSection y) = Quot.mk _ y
      exact coneToIntervalQuot_intervalSection y

private noncomputable def coneIntervalHomeomorph :
    Hatcher.VanKampen.ConeAttachment pointAttachingMap.{u} ≃ₜ
      Quot (AddCircle.EndpointIdent (2 : ℝ) 0) := by
  let hq := isQuotientMap_quotientMk pointAttachingMap.{u}
  letI : CompactSpace
      (Hatcher.VanKampen.ConeAttachment pointAttachingMap.{u}) :=
    ⟨by
      rw [← hq.surjective.range_eq]
      exact isCompact_range hq.continuous⟩
  letI : T2Space (Quot (AddCircle.EndpointIdent (2 : ℝ) 0)) :=
    (AddCircle.homeoIccQuot (2 : ℝ) 0).t2Space
  change (Hatcher.VanKampen.ConeAttachment pointAttachingMap.{u} ≃ₜ
    Quot (AddCircle.EndpointIdent (2 : ℝ) 0))
  exact coneIntervalEquiv.toHomeomorphOfContinuousClosed
    (by change Continuous coneToIntervalQuot; exact continuous_coneToIntervalQuot)
    (by change IsClosedMap coneToIntervalQuot
        exact continuous_coneToIntervalQuot.isClosedMap)

end ConeAttachment

local instance : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩

/-- Attaching the cone on the boundary of the standard one-disk to a point
gives the circle. -/
noncomputable def circleOneCellHomeomorph :
    Hatcher.VanKampen.ConeAttachment
      (fun _ : ((TopCat.diskBoundary.{u} 1 : TopCat.{u}) : Type u) ↦
        PUnit.unit) ≃ₜ ULift.{u} _root_.Circle :=
  ConeAttachment.coneIntervalHomeomorph.{u} |>.trans
    (AddCircle.homeoIccQuot (2 : ℝ) 0).symm |>.trans
      (AddCircle.homeomorphCircle (by norm_num : (2 : ℝ) ≠ 0)) |>.trans
        Homeomorph.ulift.symm

/-- The point retained by the one-cell attachment corresponds to `1` on the
circle. -/
@[simp] theorem circleOneCellHomeomorph_basepoint :
    circleOneCellHomeomorph.{u}
        (ConeAttachment.base
          (fun _ : ((TopCat.diskBoundary.{u} 1 : TopCat.{u}) : Type u) ↦
            PUnit.unit)
          PUnit.unit) =
      ULift.up (1 : _root_.Circle) := by
  change ULift.up
      (AddCircle.homeomorphCircle (by norm_num : (2 : ℝ) ≠ 0)
        ((AddCircle.homeoIccQuot (2 : ℝ) 0).symm
          (ConeAttachment.coneToIntervalQuot
            (ConeAttachment.base ConeAttachment.pointAttachingMap PUnit.unit)))) = _
  rw [ConeAttachment.coneToIntervalQuot_basepoint]
  change ULift.up
      (AddCircle.homeomorphCircle (by norm_num : (2 : ℝ) ≠ 0)
        (0 : AddCircle (2 : ℝ))) = _
  simp [AddCircle.homeomorphCircle_apply]

end Hatcher.VanKampen
