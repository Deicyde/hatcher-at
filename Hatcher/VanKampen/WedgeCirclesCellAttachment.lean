import Hatcher.VanKampen.CircleOneCell
import Hatcher.VanKampen.IndexedConeAttachment
import Hatcher.VanKampen.PointedWedgeUniversal

/-!
# A wedge of circles as an indexed one-cell attachment

This module presents the canonical map from a point to the wedge point as an
attachment of one standard one-cell for each wedge summand.
-/

noncomputable section

open CategoryTheory HomotopicalAlgebra
open scoped TopCat unitInterval

namespace Hatcher

universe u

private abbrev BoundaryOne : Type u :=
  ((TopCat.diskBoundary.{u} 1 : TopCat.{u}) : Type u)

private def wedgeCirclesAttachingMap {ι : Type u} :
    ∀ _ : ι, BoundaryOne.{u} → PUnit.{u + 1} :=
  fun _ _ => PUnit.unit

private def indexedToConeWedgeRaw {ι : Type u} :
    VanKampen.IndexedConeAttachment.Prequotient PUnit.{u + 1}
        (fun _ : ι => BoundaryOne.{u}) →
      PointedWedge
        (fun i : ι => VanKampen.ConeAttachment
          (wedgeCirclesAttachingMap (ι := ι) i))
        (fun i : ι => VanKampen.ConeAttachment.base
          (wedgeCirclesAttachingMap (ι := ι) i) PUnit.unit)
  | Sum.inl _ => PointedWedge.basepoint _
  | Sum.inr ⟨i, Sum.inl _⟩ =>
      PointedWedge.inclusion _ i
        (VanKampen.ConeAttachment.apex (wedgeCirclesAttachingMap i))
  | Sum.inr ⟨i, Sum.inr (s, t)⟩ =>
      PointedWedge.inclusion _ i
        (VanKampen.ConeAttachment.cylinder (wedgeCirclesAttachingMap i) s t)

private theorem indexedToConeWedgeRaw_normalForm {ι : Type u}
    (z : VanKampen.IndexedConeAttachment.Prequotient PUnit.{u + 1}
      (fun _ : ι => BoundaryOne.{u})) :
    indexedToConeWedgeRaw
        (VanKampen.IndexedConeAttachment.normalForm
          wedgeCirclesAttachingMap z) =
      indexedToConeWedgeRaw z := by
  rcases z with x | ⟨i, z⟩
  · obtain rfl : x = PUnit.unit := Subsingleton.elim _ _
    rfl
  · rcases z with a | ⟨s, t⟩
    · obtain rfl : a = () := Subsingleton.elim _ _
      rfl
    · by_cases h0 : t = 0
      · subst t
        simp [VanKampen.IndexedConeAttachment.normalForm,
          indexedToConeWedgeRaw]
      · by_cases h1 : t = 1
        · subst t
          simp [VanKampen.IndexedConeAttachment.normalForm,
            indexedToConeWedgeRaw, PointedWedge.inclusion_basepoint]
        · simp [VanKampen.IndexedConeAttachment.normalForm,
            indexedToConeWedgeRaw, h0, h1]

private def indexedToConeWedge {ι : Type u} :
    VanKampen.IndexedConeAttachment
        (wedgeCirclesAttachingMap (ι := ι)) →
      PointedWedge
        (fun i : ι => VanKampen.ConeAttachment
          (wedgeCirclesAttachingMap (ι := ι) i))
        (fun i : ι => VanKampen.ConeAttachment.base
          (wedgeCirclesAttachingMap (ι := ι) i) PUnit.unit) :=
  Quotient.lift indexedToConeWedgeRaw (by
    intro a b hab
    change VanKampen.IndexedConeAttachment.normalForm
        wedgeCirclesAttachingMap a =
      VanKampen.IndexedConeAttachment.normalForm
        wedgeCirclesAttachingMap b at hab
    rw [← indexedToConeWedgeRaw_normalForm a,
      ← indexedToConeWedgeRaw_normalForm b, hab])

private theorem continuous_indexedToConeWedge {ι : Type u} :
    Continuous (indexedToConeWedge (ι := ι)) := by
  apply Continuous.quotient_lift
  rw [continuous_sum_dom]
  constructor
  · exact continuous_const
  · rw [continuous_sigma_iff]
    intro i
    rw [continuous_sum_dom]
    constructor
    · exact continuous_const
    · simpa [indexedToConeWedge, indexedToConeWedgeRaw,
        VanKampen.IndexedConeAttachment.quotientMk, Function.comp_def] using
        (PointedWedge.continuous_inclusion
          (fun i : ι => VanKampen.ConeAttachment.base
            (wedgeCirclesAttachingMap (ι := ι) i) PUnit.unit) i).comp
          (VanKampen.ConeAttachment.continuous_cylinder
            (wedgeCirclesAttachingMap (ι := ι) i))

private def coneToIndexedRaw {ι : Type u} (i : ι) :
    VanKampen.ConeAttachment.Prequotient PUnit.{u + 1} BoundaryOne.{u} →
      VanKampen.IndexedConeAttachment
        (wedgeCirclesAttachingMap (ι := ι))
  | Sum.inl _ => VanKampen.IndexedConeAttachment.base
      wedgeCirclesAttachingMap PUnit.unit
  | Sum.inr (Sum.inl _) =>
      VanKampen.IndexedConeAttachment.apex wedgeCirclesAttachingMap i
  | Sum.inr (Sum.inr (s, t)) =>
      VanKampen.IndexedConeAttachment.cylinder wedgeCirclesAttachingMap i s t

private theorem coneToIndexedRaw_normalForm {ι : Type u} (i : ι)
    (z : VanKampen.ConeAttachment.Prequotient
      PUnit.{u + 1} BoundaryOne.{u}) :
    coneToIndexedRaw i
        (VanKampen.ConeAttachment.normalForm
          (wedgeCirclesAttachingMap i) z) =
      coneToIndexedRaw i z := by
  rcases z with x | z
  · obtain rfl : x = PUnit.unit := Subsingleton.elim _ _
    rfl
  · rcases z with a | ⟨s, t⟩
    · obtain rfl : a = () := Subsingleton.elim _ _
      rfl
    · by_cases h0 : t = 0
      · subst t
        simp [VanKampen.ConeAttachment.normalForm, coneToIndexedRaw]
      · by_cases h1 : t = 1
        · subst t
          simp [VanKampen.ConeAttachment.normalForm, coneToIndexedRaw]
        · simp [VanKampen.ConeAttachment.normalForm,
            coneToIndexedRaw, h0, h1]

private def coneToIndexed {ι : Type u} (i : ι) :
    VanKampen.ConeAttachment (wedgeCirclesAttachingMap i) →
      VanKampen.IndexedConeAttachment
        (wedgeCirclesAttachingMap (ι := ι)) :=
  Quotient.lift (coneToIndexedRaw i) (by
    intro a b hab
    change VanKampen.ConeAttachment.normalForm
        (wedgeCirclesAttachingMap i) a =
      VanKampen.ConeAttachment.normalForm
        (wedgeCirclesAttachingMap i) b at hab
    rw [← coneToIndexedRaw_normalForm i a,
      ← coneToIndexedRaw_normalForm i b, hab])

private theorem continuous_coneToIndexed {ι : Type u} (i : ι) :
    Continuous (coneToIndexed i) := by
  apply Continuous.quotient_lift
  rw [continuous_sum_dom]
  constructor
  · exact continuous_const
  · rw [continuous_sum_dom]
    constructor
    · exact continuous_const
    · simpa [coneToIndexed, coneToIndexedRaw,
        VanKampen.ConeAttachment.quotientMk, Function.comp_def] using
        VanKampen.IndexedConeAttachment.continuous_cylinder
          wedgeCirclesAttachingMap i

private def coneWedgeToIndexed {ι : Type u} :
    C(PointedWedge
        (fun i : ι => VanKampen.ConeAttachment
          (wedgeCirclesAttachingMap (ι := ι) i))
        (fun i : ι => VanKampen.ConeAttachment.base
          (wedgeCirclesAttachingMap (ι := ι) i) PUnit.unit),
      VanKampen.IndexedConeAttachment
        (wedgeCirclesAttachingMap (ι := ι))) :=
  PointedWedge.desc
    (fun i : ι => VanKampen.ConeAttachment.base
      (wedgeCirclesAttachingMap (ι := ι) i) PUnit.unit)
    (VanKampen.IndexedConeAttachment.base wedgeCirclesAttachingMap PUnit.unit)
    (fun i => ⟨coneToIndexed i, continuous_coneToIndexed i⟩)
    (fun _ => rfl)

private theorem coneWedgeToIndexed_indexedToConeWedge {ι : Type u}
    (q : VanKampen.IndexedConeAttachment
      (wedgeCirclesAttachingMap (ι := ι))) :
    coneWedgeToIndexed (indexedToConeWedge q) = q := by
  induction q using Quotient.inductionOn with
  | _ z =>
    rcases z with x | ⟨i, z⟩
    · obtain rfl : x = PUnit.unit := Subsingleton.elim _ _
      rfl
    · rcases z with a | ⟨s, t⟩
      · obtain rfl : a = () := Subsingleton.elim _ _
        rfl
      · rfl

private theorem indexedToConeWedge_coneWedgeToIndexed {ι : Type u}
    (q : PointedWedge
      (fun i : ι => VanKampen.ConeAttachment
        (wedgeCirclesAttachingMap (ι := ι) i))
      (fun i : ι => VanKampen.ConeAttachment.base
        (wedgeCirclesAttachingMap (ι := ι) i) PUnit.unit)) :
    indexedToConeWedge (ι := ι) (coneWedgeToIndexed (ι := ι) q) = q := by
  induction q using Quotient.inductionOn with
  | _ z =>
    cases z with
    | none => rfl
    | some z =>
      rcases z with ⟨i, q⟩
      induction q using Quotient.inductionOn with
      | _ z =>
        rcases z with x | z
        · obtain rfl : x = PUnit.unit := Subsingleton.elim _ _
          exact (PointedWedge.inclusion_basepoint
            (fun i : ι => VanKampen.ConeAttachment.base
              (wedgeCirclesAttachingMap (ι := ι) i) PUnit.unit) i).symm
        · rcases z with a | ⟨s, t⟩
          · obtain rfl : a = () := Subsingleton.elim _ _
            rfl
          · rfl

private def indexedConeWedgeHomeomorph {ι : Type u} :
    VanKampen.IndexedConeAttachment
        (wedgeCirclesAttachingMap (ι := ι)) ≃ₜ
      PointedWedge
        (fun i : ι => VanKampen.ConeAttachment
          (wedgeCirclesAttachingMap (ι := ι) i))
        (fun i : ι => VanKampen.ConeAttachment.base
          (wedgeCirclesAttachingMap (ι := ι) i) PUnit.unit) where
  toEquiv :=
    { toFun := indexedToConeWedge
      invFun := coneWedgeToIndexed
      left_inv := coneWedgeToIndexed_indexedToConeWedge
      right_inv := indexedToConeWedge_coneWedgeToIndexed }
  continuous_toFun := continuous_indexedToConeWedge
  continuous_invFun := coneWedgeToIndexed.continuous

private def coneCircleHomeomorph {ι : Type u} (i : ι) :
    VanKampen.ConeAttachment (wedgeCirclesAttachingMap i) ≃ₜ
      _root_.Circle :=
  VanKampen.circleOneCellHomeomorph.{u}.trans Homeomorph.ulift

@[simp]
private theorem coneCircleHomeomorph_base {ι : Type u} (i : ι) :
    coneCircleHomeomorph i
        (VanKampen.ConeAttachment.base
          (wedgeCirclesAttachingMap i) PUnit.unit) =
      (1 : _root_.Circle) := by
  change Homeomorph.ulift
      (VanKampen.circleOneCellHomeomorph.{u}
        (VanKampen.ConeAttachment.base
          (fun _ : BoundaryOne.{u} => PUnit.unit) PUnit.unit)) = 1
  rw [VanKampen.circleOneCellHomeomorph_basepoint]
  rfl

private def indexedWedgeCirclesHomeomorph {ι : Type u} :
    VanKampen.IndexedConeAttachment
        (wedgeCirclesAttachingMap (ι := ι)) ≃ₜ
      PointedWedge
        (fun _ : ι => _root_.Circle) (fun _ => (1 : _root_.Circle)) :=
  (indexedConeWedgeHomeomorph (ι := ι)).trans
    (PointedWedge.homeomorphCongr
      (fun i : ι => VanKampen.ConeAttachment.base
        (wedgeCirclesAttachingMap (ι := ι) i) PUnit.unit)
      (fun _ : ι => (1 : _root_.Circle))
      (coneCircleHomeomorph (ι := ι)) (coneCircleHomeomorph_base (ι := ι)))

@[simp]
private theorem indexedWedgeCirclesHomeomorph_base {ι : Type u} :
    indexedWedgeCirclesHomeomorph
        (VanKampen.IndexedConeAttachment.base
          (wedgeCirclesAttachingMap (ι := ι)) PUnit.unit) =
      PointedWedge.basepoint (fun _ : ι => (1 : _root_.Circle)) :=
  rfl

/-- The canonical map from a point to the basepoint of a wedge of circles. -/
def wedgeCirclesBaseHom {ι : Type u} :
    TopCat.of PUnit.{u + 1} ⟶
      TopCat.of (PointedWedge
        (fun _ : ι => _root_.Circle) (fun _ => (1 : _root_.Circle))) :=
  TopCat.ofHom ⟨fun _ => PointedWedge.basepoint
    (fun _ : ι => (1 : _root_.Circle)), continuous_const⟩

private def indexedWedgeCirclesArrowIso {ι : Type u} :
    Arrow.mk (VanKampen.IndexedConeAttachment.baseHom
      (wedgeCirclesAttachingMap (ι := ι))) ≅
      Arrow.mk (wedgeCirclesBaseHom (ι := ι)) :=
  Arrow.isoMk (Iso.refl _)
    (TopCat.isoOfHomeo (indexedWedgeCirclesHomeomorph (ι := ι))) (by
      ext x
      change PUnit at x
      obtain rfl : x = PUnit.unit := Subsingleton.elim _ _
      exact indexedWedgeCirclesHomeomorph_base)

/-- The wedge of circles is obtained from its basepoint by attaching one
standard one-cell for every circle. -/
noncomputable def wedgeCirclesAttachCells {ι : Type u} :
    AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} 1)
      (wedgeCirclesBaseHom (ι := ι)) :=
  (VanKampen.IndexedConeAttachment.attachCells_basicCell 1
    (wedgeCirclesAttachingMap (ι := ι))
    (fun _ => continuous_const)).ofArrowIso
      (indexedWedgeCirclesArrowIso (ι := ι))

end Hatcher
