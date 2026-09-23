import Hatcher.VanKampen.CellAttachmentModel

/-!
# Cell attachments with no cells

An abstract cell attachment indexed by an empty type is isomorphic to its
source. The isomorphism below uses the original attachment map as its inverse.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat

namespace Hatcher.VanKampen.CellAttachment

universe u

variable {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}

/-- The identity map is the attachment of an empty family of standard cells. -/
noncomputable def attachCellsId (n : ℕ) (X : TopCat.{u}) :
    AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) (𝟙 X) where
  ι := PEmpty
  π := PEmpty.elim
  cofan₁ := Cofan.mk (⊥_ TopCat.{u}) PEmpty.elim
  cofan₂ := Cofan.mk (⊥_ TopCat.{u}) PEmpty.elim
  isColimit₁ := (isColimitEquivIsInitialOfIsEmpty TopCat _).symm initialIsInitial
  isColimit₂ := (isColimitEquivIsInitialOfIsEmpty TopCat _).symm initialIsInitial
  m := 𝟙 _
  hm i := i.elim
  g₁ := initial.to X
  g₂ := initial.to X
  isPushout := IsPushout.of_id_snd

private noncomputable def modelToBaseIso
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    [IsEmpty c.ι] :
    TopCat.of (IndexedConeAttachment (attachingMap c)) ≅ X :=
  TopCat.isoOfHomeo (IndexedConeAttachment.emptyIndexHomeomorph (attachingMap c))

private noncomputable def composedTargetIso
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    [IsEmpty c.ι] : Y ≅ X :=
  (modelIso c).trans (modelToBaseIso c)

private theorem composedTargetIso_inv
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    [IsEmpty c.ι] :
    (composedTargetIso c).inv = f := by
  rw [← cancel_mono (modelIso c).hom]
  calc
    (composedTargetIso c).inv ≫ (modelIso c).hom =
        (modelToBaseIso c).inv := by simp [composedTargetIso]
    _ = IndexedConeAttachment.baseHom (attachingMap c) := by
      ext x
      rfl
    _ = f ≫ (modelIso c).hom := (f_modelIso_hom c).symm

/-- If an abstract cell attachment has no cells, its target is canonically
isomorphic to its source. The inverse is definitionally the attachment map. -/
noncomputable def targetIsoOfIsEmpty
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    [IsEmpty c.ι] : Y ≅ X where
  hom := (composedTargetIso c).hom
  inv := f
  hom_inv_id := by
    calc
      (composedTargetIso c).hom ≫ f =
          (composedTargetIso c).hom ≫ (composedTargetIso c).inv :=
        congrArg (fun k : X ⟶ Y ↦ (composedTargetIso c).hom ≫ k)
          (composedTargetIso_inv c).symm
      _ = 𝟙 Y := (composedTargetIso c).hom_inv_id
  inv_hom_id := by
    calc
      f ≫ (composedTargetIso c).hom =
          (composedTargetIso c).inv ≫ (composedTargetIso c).hom :=
        congrArg (fun k : X ⟶ Y ↦ k ≫ (composedTargetIso c).hom)
          (composedTargetIso_inv c).symm
      _ = 𝟙 X := (composedTargetIso c).inv_hom_id

@[simp]
theorem targetIsoOfIsEmpty_inv
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    [IsEmpty c.ι] :
    (targetIsoOfIsEmpty c).inv = f := rfl

@[simp]
theorem targetIsoOfIsEmpty_hom_f
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    [IsEmpty c.ι] :
    (targetIsoOfIsEmpty c).hom ≫ f = 𝟙 Y :=
  (targetIsoOfIsEmpty c).hom_inv_id

@[simp]
theorem f_targetIsoOfIsEmpty_hom
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    [IsEmpty c.ι] :
    f ≫ (targetIsoOfIsEmpty c).hom = 𝟙 X :=
  (targetIsoOfIsEmpty c).inv_hom_id

end Hatcher.VanKampen.CellAttachment
