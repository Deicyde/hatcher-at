import Hatcher.VanKampen.IndexedConeAttachment

/-!
# Explicit models for abstract cell attachments

This module compares a `HomotopicalAlgebra.AttachCells` pushout with the
explicit indexed cone attachment built from its attaching maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat

namespace Hatcher.VanKampen.CellAttachment

universe u

variable {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}

/-- The attaching map of one cell in an abstract `AttachCells` presentation. -/
def attachingMap
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (i : c.ι) :
    ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u) → X :=
  c.cofan₁.inj i ≫ c.g₁

theorem continuous_attachingMap
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (i : c.ι) : Continuous (attachingMap c i) :=
  (c.cofan₁.inj i ≫ c.g₁).hom.continuous

private noncomputable def modelCells
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f) :
    AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n)
      (IndexedConeAttachment.baseHom (attachingMap c)) :=
  IndexedConeAttachment.attachCells_basicCell n (attachingMap c)
    (continuous_attachingMap c)

private noncomputable def boundaryCofanIso
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f) :
    c.cofan₁.pt ≅ (modelCells c).cofan₁.pt :=
  c.isColimit₁.coconePointUniqueUpToIso (modelCells c).isColimit₁

private noncomputable def diskCofanIso
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f) :
    c.cofan₂.pt ≅ (modelCells c).cofan₂.pt :=
  c.isColimit₂.coconePointUniqueUpToIso (modelCells c).isColimit₂

private theorem inj_boundaryCofanIso_hom
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (i : c.ι) :
    c.cofan₁.inj i ≫ (boundaryCofanIso c).hom =
      (modelCells c).cofan₁.inj (show (modelCells c).ι from i) := by
  exact c.isColimit₁.comp_coconePointUniqueUpToIso_hom
    (modelCells c).isColimit₁ ⟨i⟩

private theorem inj_diskCofanIso_hom
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (i : c.ι) :
    c.cofan₂.inj i ≫ (diskCofanIso c).hom =
      (modelCells c).cofan₂.inj (show (modelCells c).ι from i) := by
  exact c.isColimit₂.comp_coconePointUniqueUpToIso_hom
    (modelCells c).isColimit₂ ⟨i⟩

private theorem model_inj_g₁
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (i : c.ι) :
    (modelCells c).cofan₁.inj (show (modelCells c).ι from i) ≫
      (modelCells c).g₁ = c.cofan₁.inj i ≫ c.g₁ := by
  ext x
  rfl

private theorem g₁_boundaryCofanIso_hom
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f) :
    c.g₁ ≫ (Iso.refl X).hom =
      (boundaryCofanIso c).hom ≫ (modelCells c).g₁ := by
  change c.g₁ = (boundaryCofanIso c).hom ≫ (modelCells c).g₁
  apply Cofan.IsColimit.hom_ext c.isColimit₁
  intro i
  rw [← Category.assoc, inj_boundaryCofanIso_hom]
  exact (model_inj_g₁ c i).symm

private theorem m_diskCofanIso_hom
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f) :
    c.m ≫ (diskCofanIso c).hom =
      (boundaryCofanIso c).hom ≫ (modelCells c).m := by
  apply Cofan.IsColimit.hom_ext c.isColimit₁
  intro i
  calc
    c.cofan₁.inj i ≫ (c.m ≫ (diskCofanIso c).hom) =
        (c.cofan₁.inj i ≫ c.m) ≫ (diskCofanIso c).hom :=
      (Category.assoc _ _ _).symm
    _ = (TopCat.RelativeCWComplex.basicCell n (c.π i) ≫ c.cofan₂.inj i) ≫
        (diskCofanIso c).hom := by rw [c.hm]
    _ = TopCat.RelativeCWComplex.basicCell n (c.π i) ≫
        (c.cofan₂.inj i ≫ (diskCofanIso c).hom) := Category.assoc _ _ _
    _ = TopCat.RelativeCWComplex.basicCell n (c.π i) ≫
        (modelCells c).cofan₂.inj (show (modelCells c).ι from i) := by
      rw [inj_diskCofanIso_hom]
    _ = (modelCells c).cofan₁.inj (show (modelCells c).ι from i) ≫
        (modelCells c).m :=
      ((modelCells c).hm (show (modelCells c).ι from i)).symm
    _ = (c.cofan₁.inj i ≫ (boundaryCofanIso c).hom) ≫
        (modelCells c).m := by rw [inj_boundaryCofanIso_hom]
    _ = c.cofan₁.inj i ≫
        ((boundaryCofanIso c).hom ≫ (modelCells c).m) := Category.assoc _ _ _

private noncomputable def isPushout_modelPresentation
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f) :
    IsPushout (modelCells c).g₁ (modelCells c).m f
      ((diskCofanIso c).inv ≫ c.g₂) := by
  apply c.isPushout.of_iso (boundaryCofanIso c) (Iso.refl X)
    (diskCofanIso c) (Iso.refl Y)
  · exact g₁_boundaryCofanIso_hom c
  · exact m_diskCofanIso_hom c
  · simp
  · simp

/-- The target of an abstract cell attachment is canonically isomorphic to the
explicit indexed cone attachment of its attaching maps. -/
noncomputable def modelIso
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f) :
    Y ≅ TopCat.of (IndexedConeAttachment (attachingMap c)) :=
  (isPushout_modelPresentation c).isoIsPushout X
    (modelCells c).cofan₂.pt (modelCells c).isPushout

@[reassoc]
theorem f_modelIso_hom
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f) :
    f ≫ (modelIso c).hom = IndexedConeAttachment.baseHom (attachingMap c) := by
  exact (isPushout_modelPresentation c).inl_isoIsPushout_hom X
    (modelCells c).cofan₂.pt (modelCells c).isPushout

/-- The `i`-th standard disk in the explicit indexed model. -/
noncomputable def modelDiskHom
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (i : c.ι) :
    (TopCat.disk.{u} n : TopCat.{u}) ⟶
      TopCat.of (IndexedConeAttachment (attachingMap c)) :=
  (modelCells c).cell (show (modelCells c).ι from i)

private theorem g₂_modelIso_hom
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f) :
    c.g₂ ≫ (modelIso c).hom =
      (diskCofanIso c).hom ≫ (modelCells c).g₂ := by
  rw [← cancel_epi (diskCofanIso c).inv]
  simpa only [modelIso, Category.assoc, Iso.inv_hom_id_assoc] using
    (isPushout_modelPresentation c).inr_isoIsPushout_hom X
      (modelCells c).cofan₂.pt (modelCells c).isPushout

@[reassoc]
theorem cell_modelIso_hom
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (i : c.ι) :
    c.cell i ≫ (modelIso c).hom = modelDiskHom c i := by
  rw [AttachCells.cell_def, modelDiskHom, AttachCells.cell_def]
  rw [Category.assoc, g₂_modelIso_hom]
  rw [← Category.assoc, inj_diskCofanIso_hom]

end Hatcher.VanKampen.CellAttachment
