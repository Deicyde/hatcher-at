import Hatcher.VanKampen.AuxiliaryCellAttachmentBasepoint
import Hatcher.VanKampen.AuxiliaryCellAttachmentOverlapPiece
import Hatcher.VanKampen.AuxiliaryCellAttachmentUpperContractible
import Hatcher.VanKampen.CellAttachmentModel
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The open-cover model for an abstract cell attachment

This file packages Hatcher's strip-enlarged open cover for an abstract
`AttachCells` presentation.  The categorical target is first identified with
the explicit indexed cone attachment, after which the auxiliary-space
constructions supply the deformation retracts, the binary cover, its pointed
overlap cover, and the basepoint-change data used in the fundamental-group
calculation.
-/

noncomputable section

open CategoryTheory HomotopicalAlgebra Set Topology
open scoped TopCat ContinuousMap

namespace Hatcher.VanKampen

universe u

namespace CellAttachmentCover

/-- The common boundary type for a family of standard `n`-cells. -/
abbrev Boundary (n : ℕ) : Type u :=
  ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u)

/-- The family of attaching maps extracted from an abstract cell attachment. -/
abbrev attachingFamily {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f) :
    c.ι → Boundary.{u} n → X :=
  CellAttachment.attachingMap c

/-- Use the chosen boundary point in every cell. -/
def boundaryPointFamily {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (s₀ : Boundary.{u} n) : c.ι → Boundary.{u} n :=
  fun _ ↦ s₀

/-- Hatcher's strip-enlarged space associated to the abstract attachment. -/
abbrev Space {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (x₀ : X) (s₀ : Boundary.{u} n)
    (gamma : ∀ i : c.ι, Path x₀ (attachingFamily c i s₀)) : Type u :=
  AuxiliaryCellAttachment (attachingFamily c) (boundaryPointFamily c s₀) x₀ gamma

/-- The base-side member of the auxiliary binary cover. -/
abbrev baseCover {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (x₀ : X) (s₀ : Boundary.{u} n)
    (gamma : ∀ i : c.ι, Path x₀ (attachingFamily c i s₀)) :
    Set (Space c x₀ s₀ gamma) :=
  AuxiliaryCellAttachment.baseCover
    (attachingFamily c) (boundaryPointFamily c s₀) x₀ gamma

/-- The contractible upper member of the auxiliary binary cover. -/
abbrev upperCover {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (x₀ : X) (s₀ : Boundary.{u} n)
    (gamma : ∀ i : c.ι, Path x₀ (attachingFamily c i s₀)) :
    Set (Space c x₀ s₀ gamma) :=
  AuxiliaryCellAttachment.upperCover
    (attachingFamily c) (boundaryPointFamily c s₀) x₀ gamma

/-- The binary cover, ordered with the base-side member first. -/
abbrev binaryCover {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (x₀ : X) (s₀ : Boundary.{u} n)
    (gamma : ∀ i : c.ι, Path x₀ (attachingFamily c i s₀)) :
    Fin 2 → Set (Space c x₀ s₀ gamma) :=
  AuxiliaryCellAttachment.binaryCover
    (attachingFamily c) (boundaryPointFamily c s₀) x₀ gamma

/-- The overlap of the two auxiliary cover members. -/
abbrev Overlap {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (x₀ : X) (s₀ : Boundary.{u} n)
    (gamma : ∀ i : c.ι, Path x₀ (attachingFamily c i s₀)) : Type u :=
  AuxiliaryCellAttachment.CoverIntersection
    (attachingFamily c) (boundaryPointFamily c s₀) x₀ gamma

/-- The overlap piece corresponding to one attached cell. -/
abbrev overlapPiece {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (x₀ : X) (s₀ : Boundary.{u} n)
    (gamma : ∀ i : c.ι, Path x₀ (attachingFamily c i s₀))
    (i : c.ι) : Set (Overlap c x₀ s₀ gamma) :=
  AuxiliaryCellAttachment.intersectionPiece
    (attachingFamily c) (boundaryPointFamily c s₀) x₀ gamma i

private theorem pathConnectedSpace_boundary {n : ℕ} (hn : 1 < n) :
    PathConnectedSpace (Boundary.{u} n) := by
  letI : PathConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [← isPathConnected_iff_pathConnectedSpace]
    apply isPathConnected_sphere
    · rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      exact_mod_cast hn
    · exact zero_le_one
  change PathConnectedSpace
    (ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
  exact ULift.up_surjective.pathConnectedSpace continuous_uliftUp

private theorem pathConnectedSpace_overlap
    {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (x₀ : X) (s₀ : Boundary.{u} n)
    (gamma : ∀ i : c.ι, Path x₀ (attachingFamily c i s₀))
    [Nonempty c.ι] [PathConnectedSpace (Boundary.{u} n)] :
    PathConnectedSpace (Overlap c x₀ s₀ gamma) := by
  let z₀ := AuxiliaryCellAttachment.coverIntersectionBasepoint
    (attachingFamily c) (boundaryPointFamily c s₀) x₀ gamma
  rw [pathConnectedSpace_iff_univ]
  refine ⟨z₀, Set.mem_univ z₀, ?_⟩
  intro z _
  have hzCover : z ∈ ⋃ i, overlapPiece c x₀ s₀ gamma i :=
    AuxiliaryCellAttachment.univ_subset_iUnion_intersectionPiece
      (attachingFamily c) (boundaryPointFamily c s₀) x₀ gamma
      (Set.mem_univ z)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzCover
  have hz₀i : z₀ ∈ overlapPiece c x₀ s₀ gamma i :=
    AuxiliaryCellAttachment.coverIntersectionBasepoint_mem_intersectionPiece
      (attachingFamily c) (boundaryPointFamily c s₀) x₀ gamma i
  have hpiece : IsPathConnected (overlapPiece c x₀ s₀ gamma i) := by
    simpa only [inter_self] using
      AuxiliaryCellAttachment.isPathConnected_intersectionPiece_inter
        (attachingFamily c) (boundaryPointFamily c s₀) x₀ gamma i i
  exact (hpiece.joinedIn z₀ hz₀i z hi).mono (Set.subset_univ _)

private theorem isPathConnected_binaryCover
    {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (x₀ : X) (s₀ : Boundary.{u} n)
    (gamma : ∀ i : c.ι, Path x₀ (attachingFamily c i s₀))
    [PathConnectedSpace X] (i : Fin 2) :
    IsPathConnected (binaryCover c x₀ s₀ gamma i) := by
  fin_cases i
  · change IsPathConnected (baseCover c x₀ s₀ gamma)
    rw [isPathConnected_iff_pathConnectedSpace]
    exact (AuxiliaryCellAttachment.baseCoverStrongDeformationRetract
      (attachingFamily c) (boundaryPointFamily c s₀) x₀ gamma
      (CellAttachment.continuous_attachingMap c)).pathConnectedSpace
  · change IsPathConnected (upperCover c x₀ s₀ gamma)
    rw [isPathConnected_iff_pathConnectedSpace]
    letI : ContractibleSpace (upperCover c x₀ s₀ gamma) :=
      AuxiliaryCellAttachment.contractibleSpace_upperCover
        (attachingFamily c) (boundaryPointFamily c s₀) x₀ gamma
    infer_instance

private theorem isPathConnected_binaryIntersection
    {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (x₀ : X) (s₀ : Boundary.{u} n)
    (gamma : ∀ i : c.ι, Path x₀ (attachingFamily c i s₀))
    [Nonempty c.ι] [PathConnectedSpace (Boundary.{u} n)] :
    IsPathConnected
      (binaryCover c x₀ s₀ gamma 0 ∩ binaryCover c x₀ s₀ gamma 1) := by
  change IsPathConnected
    (baseCover c x₀ s₀ gamma ∩ upperCover c x₀ s₀ gamma)
  rw [isPathConnected_iff_pathConnectedSpace]
  exact pathConnectedSpace_overlap c x₀ s₀ gamma

end CellAttachmentCover

/-- The complete auxiliary-cover package associated to a nonempty family of
standard cells.  Its fields use the canonical constructions, so no transport
between competing quotient models is needed downstream. -/
structure CellAttachmentCover
    {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (x₀ : X) (s₀ : CellAttachmentCover.Boundary.{u} n)
    (gamma : ∀ i : c.ι,
      Path x₀ (CellAttachmentCover.attachingFamily c i s₀)) where
  modelIso :
    Y ≅ TopCat.of (IndexedConeAttachment (CellAttachmentCover.attachingFamily c))
  modelIso_base :
    f ≫ modelIso.hom =
      IndexedConeAttachment.baseHom (CellAttachmentCover.attachingFamily c)
  modelIso_cell : ∀ i : c.ι,
    c.cell i ≫ modelIso.hom = CellAttachment.modelDiskHom c i
  attachmentRetract :
    Hatcher.StrongDeformationRetract
      (AuxiliaryCellAttachment.attachment
        (CellAttachmentCover.attachingFamily c)
        (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma)
  attachment_base : ∀ x : X,
    AuxiliaryCellAttachment.attachment
        (CellAttachmentCover.attachingFamily c)
        (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma
        (IndexedConeAttachment.base
          (CellAttachmentCover.attachingFamily c) x) =
      AuxiliaryCellAttachment.base
        (CellAttachmentCover.attachingFamily c)
        (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma x
  binaryCoverOpen : ∀ i,
    IsOpen (CellAttachmentCover.binaryCover c x₀ s₀ gamma i)
  binaryCoverCovers :
    Set.univ ⊆ ⋃ i, CellAttachmentCover.binaryCover c x₀ s₀ gamma i
  binaryCoverPathConnected : ∀ i,
    IsPathConnected (CellAttachmentCover.binaryCover c x₀ s₀ gamma i)
  binaryIntersectionPathConnected :
    IsPathConnected
      (CellAttachmentCover.binaryCover c x₀ s₀ gamma 0 ∩
        CellAttachmentCover.binaryCover c x₀ s₀ gamma 1)
  overlapBasepointMem : ∀ i,
    AuxiliaryCellAttachment.overlapBasepoint
        (CellAttachmentCover.attachingFamily c)
        (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma ∈
      CellAttachmentCover.binaryCover c x₀ s₀ gamma i
  baseCoverRetract :
    Hatcher.StrongDeformationRetract
      (AuxiliaryCellAttachment.baseToBaseCover
        (CellAttachmentCover.attachingFamily c)
        (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma)
  upperContraction :
    (ContinuousMap.id (CellAttachmentCover.upperCover c x₀ s₀ gamma)).HomotopyRel
      (ContinuousMap.const (CellAttachmentCover.upperCover c x₀ s₀ gamma)
        (AuxiliaryCellAttachment.upperOverlapBasepoint
          (CellAttachmentCover.attachingFamily c)
          (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma))
      {AuxiliaryCellAttachment.upperOverlapBasepoint
        (CellAttachmentCover.attachingFamily c)
        (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma}
  upperContractible :
    ContractibleSpace (CellAttachmentCover.upperCover c x₀ s₀ gamma)
  overlapOpenCover :
    (∀ i, IsOpen (CellAttachmentCover.overlapPiece c x₀ s₀ gamma i)) ∧
      (Set.univ ⊆ ⋃ i, CellAttachmentCover.overlapPiece c x₀ s₀ gamma i) ∧
      (∀ i j, IsPathConnected
        (CellAttachmentCover.overlapPiece c x₀ s₀ gamma i ∩
          CellAttachmentCover.overlapPiece c x₀ s₀ gamma j)) ∧
      (∀ i, AuxiliaryCellAttachment.coverIntersectionBasepoint
        (CellAttachmentCover.attachingFamily c)
        (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma ∈
          CellAttachmentCover.overlapPiece c x₀ s₀ gamma i)
  overlapPieceEquiv : ∀ i : c.ι,
    ↑(CellAttachmentCover.overlapPiece c x₀ s₀ gamma i) ≃ₕ
      CellAttachmentCover.Boundary.{u} n
  overlapPieceEquiv_basepoint : ∀ i : c.ι,
    overlapPieceEquiv i
        (AuxiliaryCellAttachment.intersectionPieceBasepoint
          (CellAttachmentCover.attachingFamily c)
          (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma i) =
      s₀
  spinePath :
    Path
      (AuxiliaryCellAttachment.baseCoverBasepoint
        (CellAttachmentCover.attachingFamily c)
        (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma)
      (AuxiliaryCellAttachment.baseToBaseCover
        (CellAttachmentCover.attachingFamily c)
        (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma x₀)
  baseCoverRetract_basepoint :
    baseCoverRetract.retract
        (AuxiliaryCellAttachment.baseCoverBasepoint
          (CellAttachmentCover.attachingFamily c)
          (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma) =
      x₀
  baseCoverRetract_base : ∀ x : X,
    baseCoverRetract.retract
        (AuxiliaryCellAttachment.baseToBaseCover
          (CellAttachmentCover.attachingFamily c)
          (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma x) =
      x
  spinePathClass :
    ((Path.Homotopic.Quotient.mk spinePath).map baseCoverRetract.retract).cast
        baseCoverRetract_basepoint.symm
        (baseCoverRetract_base x₀).symm =
      Path.Homotopic.Quotient.refl x₀
  baseFundamentalGroupEquiv :
    FundamentalGroup
        (CellAttachmentCover.baseCover c x₀ s₀ gamma)
        (AuxiliaryCellAttachment.baseCoverBasepoint
          (CellAttachmentCover.attachingFamily c)
          (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma) ≃*
      FundamentalGroup X x₀
  baseFundamentalGroupEquiv_formula :
    baseFundamentalGroupEquiv.toMonoidHom =
      (FundamentalGroup.mapOfEq baseCoverRetract.retract
        (baseCoverRetract_base x₀)).comp
        (FundamentalGroup.fundamentalGroupMulEquivOfPath spinePath).toMonoidHom

/-- Hatcher's auxiliary open-cover package exists for every nonempty family
of standard `n`-cells with `1 < n`. -/
theorem exists_cellAttachmentCover
    {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    [PathConnectedSpace X] [Nonempty c.ι]
    (hn : 1 < n) (x₀ : X) (s₀ : CellAttachmentCover.Boundary.{u} n)
    (gamma : ∀ i : c.ι,
      Path x₀ (CellAttachmentCover.attachingFamily c i s₀)) :
    Nonempty (CellAttachmentCover c x₀ s₀ gamma) := by
  letI : PathConnectedSpace (CellAttachmentCover.Boundary.{u} n) :=
    CellAttachmentCover.pathConnectedSpace_boundary hn
  let hf : ∀ i, Continuous (CellAttachmentCover.attachingFamily c i) :=
    CellAttachment.continuous_attachingMap c
  refine ⟨{
    modelIso := CellAttachment.modelIso c
    modelIso_base := CellAttachment.f_modelIso_hom c
    modelIso_cell := CellAttachment.cell_modelIso_hom c
    attachmentRetract :=
      AuxiliaryCellAttachment.attachmentStrongDeformationRetract
        (CellAttachmentCover.attachingFamily c)
        (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma
    attachment_base := AuxiliaryCellAttachment.attachment_base
      (CellAttachmentCover.attachingFamily c)
      (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma
    binaryCoverOpen := AuxiliaryCellAttachment.isOpen_binaryCover
      (CellAttachmentCover.attachingFamily c)
      (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma
    binaryCoverCovers := AuxiliaryCellAttachment.univ_subset_iUnion_binaryCover
      (CellAttachmentCover.attachingFamily c)
      (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma
    binaryCoverPathConnected :=
      CellAttachmentCover.isPathConnected_binaryCover c x₀ s₀ gamma
    binaryIntersectionPathConnected :=
      CellAttachmentCover.isPathConnected_binaryIntersection c x₀ s₀ gamma
    overlapBasepointMem := AuxiliaryCellAttachment.overlapBasepoint_mem_binaryCover
      (CellAttachmentCover.attachingFamily c)
      (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma
    baseCoverRetract := AuxiliaryCellAttachment.baseCoverStrongDeformationRetract
      (CellAttachmentCover.attachingFamily c)
      (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma hf
    upperContraction := AuxiliaryCellAttachment.upperContraction
      (CellAttachmentCover.attachingFamily c)
      (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma
    upperContractible := AuxiliaryCellAttachment.contractibleSpace_upperCover
      (CellAttachmentCover.attachingFamily c)
      (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma
    overlapOpenCover := AuxiliaryCellAttachment.isOpenCover_intersectionPieces
      (CellAttachmentCover.attachingFamily c)
      (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma
    overlapPieceEquiv := AuxiliaryCellAttachment.intersectionPieceHomotopyEquivBoundary
      (CellAttachmentCover.attachingFamily c)
      (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma
    overlapPieceEquiv_basepoint :=
      AuxiliaryCellAttachment.intersectionPieceHomotopyEquivBoundary_basepoint
        (CellAttachmentCover.attachingFamily c)
        (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma
    spinePath := AuxiliaryCellAttachment.basepointPath
      (CellAttachmentCover.attachingFamily c)
      (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma
    baseCoverRetract_basepoint :=
      AuxiliaryCellAttachment.baseCoverRetraction_overlapBasepoint
        (CellAttachmentCover.attachingFamily c)
        (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma hf
    baseCoverRetract_base := AuxiliaryCellAttachment.baseCoverRetraction_base
      (CellAttachmentCover.attachingFamily c)
      (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma hf
    spinePathClass := AuxiliaryCellAttachment.basepointPath_class_map_retraction
      (CellAttachmentCover.attachingFamily c)
      (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma hf
    baseFundamentalGroupEquiv :=
      AuxiliaryCellAttachment.baseCoverFundamentalGroupEquiv
        (CellAttachmentCover.attachingFamily c)
        (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma hf
    baseFundamentalGroupEquiv_formula :=
      AuxiliaryCellAttachment.baseCoverFundamentalGroupEquiv_toMonoidHom
        (CellAttachmentCover.attachingFamily c)
        (CellAttachmentCover.boundaryPointFamily c s₀) x₀ gamma hf }⟩

end Hatcher.VanKampen
