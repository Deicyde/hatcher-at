import Hatcher.VanKampen.CellAttachmentTwo
import Hatcher.VanKampen.DiskBoundaryRepresentative
import Hatcher.VanKampen.IndexedConeAttachment
import Hatcher.VanKampen.WedgeCircles

/-!
# Relator two-cell attachments

This file realizes free-group relators by based disk-boundary maps into a
wedge of circles and packages the resulting presentation complex as an
indexed attachment of standard two-cells.
-/

noncomputable section

open CategoryTheory FundamentalGroupoid HomotopicalAlgebra
open scoped ContinuousMap TopCat

namespace Hatcher

universe u

/-- A based disk-boundary map spelling a free-group relator in the wedge of
circles. -/
noncomputable def wedgeCircleRelatorAttachingMap {S : Type u}
    (r : FreeGroup S) :
    C(((TopCat.diskBoundary.{u} 2 : TopCat.{u}) : Type u),
      PointedWedge (fun _ : S => _root_.Circle)
        (fun _ => (1 : _root_.Circle))) :=
  diskBoundaryMapOfFundamentalGroup
    (fundamentalGroupEquivWedgeCircles.symm r)

/-- A relator attaching map preserves the standard basepoint. -/
@[simp]
theorem wedgeCircleRelatorAttachingMap_basepoint {S : Type u}
    (r : FreeGroup S) :
    wedgeCircleRelatorAttachingMap r diskBoundaryTwoBasepoint.{u} =
      PointedWedge.basepoint (fun _ : S => (1 : _root_.Circle)) :=
  diskBoundaryMapOfFundamentalGroup_basepoint
    (fundamentalGroupEquivWedgeCircles.symm r)

/-- The standard boundary generator of a relator attaching map represents
the specified free-group element. -/
@[simp]
theorem wedgeCircleRelatorAttachingMap_generator {S : Type u}
    (r : FreeGroup S) :
    fundamentalGroupEquivWedgeCircles
      (FundamentalGroup.mapOfEq (wedgeCircleRelatorAttachingMap r)
        (wedgeCircleRelatorAttachingMap_basepoint r)
        (FundamentalGroup.fromPath
          (.mk diskBoundaryTwoLoop.{u}))) = r := by
  unfold wedgeCircleRelatorAttachingMap
  rw [diskBoundaryMapOfFundamentalGroup_generator,
    MulEquiv.apply_symm_apply]

/-- The family of disk-boundary maps indexed by a set of relators. -/
noncomputable def presentationRelatorAttachingMap {S : Type u}
    (rels : Set (FreeGroup S)) (r : rels) :
    ((TopCat.diskBoundary.{u} 2 : TopCat.{u}) : Type u) →
      PointedWedge (fun _ : S => _root_.Circle)
        (fun _ => (1 : _root_.Circle)) :=
  wedgeCircleRelatorAttachingMap r.1

theorem continuous_presentationRelatorAttachingMap {S : Type u}
    (rels : Set (FreeGroup S)) (r : rels) :
    Continuous (presentationRelatorAttachingMap rels r) :=
  (wedgeCircleRelatorAttachingMap r.1).continuous

/-- Each relator map sends the disk-boundary basepoint to the wedge point. -/
@[simp]
theorem presentationRelatorAttachingMap_basepoint {S : Type u}
    (rels : Set (FreeGroup S)) (r : rels) :
    presentationRelatorAttachingMap rels r diskBoundaryTwoBasepoint.{u} =
      PointedWedge.basepoint (fun _ : S => (1 : _root_.Circle)) :=
  wedgeCircleRelatorAttachingMap_basepoint r.1

/-- The two-dimensional presentation complex with one cell for each
relator. -/
abbrev presentationComplex {S : Type u}
    (rels : Set (FreeGroup S)) : Type u :=
  VanKampen.IndexedConeAttachment (presentationRelatorAttachingMap rels)

/-- The image of the wedge point in the presentation complex. -/
def presentationComplexBasepoint {S : Type u}
    (rels : Set (FreeGroup S)) : presentationComplex rels :=
  VanKampen.IndexedConeAttachment.base
    (presentationRelatorAttachingMap rels)
    (PointedWedge.basepoint (fun _ : S => (1 : _root_.Circle)))

/-- The inclusion of the wedge of circles into the presentation complex. -/
def presentationComplexBaseHom {S : Type u}
    (rels : Set (FreeGroup S)) :
    TopCat.of
        (PointedWedge (fun _ : S => _root_.Circle)
          (fun _ => (1 : _root_.Circle))) ⟶
      TopCat.of (presentationComplex rels) :=
  VanKampen.IndexedConeAttachment.baseHom
    (presentationRelatorAttachingMap rels)

/-- The presentation complex is an indexed attachment of standard
two-cells. -/
noncomputable def presentationRelatorAttachCells {S : Type u}
    (rels : Set (FreeGroup S)) :
    AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} 2)
      (presentationComplexBaseHom rels) :=
  VanKampen.IndexedConeAttachment.attachCells_basicCell 2
    (presentationRelatorAttachingMap rels)
    (continuous_presentationRelatorAttachingMap rels)

/-- The attaching family exposed by the abstract attachment is the original
relator family. -/
@[simp]
theorem presentationRelatorAttachCells_attachingFamily {S : Type u}
    (rels : Set (FreeGroup S))
    (r : (presentationRelatorAttachCells rels).ι) :
    VanKampen.CellAttachmentCover.attachingFamily
        (presentationRelatorAttachCells rels) r =
      presentationRelatorAttachingMap rels r := by
  rfl

/-- Constant paths base every relator attaching map at the wedge point. -/
def presentationRelatorBasepointPath {S : Type u}
    (rels : Set (FreeGroup S)) :
    ∀ r : (presentationRelatorAttachCells rels).ι,
      Path (PointedWedge.basepoint
          (fun _ : S => (1 : _root_.Circle)))
        (VanKampen.CellAttachmentCover.attachingFamily
          (presentationRelatorAttachCells rels) r
            diskBoundaryTwoBasepoint.{u}) :=
  fun r ↦ (Path.refl (PointedWedge.basepoint
      (fun _ : S => (1 : _root_.Circle)))).cast rfl
    (presentationRelatorAttachingMap_basepoint rels r)

private theorem fundamentalGroup_basechange_refl_cast_map_eq_mapOfEq
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (F : C(A, B)) (a : A) (b : B) (h : F a = b)
    (g : FundamentalGroup A a) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
        ((Path.refl b).cast rfl h)).symm
          (FundamentalGroup.map F a g) =
      FundamentalGroup.mapOfEq F h g := by
  subst b
  rfl

/-- Under the free-group equivalence, the loop attaching the cell indexed by
`r` is exactly the relator `r.1`. -/
@[simp]
theorem presentationRelator_twoCellAttachingLoop {S : Type u}
    (rels : Set (FreeGroup S))
    (r : (presentationRelatorAttachCells rels).ι) :
    fundamentalGroupEquivWedgeCircles
      (VanKampen.twoCellAttachingLoop
        (presentationRelatorAttachCells rels)
        (PointedWedge.basepoint
          (fun _ : S => (1 : _root_.Circle)))
        (presentationRelatorBasepointPath rels) r) = r.1 := by
  rw [show VanKampen.twoCellAttachingLoop
      (presentationRelatorAttachCells rels)
      (PointedWedge.basepoint
        (fun _ : S => (1 : _root_.Circle)))
      (presentationRelatorBasepointPath rels) r =
    FundamentalGroup.mapOfEq
      (wedgeCircleRelatorAttachingMap r.1)
      (wedgeCircleRelatorAttachingMap_basepoint r.1)
      (FundamentalGroup.fromPath
        (.mk diskBoundaryTwoLoop.{u})) by
    unfold VanKampen.twoCellAttachingLoop presentationRelatorBasepointPath
    apply fundamentalGroup_basechange_refl_cast_map_eq_mapOfEq]
  exact wedgeCircleRelatorAttachingMap_generator r.1

end Hatcher
