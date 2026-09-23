import Hatcher.Appendix.SuccessorSkeletonQuotient
import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

/-!
# Classical skeleton inclusions as cell attachments

This file packages each successor step in a classical CW complex as an
`AttachCells` square. The classical sup-norm cells are first used directly,
then transported to Mathlib's standard abstract cells.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set
open scoped TopCat

namespace Hatcher.ClassicalCW

universe u

open Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) {D : Set X} [RelCWComplex C D]

private noncomputable def skeletonLTStepCellMap
    (n : ℕ)
    (c : PushoutCocone (skeletonLTStepAttachingMap C n)
      (skeletonLTStepBoundaryInclusion C n))
    (i : RelCWComplex.cell C n) :
    C(↑(closedBall (0 : Fin n → ℝ) 1), c.pt) where
  toFun x := c.inr ⟨i, ULift.up x⟩
  continuous_toFun := c.inr.hom.continuous.comp
    (continuous_sigmaMk.comp continuous_uliftUp)

private theorem skeletonLTStep_isPushout (n : ℕ) :
    IsPushout (skeletonLTStepAttachingMap C n)
      (skeletonLTStepBoundaryInclusion C n)
      (skeletonLTInclusion C n)
      (skeletonLTStepCharacteristicMap C n) := by
  have comm := (skeletonLTStep_square C n).symm
  have hboundary
      (c : PushoutCocone (skeletonLTStepAttachingMap C n)
        (skeletonLTStepBoundaryInclusion C n)) :
      ∀ (i : RelCWComplex.cell C n)
        (x : ↑(sphere (0 : Fin n → ℝ) 1)),
        c.inl.hom (skeletonLTStepBoundaryMap C n i x) =
          skeletonLTStepCellMap C n c i ⟨x, sphere_subset_closedBall x.2⟩ := by
    intro i x
    exact ConcreteCategory.congr_hom c.condition ⟨i, ULift.up x⟩
  let d (c : PushoutCocone (skeletonLTStepAttachingMap C n)
      (skeletonLTStepBoundaryInclusion C n)) :
      TopCat.of ↑(RelCWComplex.skeletonLT C (n + 1) : Set X) ⟶ c.pt :=
    TopCat.ofHom (skeletonLTStepDesc C n c.inl.hom
      (skeletonLTStepCellMap C n c) (hboundary c))
  refine { w := comm, isColimit' := ⟨?_⟩ }
  refine PushoutCocone.IsColimit.mk comm d ?_ ?_ ?_
  · intro c
    ext x
    exact skeletonLTStepDesc_old_apply C n c.inl.hom
      (skeletonLTStepCellMap C n c) (hboundary c) x
  · intro c
    ext p
    rcases p with ⟨i, x⟩
    exact skeletonLTStepDesc_cell_apply C n c.inl.hom
      (skeletonLTStepCellMap C n c) (hboundary c) i x.down
  · intro c m hmOld hmCells
    ext y
    obtain ⟨z, rfl⟩ := surjective_skeletonLTStepJointMap C n y
    rcases z with x | ⟨i, x⟩
    · change m (skeletonLTStepOldMap C n x) =
        d c (skeletonLTStepOldMap C n x)
      calc
        _ = c.inl x := ConcreteCategory.congr_hom hmOld x
        _ = _ := (skeletonLTStepDesc_old_apply C n c.inl.hom
          (skeletonLTStepCellMap C n c) (hboundary c) x).symm
    · change m (skeletonLTStepClosedCellMap C n i x) =
        d c (skeletonLTStepClosedCellMap C n i x)
      calc
        _ = c.inr ⟨i, ULift.up x⟩ :=
          ConcreteCategory.congr_hom hmCells ⟨i, ULift.up x⟩
        _ = _ := (skeletonLTStepDesc_cell_apply C n c.inl.hom
          (skeletonLTStepCellMap C n c) (hboundary c) i x).symm

private noncomputable def skeletonLTInclusion_attachClassicalCells (n : ℕ) :
    HomotopicalAlgebra.AttachCells.{u}
      (fun _ : Unit ↦ classicalDiskBoundaryInclusion.{u} n)
      (skeletonLTInclusion C n) where
  ι := RelCWComplex.cell C n
  π := fun _ ↦ ()
  cofan₁ := skeletonLTStepBoundaryCofan C n
  cofan₂ := skeletonLTStepClosedCellCofan C n
  isColimit₁ := TopCat.sigmaCofanIsColimit _
  isColimit₂ := TopCat.sigmaCofanIsColimit _
  m := skeletonLTStepBoundaryInclusion C n
  hm i := by
    ext x
    rfl
  g₁ := skeletonLTStepAttachingMap C n
  g₂ := skeletonLTStepCharacteristicMap C n
  isPushout := skeletonLTStep_isPushout C n

/-- The inclusion into the next strict classical skeleton is an attachment by
standard abstract cells. -/
noncomputable def skeletonLTInclusion_attachCells (n : ℕ) :
    HomotopicalAlgebra.AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} n)
      (skeletonLTInclusion C n) :=
  (skeletonLTInclusion_attachClassicalCells C n).reindexCellTypes
    (TopCat.RelativeCWComplex.basicCell.{u} n) (fun _ ↦ ())
    (fun _ ↦ classicalCellArrowIso n)

/-- Inclusion of one standard classical skeleton into its successor. -/
noncomputable def skeletonInclusion (n : ℕ) :
    TopCat.of ↑(RelCWComplex.skeleton C n : Set X) ⟶
      TopCat.of ↑(RelCWComplex.skeleton C (n + 1) : Set X) :=
  skeletonLTInclusion C (n + 1)

/-- The inclusion into the next classical skeleton is an attachment by cells
of the next dimension. -/
noncomputable def skeletonInclusion_attachCells (n : ℕ) :
    HomotopicalAlgebra.AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} (n + 1))
      (skeletonInclusion C n) :=
  skeletonLTInclusion_attachCells C (n + 1)

end Hatcher.ClassicalCW
