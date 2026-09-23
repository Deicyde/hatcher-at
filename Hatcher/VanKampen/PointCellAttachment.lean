import Hatcher.VanKampen.IndexedConeAttachment

/-!
# A point as one standard zero-cell

The unique map from the initial topological space to a point is an attachment
of one zero-cell.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat

namespace Hatcher.VanKampen

universe u

private instance diskBoundaryZeroIsEmpty :
    IsEmpty (((TopCat.diskBoundary.{u} 0 : TopCat.{u}) : Type u)) where
  false x := by
    have hx : ‖(x.down.1 : EuclideanSpace ℝ (Fin 0))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp x.down.2
    have hz : (x.down.1 : EuclideanSpace ℝ (Fin 0)) = 0 :=
      Subsingleton.elim _ _
    simp [hz] at hx

private def pointAttachingMap :
    ∀ _ : PUnit.{u + 1},
      (((TopCat.diskBoundary.{u} 0 : TopCat.{u}) : Type u)) → PEmpty.{u + 1} :=
  fun _ x ↦ (diskBoundaryZeroIsEmpty.false x).elim

private theorem continuous_pointAttachingMap (j : PUnit.{u + 1}) :
    Continuous (pointAttachingMap.{u} j) := by
  fun_prop

private noncomputable instance pointIndexedAttachmentUnique :
    Unique (IndexedConeAttachment pointAttachingMap.{u}) where
  default := IndexedConeAttachment.apex pointAttachingMap PUnit.unit
  uniq q := by
    refine Quotient.inductionOn q ?_
    intro z
    rcases z with x | ⟨j, y⟩
    · exact isEmptyElim x
    · rcases y with a | ⟨s, t⟩
      · obtain rfl : j = PUnit.unit := Subsingleton.elim _ _
        obtain rfl : a = () := Subsingleton.elim _ _
        rfl
      · exact (diskBoundaryZeroIsEmpty.false s).elim

private noncomputable def indexedPointAttachment :
    AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} 0)
      (IndexedConeAttachment.baseHom pointAttachingMap.{u}) :=
  IndexedConeAttachment.attachCells_basicCell 0 pointAttachingMap
    continuous_pointAttachingMap

private noncomputable def indexedPointArrowIso :
    Arrow.mk (IndexedConeAttachment.baseHom pointAttachingMap.{u}) ≅
      Arrow.mk (initial.to (TopCat.of PUnit.{u + 1})) :=
  Arrow.isoMk TopCat.initialIsoPEmpty.symm
    (TopCat.isoOfHomeo (Homeomorph.homeomorphOfUnique
      (IndexedConeAttachment pointAttachingMap.{u}) PUnit.{u + 1})) (by
      ext x
      change PEmpty at x
      exact x.elim)

/-- The unique map from the initial topological space to a point is the
attachment of one standard zero-cell. -/
noncomputable def pointAttachCells :
    AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} 0)
      (initial.to (TopCat.of PUnit.{u + 1})) :=
  indexedPointAttachment.ofArrowIso indexedPointArrowIso

end Hatcher.VanKampen
