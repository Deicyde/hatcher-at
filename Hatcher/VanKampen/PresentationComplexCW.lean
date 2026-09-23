import Hatcher.VanKampen.PointCellAttachment
import Hatcher.VanKampen.WedgeCirclesCellAttachment
import Hatcher.VanKampen.PresentationRelatorAttachment
import Hatcher.VanKampen.CellAttachmentEmpty
import Hatcher.VanKampen.EventuallyConstantCellSequence

/-!
# The presentation complex as an abstract CW complex

This module assembles the point, wedge-of-circles, and relator attachments into
an eventually constant cell sequence. The empty tail records that the resulting
presentation complex has no cells above dimension two.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat

namespace Hatcher

universe u

private def presentationComplexStage {S : Type u}
    (rels : Set (FreeGroup S)) : ℕ → TopCat.{u}
  | 0 => ⊥_ TopCat.{u}
  | 1 => TopCat.of PUnit.{u + 1}
  | 2 => TopCat.of
      (PointedWedge (fun _ : S => _root_.Circle)
        (fun _ => (1 : _root_.Circle)))
  | _ + 3 => TopCat.of (presentationComplex rels)

private def presentationComplexStep {S : Type u}
    (rels : Set (FreeGroup S)) :
    ∀ n, presentationComplexStage rels n ⟶
      presentationComplexStage rels (n + 1)
  | 0 => initial.to _
  | 1 => wedgeCirclesBaseHom (ι := S)
  | 2 => presentationComplexBaseHom rels
  | _ + 3 => CategoryStruct.id _

private noncomputable def presentationComplexCells {S : Type u}
    (rels : Set (FreeGroup S)) :
    ∀ n, AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n)
      (presentationComplexStep rels n)
  | 0 => VanKampen.pointAttachCells
  | 1 => wedgeCirclesAttachCells
  | 2 => presentationRelatorAttachCells rels
  | n + 3 => VanKampen.CellAttachment.attachCellsId (n + 3) _

private theorem presentationComplexSequence_eventuallyConstant {S : Type u}
    (rels : Set (FreeGroup S)) :
    (Functor.ofSequence
      (presentationComplexStep rels)).IsEventuallyConstantFrom 3 := by
  apply VanKampen.CellAttachment.ofSequence_isEventuallyConstantFrom
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 3 k]
  change IsIso (CategoryStruct.id _)
  infer_instance

private theorem presentationComplexCells_empty_above_two {S : Type u}
    (rels : Set (FreeGroup S)) :
    ∀ n, 3 ≤ n → IsEmpty (presentationComplexCells rels n).ι := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 3 k]
  change IsEmpty PEmpty
  infer_instance

/-- The presentation complex carries the abstract CW structure obtained from
one zero-cell, one one-cell per generator, and one two-cell per relator. -/
noncomputable def presentationComplexCWComplex {S : Type u}
    (rels : Set (FreeGroup S)) :
    TopCat.CWComplex (TopCat.of (presentationComplex rels)) :=
  VanKampen.CellAttachment.cwComplexOfEventuallyConstantSequence
    (presentationComplexStage rels) (presentationComplexStep rels)
    initialIsInitial 3 (presentationComplexSequence_eventuallyConstant rels)
    (presentationComplexCells rels)

/-- Every cell in the presentation complex has dimension at most two. -/
theorem presentationComplexCWComplex_cells_dim_le_two {S : Type u}
    (rels : Set (FreeGroup S))
    (γ : RelativeCellComplex.Cells (presentationComplexCWComplex rels)) :
    γ.j ≤ 2 := by
  have hγ : γ.j < 3 :=
    VanKampen.CellAttachment.cwComplexOfEventuallyConstantSequence_cell_dim_lt
      (presentationComplexStage rels) (presentationComplexStep rels)
      initialIsInitial 3 (presentationComplexSequence_eventuallyConstant rels)
      (presentationComplexCells rels)
      (presentationComplexCells_empty_above_two rels) γ
  omega

end Hatcher
