import Hatcher.VanKampen.PresentationRelatorAttachment
import Mathlib.GroupTheory.PresentedGroup

/-!
# Fundamental group of a presentation complex

This file computes the fundamental group of the presentation complex by
transporting the two-cell attachment quotient across the free-group
equivalence for a wedge of circles.
-/

noncomputable section

namespace Hatcher

universe u

/-- Transporting the normal closure of the relator attaching loops through
the wedge-of-circles equivalence gives the prescribed relator subgroup. -/
theorem presentationRelatorAttachingNormalSubgroup_map
    {S : Type u} (rels : Set (FreeGroup S)) :
    (VanKampen.twoCellAttachingNormalSubgroup
      (presentationRelatorAttachCells rels)
      (PointedWedge.basepoint (fun _ : S => (1 : _root_.Circle)))
      (presentationRelatorBasepointPath rels)).map
        fundamentalGroupEquivWedgeCircles.toMonoidHom =
      Subgroup.normalClosure rels := by
  rw [VanKampen.twoCellAttachingNormalSubgroup,
    Subgroup.map_normalClosure _ _
      fundamentalGroupEquivWedgeCircles.surjective]
  congr 1
  ext r
  constructor
  · rintro ⟨g, ⟨i, rfl⟩, h⟩
    change fundamentalGroupEquivWedgeCircles
      (VanKampen.twoCellAttachingLoop
        (presentationRelatorAttachCells rels)
        (PointedWedge.basepoint (fun _ : S => (1 : _root_.Circle)))
        (presentationRelatorBasepointPath rels) i) = r at h
    rw [presentationRelator_twoCellAttachingLoop] at h
    rw [← h]
    exact i.property
  · intro hr
    refine ⟨VanKampen.twoCellAttachingLoop
      (presentationRelatorAttachCells rels)
      (PointedWedge.basepoint (fun _ : S => (1 : _root_.Circle)))
      (presentationRelatorBasepointPath rels) ⟨r, hr⟩, ?_, ?_⟩
    · exact ⟨⟨r, hr⟩, rfl⟩
    · exact presentationRelator_twoCellAttachingLoop rels ⟨r, hr⟩

/-- The presentation complex associated to an arbitrary set of relators has
the presented fundamental group. This includes empty and infinite
presentations. -/
noncomputable def presentationComplexFundamentalGroupEquiv
    {S : Type u} (rels : Set (FreeGroup S)) :
    PresentedGroup rels ≃*
      FundamentalGroup (presentationComplex rels)
        (presentationComplexBasepoint rels) := by
  letI := VanKampen.twoCellAttachingNormalSubgroup_normal
    (presentationRelatorAttachCells rels)
    (PointedWedge.basepoint (fun _ : S => (1 : _root_.Circle)))
    (presentationRelatorBasepointPath rels)
  exact
    (QuotientGroup.congr
      (VanKampen.twoCellAttachingNormalSubgroup
        (presentationRelatorAttachCells rels)
        (PointedWedge.basepoint (fun _ : S => (1 : _root_.Circle)))
        (presentationRelatorBasepointPath rels))
      (Subgroup.normalClosure rels)
      fundamentalGroupEquivWedgeCircles
      (presentationRelatorAttachingNormalSubgroup_map rels)).symm.trans
        (fundamentalGroup_quotient_of_attachTwoCells
          (presentationRelatorAttachCells rels)
          (PointedWedge.basepoint (fun _ : S => (1 : _root_.Circle)))
          (presentationRelatorBasepointPath rels))

end Hatcher
