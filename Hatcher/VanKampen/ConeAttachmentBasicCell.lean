import Hatcher.VanKampen.ConeAttachmentDisk
import Hatcher.VanKampen.ConeAttachmentPushout
import Mathlib.Topology.CWComplex.Abstract.Basic

/-!
# A cone attachment as a basic CW-cell attachment

This module transports the retained-cone cell in a single cone attachment
to Mathlib's standard disk-boundary inclusion.
-/

noncomputable section

open CategoryTheory
open scoped TopCat

namespace Hatcher.VanKampen.ConeAttachment

universe u

/-- The retained boundary inclusion of the explicit cone is isomorphic to
Mathlib's standard `n`-disk boundary inclusion. -/
def coneBoundaryIsoBasicCell (n : ℕ) :
    Arrow.mk
        (coneBoundaryHom
          ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u)) ≅
      Arrow.mk (TopCat.RelativeCWComplex.basicCell.{u} n ()) :=
  Arrow.isoMk (Iso.refl _)
    (TopCat.isoOfHomeo (diskHomeomorph n)) (by
      ext x
      exact diskHomeomorph_base_eq_diskBoundaryInclusion n x)

/-- A cone attached along the boundary of the standard `n`-disk is obtained
by attaching one cell of Mathlib's standard `n`-cell type. -/
def attachCells_basicCell (n : ℕ) {X : Type u} [TopologicalSpace X]
    (f : ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u) → X)
    (hf : Continuous f) :
    HomotopicalAlgebra.AttachCells
      (TopCat.RelativeCWComplex.basicCell.{u} n) (baseHom f) :=
  (attachCells_coneAttachment f hf).reindexCellTypes
    (TopCat.RelativeCWComplex.basicCell.{u} n) id
    (fun _ ↦ coneBoundaryIsoBasicCell n)

end Hatcher.VanKampen.ConeAttachment
