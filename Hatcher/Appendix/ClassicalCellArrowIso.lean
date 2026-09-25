import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.CWComplex.Abstract.Basic
import Mathlib.Topology.Category.TopCat.ULift

noncomputable section

open CategoryTheory Metric Set

namespace Hatcher.ClassicalCW

universe u

private abbrev SupSpace (n : ℕ) := Fin n → ℝ
private abbrev L2Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

private noncomputable def supToL2 (n : ℕ) : SupSpace n ≃L[ℝ] L2Space n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm

private theorem exists_ambientHomeomorph (n : ℕ) :
    ∃ e : SupSpace n ≃ₜ L2Space n,
      e '' closedBall 0 1 = closedBall 0 1 ∧
      e '' sphere 0 1 = sphere 0 1 := by
  let L : SupSpace n ≃L[ℝ] L2Space n := supToL2 n
  let Lh : SupSpace n ≃ₜ L2Space n := L.toHomeomorph
  let s : Set (L2Space n) := Lh '' ball (0 : SupSpace n) 1
  have hsconv : Convex ℝ s := by
    change Convex ℝ (L '' ball (0 : SupSpace n) 1)
    exact (convex_ball (0 : SupSpace n) 1).linear_image L.toLinearEquiv.toLinearMap
  have hsopen : IsOpen s := Lh.isOpenMap _ Metric.isOpen_ball
  have hsne : (interior s).Nonempty := by
    rw [hsopen.interior_eq]
    exact ⟨Lh 0, ⟨0, by simp, rfl⟩⟩
  have hsb : Bornology.IsBounded s := by
    change Bornology.IsBounded (L '' ball (0 : SupSpace n) 1)
    exact Metric.isBounded_ball.image L.toContinuousLinearMap
  obtain ⟨h, _hi, hc, hf⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hsconv hsne hsb
  refine ⟨Lh.trans h, ?_, ?_⟩
  · have hLs : Lh '' closedBall (0 : SupSpace n) 1 = closure s := by
      rw [← closure_ball (0 : SupSpace n) one_ne_zero, Lh.image_closure]
    calc
      (Lh.trans h) '' closedBall (0 : SupSpace n) 1 =
          (fun x ↦ h (Lh x)) '' closedBall 0 1 := by
            apply congrArg (fun g : SupSpace n → L2Space n ↦
              g '' closedBall (0 : SupSpace n) 1)
            funext x
            exact Homeomorph.trans_apply Lh h x
      _ = h '' (Lh '' closedBall 0 1) := (image_image h Lh _).symm
      _ = closedBall 0 1 := by rw [hLs, hc]
  · have hLs : Lh '' sphere (0 : SupSpace n) 1 = frontier s := by
      rw [← frontier_ball (0 : SupSpace n) one_ne_zero, Lh.image_frontier]
    calc
      (Lh.trans h) '' sphere (0 : SupSpace n) 1 =
          (fun x ↦ h (Lh x)) '' sphere 0 1 := by
            apply congrArg (fun g : SupSpace n → L2Space n ↦
              g '' sphere (0 : SupSpace n) 1)
            funext x
            exact Homeomorph.trans_apply Lh h x
      _ = h '' (Lh '' sphere 0 1) := (image_image h Lh _).symm
      _ = sphere 0 1 := by rw [hLs, hf]

private noncomputable def ambientHomeomorph (n : ℕ) : SupSpace n ≃ₜ L2Space n :=
  (exists_ambientHomeomorph n).choose

private theorem ambientHomeomorph_image_closedBall (n : ℕ) :
    ambientHomeomorph n '' closedBall (0 : SupSpace n) 1 =
      closedBall (0 : L2Space n) 1 :=
  (exists_ambientHomeomorph n).choose_spec.1

private theorem ambientHomeomorph_image_sphere (n : ℕ) :
    ambientHomeomorph n '' sphere (0 : SupSpace n) 1 =
      sphere (0 : L2Space n) 1 :=
  (exists_ambientHomeomorph n).choose_spec.2

private noncomputable def diskHomeomorph (n : ℕ) :
    closedBall (0 : SupSpace n) 1 ≃ₜ closedBall (0 : L2Space n) 1 :=
  (ambientHomeomorph n).sets
    ((ambientHomeomorph n).toEquiv.eq_preimage_iff_image_eq _ _ |>.2
      (ambientHomeomorph_image_closedBall n))

private noncomputable def diskBoundaryHomeomorph (n : ℕ) :
    sphere (0 : SupSpace n) 1 ≃ₜ sphere (0 : L2Space n) 1 :=
  (ambientHomeomorph n).sets
    ((ambientHomeomorph n).toEquiv.eq_preimage_iff_image_eq _ _ |>.2
      (ambientHomeomorph_image_sphere n))

private def liftHomeomorph {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) : ULift.{u} A ≃ₜ ULift.{u} B :=
  Homeomorph.ulift.trans (e.trans Homeomorph.ulift.symm)

/-- The universe-lifted sup-norm disk used by classical characteristic maps. -/
noncomputable def classicalDisk (n : ℕ) : TopCat.{u} :=
  TopCat.uliftFunctor.{u}.obj
    (TopCat.of (closedBall (0 : SupSpace n) 1))

/-- The universe-lifted sup-norm boundary used by classical characteristic maps. -/
noncomputable def classicalDiskBoundary (n : ℕ) : TopCat.{u} :=
  TopCat.uliftFunctor.{u}.obj
    (TopCat.of (sphere (0 : SupSpace n) 1))

private def supDiskBoundaryInclusion (n : ℕ) :
    C(sphere (0 : SupSpace n) 1, closedBall (0 : SupSpace n) 1) where
  toFun x := ⟨x, sphere_subset_closedBall x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Inclusion of the classical sup-norm disk boundary into its disk. -/
def classicalDiskBoundaryInclusion (n : ℕ) :
    classicalDiskBoundary.{u} n ⟶ classicalDisk.{u} n :=
  TopCat.uliftFunctor.{u}.map (TopCat.ofHom (supDiskBoundaryInclusion n))

private noncomputable def classicalDiskIsoStandardDisk (n : ℕ) :
    classicalDisk.{u} n ≅ TopCat.disk.{u} n :=
  TopCat.isoOfHomeo (liftHomeomorph (diskHomeomorph n))

private noncomputable def classicalDiskBoundaryIsoStandardDisk (n : ℕ) :
    classicalDiskBoundary.{u} n ≅ TopCat.diskBoundary.{u} n :=
  TopCat.isoOfHomeo (liftHomeomorph (diskBoundaryHomeomorph n))

/-- The sup-norm classical cell arrow is isomorphic to Mathlib's standard L2
cell arrow. -/
noncomputable def classicalCellArrowIso (n : ℕ) :
    Arrow.mk (classicalDiskBoundaryInclusion.{u} n) ≅
      Arrow.mk (TopCat.RelativeCWComplex.basicCell.{u} n ()) :=
  Arrow.isoMk (classicalDiskBoundaryIsoStandardDisk n)
    (classicalDiskIsoStandardDisk n) (by
      ext x
      rfl)

end Hatcher.ClassicalCW
