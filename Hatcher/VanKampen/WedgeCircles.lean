import Hatcher.Circle.FundamentalGroup
import Hatcher.Circle.WellPointed
import Hatcher.VanKampen.WedgeFundamentalGroup

noncomputable section

open CategoryTheory FundamentalGroupoid
open scoped ContinuousMap

namespace Hatcher

universe u

/-- The fundamental group of a wedge of circles is the free group on the
indexing type. -/
def fundamentalGroupEquivWedgeCircles {ι : Type u} :
    FundamentalGroup
        (PointedWedge (fun _ : ι => _root_.Circle) (fun _ => (1 : _root_.Circle)))
        (PointedWedge.basepoint (fun _ : ι => (1 : _root_.Circle))) ≃*
      FreeGroup ι :=
  (fundamentalGroupEquivPointedWedge
      (fun _ : ι => (1 : _root_.Circle))
      (fun _ => Circle.wellPointedAt_one)).symm |>.trans
    (coprodIEquiv fun _ =>
      Circle.fundamentalGroupEquivInt.trans
        FreeGroup.mulEquivIntOfUnique.symm) |>.trans
    freeGroupEquivCoprodI.symm

/-- The `i`th standard circle loop of winding number `n` maps to the `n`th
power of the `i`th free generator. -/
@[simp]
theorem fundamentalGroupEquivWedgeCircles_inclusion_loopOfInt
    {ι : Type u} (i : ι) (n : ℤ) :
    fundamentalGroupEquivWedgeCircles
        (FundamentalGroup.mapOfEq
          (⟨PointedWedge.inclusion
              (fun _ : ι => (1 : _root_.Circle)) i,
            PointedWedge.continuous_inclusion
              (fun _ : ι => (1 : _root_.Circle)) i⟩ :
            C(_root_.Circle,
              PointedWedge (fun _ : ι => _root_.Circle)
                (fun _ => (1 : _root_.Circle))))
          (PointedWedge.inclusion_basepoint
            (fun _ : ι => (1 : _root_.Circle)) i)
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (Circle.loopOfInt n)))) =
      FreeGroup.of i ^ n := by
  let x₀ : ι → _root_.Circle := fun _ => 1
  let hwell : ∀ j, WellPointedAt (x₀ j) := fun _ =>
    Circle.wellPointedAt_one
  let g : FundamentalGroup _root_.Circle 1 :=
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Circle.loopOfInt n))
  have hinv :
      (fundamentalGroupEquivPointedWedge x₀ hwell).symm
          (FundamentalGroup.mapOfEq
            (⟨PointedWedge.inclusion x₀ i,
              PointedWedge.continuous_inclusion x₀ i⟩ :
              C(_root_.Circle,
                PointedWedge (fun _ : ι => _root_.Circle) x₀))
            (PointedWedge.inclusion_basepoint x₀ i) g) =
        (Monoid.CoprodI.of
          (M := fun _ : ι => FundamentalGroup _root_.Circle 1)
          (i := i)) g := by
    rw [← fundamentalGroupEquivPointedWedge_of x₀ hwell]
    exact MulEquiv.symm_apply_apply _ _
  change freeGroupEquivCoprodI.symm
      ((coprodIEquiv fun _ =>
          Circle.fundamentalGroupEquivInt.trans
            FreeGroup.mulEquivIntOfUnique.symm)
        ((fundamentalGroupEquivPointedWedge x₀ hwell).symm
          (FundamentalGroup.mapOfEq
            (⟨PointedWedge.inclusion x₀ i,
              PointedWedge.continuous_inclusion x₀ i⟩ :
              C(_root_.Circle,
                PointedWedge (fun _ : ι => _root_.Circle) x₀))
            (PointedWedge.inclusion_basepoint x₀ i) g))) =
      FreeGroup.of i ^ n
  rw [hinv]
  simp [coprodIEquiv,
    FreeGroup.mulEquivIntOfUnique,
    freeGroupEquivCoprodI_symm_apply,
    Circle.fundamentalGroupEquivInt_apply,
    Circle.windingNumberFun_loopOfInt, g]
  change (FreeGroup.lift fun _ : Unit => FreeGroup.of i)
      (FreeGroup.of () ^ n) = FreeGroup.of i ^ n
  rw [map_zpow, FreeGroup.lift_apply_of]

end Hatcher
