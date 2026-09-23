import Hatcher.VanKampen.CellAttachmentHigher
import Hatcher.VanKampen.TwoSkeletonPathConnected

/-!
# Fundamental groups of finite classical skeleta

This file iterates the higher-cell attachment equivalence from the
two-skeleton to any finite skeleton of dimension at least two.
-/

noncomputable section

open Set

namespace Hatcher.ClassicalCW

universe u

open Topology

private theorem pathConnectedSpace_skeleton_of_two_le
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [PathConnectedSpace C]
    (m : ℕ) (hm : 2 ≤ m) :
    PathConnectedSpace (CWComplex.skeleton C (m : ℕ∞)) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hbase : m = 1
      · subst m
        exact pathConnectedSpace_twoSkeleton C
      · have hm' : 2 ≤ m := by omega
        letI : PathConnectedSpace (CWComplex.skeleton C (m : ℕ∞)) := ih hm'
        exact Hatcher.pathConnectedSpace_of_attachCells_of_two_lt
          (skeletonInclusion_attachCells C m) (by omega)

private def directInclusion
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C]
    (m : ℕ) (hm : 2 ≤ m) :
    C(CWComplex.skeleton C (2 : ℕ∞),
      CWComplex.skeleton C (m : ℕ∞)) where
  toFun x := ⟨x.1, CWComplex.skeleton_mono
    (C := C) (Nat.cast_le.mpr hm) x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private theorem directMap_bijective
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [PathConnectedSpace C]
    (m : ℕ) (hm : 2 ≤ m)
    (x₀ : CWComplex.skeleton C (2 : ℕ∞)) :
    Function.Bijective (FundamentalGroup.map (directInclusion C m hm) x₀) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hbase : m = 1
      · subst m
        have heq : FundamentalGroup.map (directInclusion C 2 hm) x₀ =
            MonoidHom.id _ := by
          ext g
          induction g using Path.Homotopic.Quotient.ind with
          | mk p => rfl
        rw [heq]
        exact Function.bijective_id
      · have hm' : 2 ≤ m := by omega
        letI : PathConnectedSpace (CWComplex.skeleton C (m : ℕ∞)) :=
          pathConnectedSpace_skeleton_of_two_le C m hm'
        let xm : CWComplex.skeleton C (m : ℕ∞) :=
          ⟨x₀.1, CWComplex.skeleton_mono
            (C := C) (Nat.cast_le.mpr hm') x₀.2⟩
        have hstep : Function.Bijective
            (FundamentalGroup.map (skeletonInclusion C m).hom xm) := by
          let e := Hatcher.fundamentalGroupEquiv_of_attachCells_of_two_lt
            (skeletonInclusion_attachCells C m) (by omega) xm
          have heq : FundamentalGroup.map (skeletonInclusion C m).hom xm = e := by
            ext g
            exact (Hatcher.fundamentalGroupEquiv_of_attachCells_of_two_lt_apply
              (skeletonInclusion_attachCells C m) (by omega) xm g).symm
          rw [heq]
          exact e.bijective
        have hcomp := hstep.comp (ih hm')
        have heq :
            (FundamentalGroup.map (directInclusion C (m + 1) hm) x₀ :
              FundamentalGroup (CWComplex.skeleton C (2 : ℕ∞)) x₀ →
                FundamentalGroup (CWComplex.skeleton C ((m + 1 : ℕ) : ℕ∞))
                  ⟨x₀.1, CWComplex.skeleton_mono
                    (C := C) (Nat.cast_le.mpr hm) x₀.2⟩) =
              (FundamentalGroup.map (skeletonInclusion C m).hom xm) ∘
                (FundamentalGroup.map (directInclusion C m hm') x₀) := by
          funext g
          induction g using Path.Homotopic.Quotient.ind with
          | mk p => rfl
        rw [heq]
        exact hcomp

/-- Every finite skeleton above dimension two has the same fundamental group
as the two-skeleton. -/
noncomputable def fundamentalGroupEquiv_twoSkeleton_skeleton
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [PathConnectedSpace C]
    (m : ℕ) (hm : 2 ≤ m)
    (x₀ : CWComplex.skeleton C (2 : ℕ∞)) :
    FundamentalGroup (CWComplex.skeleton C (2 : ℕ∞)) x₀ ≃*
      FundamentalGroup (CWComplex.skeleton C (m : ℕ∞))
        ⟨x₀.1, CWComplex.skeleton_mono
          (C := C) (Nat.cast_le.mpr hm) x₀.2⟩ :=
  MulEquiv.ofBijective (FundamentalGroup.map (directInclusion C m hm) x₀)
    (directMap_bijective C m hm x₀)

/-- The finite-skeleton equivalence is the map induced by the direct subtype
inclusion from the two-skeleton. -/
@[simp]
theorem fundamentalGroupEquiv_twoSkeleton_skeleton_apply
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [PathConnectedSpace C]
    (m : ℕ) (hm : 2 ≤ m)
    (x₀ : CWComplex.skeleton C (2 : ℕ∞))
    (g : FundamentalGroup (CWComplex.skeleton C (2 : ℕ∞)) x₀) :
    fundamentalGroupEquiv_twoSkeleton_skeleton C m hm x₀ g =
      FundamentalGroup.map
        ({ toFun := fun x => ⟨x.1, CWComplex.skeleton_mono
              (C := C) (Nat.cast_le.mpr hm) x.2⟩,
           continuous_toFun := continuous_subtype_val.subtype_mk _ } :
          C(CWComplex.skeleton C (2 : ℕ∞),
            CWComplex.skeleton C (m : ℕ∞)))
        x₀ g := rfl

end Hatcher.ClassicalCW
