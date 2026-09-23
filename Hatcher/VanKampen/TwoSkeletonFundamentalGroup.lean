import Hatcher.Appendix.CompactSubspaceFiniteSubcomplex
import Hatcher.VanKampen.FiniteSkeletonFundamentalGroup

/-!
# The fundamental group of a classical CW complex and its two-skeleton

This file completes Hatcher's compactness argument: every loop and every path
homotopy in a CW complex has image in one finite skeleton, where the comparison
with the two-skeleton is already an equivalence.
-/

noncomputable section

open Set unitInterval

namespace Hatcher

universe u

open Topology

private def twoSkeletonInclusion
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] :
    C(CWComplex.skeleton C (2 : ℕ∞), C) where
  toFun x := ⟨x.1, (CWComplex.skeleton C (2 : ℕ∞)).subset_complex x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private def skeletonInclusionToComplex
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] (m : ℕ) :
    C(CWComplex.skeleton C (m : ℕ∞), C) where
  toFun x := ⟨x.1, (CWComplex.skeleton C (m : ℕ∞)).subset_complex x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private def twoSkeletonToSkeleton
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C]
    (m : ℕ) (hm : 2 ≤ m) :
    C(CWComplex.skeleton C (2 : ℕ∞),
      CWComplex.skeleton C (m : ℕ∞)) where
  toFun x := ⟨x.1, CWComplex.skeleton_mono
    (C := C) (Nat.cast_le.mpr hm) x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private theorem twoSkeletonMap_surjective
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [PathConnectedSpace C]
    (x₀ : CWComplex.skeleton C (2 : ℕ∞)) :
    Function.Surjective (FundamentalGroup.map (twoSkeletonInclusion C) x₀) := by
  intro g
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
      let pX : I → X := fun t ↦ (p t : X)
      have hpX : Continuous pX := continuous_subtype_val.comp p.continuous
      have hpC : Set.range pX ⊆ C := by
        rintro _ ⟨t, rfl⟩
        exact (p t).2
      obtain ⟨n, hn⟩ := Hatcher.compact_subset_skeleton
        (isCompact_range hpX) hpC
      let m := max n 2
      have hm : 2 ≤ m := Nat.le_max_right _ _
      have hn_m : n ≤ m := Nat.le_max_left _ _
      have hxM : x₀.1 ∈ CWComplex.skeleton C (m : ℕ∞) :=
        CWComplex.skeleton_mono (C := C) (Nat.cast_le.mpr hm) x₀.2
      let xm : CWComplex.skeleton C (m : ℕ∞) :=
        ⟨x₀.1, hxM⟩
      let pm : Path xm xm :=
        { toFun := fun t ↦ ⟨pX t, CWComplex.skeleton_mono
              (C := C) (Nat.cast_le.mpr hn_m) (hn ⟨t, rfl⟩)⟩
          continuous_toFun := hpX.subtype_mk _
          source' := by
            apply Subtype.ext
            exact congrArg (fun z : C ↦ (z : X)) p.source
          target' := by
            apply Subtype.ext
            exact congrArg (fun z : C ↦ (z : X)) p.target }
      let e := ClassicalCW.fundamentalGroupEquiv_twoSkeleton_skeleton C m hm x₀
      obtain ⟨w, hw⟩ := e.surjective
        (FundamentalGroup.fromPath (.mk pm))
      refine ⟨w, ?_⟩
      have hw' : FundamentalGroup.map
          ({ toFun := fun x ↦ ⟨x.1, CWComplex.skeleton_mono
                (C := C) (Nat.cast_le.mpr hm) x.2⟩,
             continuous_toFun := continuous_subtype_val.subtype_mk _ } :
            C(CWComplex.skeleton C (2 : ℕ∞),
              CWComplex.skeleton C (m : ℕ∞)))
          x₀ w = FundamentalGroup.fromPath (.mk pm) := by
        rw [ClassicalCW.fundamentalGroupEquiv_twoSkeleton_skeleton_apply] at hw
        exact hw
      change FundamentalGroup.map (twoSkeletonInclusion C) x₀ w =
        FundamentalGroup.fromPath (.mk p)
      calc
        _ = FundamentalGroup.map (skeletonInclusionToComplex C m) xm
              (FundamentalGroup.map
                ({ toFun := fun x ↦ ⟨x.1, CWComplex.skeleton_mono
                      (C := C) (Nat.cast_le.mpr hm) x.2⟩,
                   continuous_toFun := continuous_subtype_val.subtype_mk _ } :
                  C(CWComplex.skeleton C (2 : ℕ∞),
                    CWComplex.skeleton C (m : ℕ∞)))
                x₀ w) := by
            induction w using Path.Homotopic.Quotient.ind with
            | mk q => rfl
        _ = FundamentalGroup.map (skeletonInclusionToComplex C m) xm
              (FundamentalGroup.fromPath (.mk pm)) := congrArg _ hw'
        _ = FundamentalGroup.fromPath (.mk p) := rfl

private theorem twoSkeletonMap_injective
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [PathConnectedSpace C]
    (x₀ : CWComplex.skeleton C (2 : ℕ∞)) :
    Function.Injective (FundamentalGroup.map (twoSkeletonInclusion C) x₀) := by
  intro g h hgh
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction h using Path.Homotopic.Quotient.ind with
    | mk q =>
      rw [FundamentalGroup.map_apply, FundamentalGroup.map_apply,
        ← Path.Homotopic.Quotient.mk_map,
        ← Path.Homotopic.Quotient.mk_map] at hgh
      have hpq : Path.Homotopic
          (p.map (twoSkeletonInclusion C).continuous)
          (q.map (twoSkeletonInclusion C).continuous) :=
        Path.Homotopic.Quotient.exact hgh
      obtain ⟨F⟩ := hpq
      let FX : I × I → X := fun z ↦ (F z : C).1
      have hFX : Continuous FX :=
        continuous_subtype_val.comp F.continuous_toFun
      have hFC : Set.range FX ⊆ C := by
        rintro _ ⟨z, rfl⟩
        exact (F z).2
      obtain ⟨n, hn⟩ := Hatcher.compact_subset_skeleton
        (isCompact_range hFX) hFC
      let m := max n 2
      have hm : 2 ≤ m := Nat.le_max_right _ _
      have hn_m : n ≤ m := Nat.le_max_left _ _
      have hrange : Set.range FX ⊆ CWComplex.skeleton C (m : ℕ∞) :=
        hn.trans (CWComplex.skeleton_mono (Nat.cast_le.mpr hn_m))
      let Fm : Path.Homotopy
          (p.map (twoSkeletonToSkeleton C m hm).continuous)
          (q.map (twoSkeletonToSkeleton C m hm).continuous) :=
        { toFun := fun z ↦ ⟨FX z, hrange ⟨z, rfl⟩⟩
          continuous_toFun := hFX.subtype_mk _
          map_zero_left := by
            intro t
            ext
            change FX (0, t) = (p t : X)
            exact congrArg (fun z : C ↦ (z : X)) (F.map_zero_left t)
          map_one_left := by
            intro t
            ext
            change FX (1, t) = (q t : X)
            exact congrArg (fun z : C ↦ (z : X)) (F.map_one_left t)
          prop' := by
            intro t s hs
            ext
            change FX (t, s) = (p s : X)
            exact congrArg (fun z : C ↦ (z : X)) (F.prop t s hs) }
      have hfinite :
          FundamentalGroup.map (twoSkeletonToSkeleton C m hm) x₀
              (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
            FundamentalGroup.map (twoSkeletonToSkeleton C m hm) x₀
              (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) := by
        rw [FundamentalGroup.map_apply, FundamentalGroup.map_apply,
          ← Path.Homotopic.Quotient.mk_map,
          ← Path.Homotopic.Quotient.mk_map]
        exact Quotient.sound ⟨Fm⟩
      apply (ClassicalCW.fundamentalGroupEquiv_twoSkeleton_skeleton C m hm x₀).injective
      rw [ClassicalCW.fundamentalGroupEquiv_twoSkeleton_skeleton_apply,
        ClassicalCW.fundamentalGroupEquiv_twoSkeleton_skeleton_apply]
      exact hfinite

/-- **Hatcher, Proposition 1.26(c).** Inclusion of the two-skeleton of a
path-connected classical CW complex induces an equivalence on fundamental
groups. -/
noncomputable def fundamentalGroupEquiv_twoSkeleton
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [PathConnectedSpace C]
    (x₀ : CWComplex.skeleton C (2 : ℕ∞)) :
    FundamentalGroup (CWComplex.skeleton C (2 : ℕ∞)) x₀ ≃*
      FundamentalGroup C
        ⟨x₀.1, (CWComplex.skeleton C (2 : ℕ∞)).subset_complex x₀.2⟩ :=
  MulEquiv.ofBijective (FundamentalGroup.map (twoSkeletonInclusion C) x₀)
    ⟨twoSkeletonMap_injective C x₀, twoSkeletonMap_surjective C x₀⟩

/-- The two-skeleton equivalence is the map induced by the subtype
inclusion into the ambient CW complex. -/
@[simp]
theorem fundamentalGroupEquiv_twoSkeleton_apply
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [PathConnectedSpace C]
    (x₀ : CWComplex.skeleton C (2 : ℕ∞))
    (g : FundamentalGroup (CWComplex.skeleton C (2 : ℕ∞)) x₀) :
    fundamentalGroupEquiv_twoSkeleton C x₀ g =
      FundamentalGroup.map
        ({ toFun := fun x =>
            ⟨x.1, (CWComplex.skeleton C (2 : ℕ∞)).subset_complex x.2⟩
           continuous_toFun := continuous_subtype_val.subtype_mk _ } :
          C(CWComplex.skeleton C (2 : ℕ∞), C))
        x₀ g := rfl

end Hatcher
