/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.Reduced
import Hatcher.Sphere.ZeroSphere
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Reduced homology of the zero-sphere

This file computes reduced homology of `S⁰` without cancelling biproduct
summands. It identifies ordinary zeroth homology with `R ⊞ R`, identifies
its augmentation with the codiagonal, and identifies reduced zeroth homology
with the antidiagonal kernel.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits
open scoped Simplicial

namespace Hatcher.Sphere

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

local instance : HasFiniteCoproducts C :=
  hasFiniteCoproducts_of_hasCoproducts C

local instance : HasBinaryBiproducts C :=
  HasBinaryBiproducts.of_hasBinaryCoproducts

/-- The coproduct indexed by the lifted two-point type is a binary biproduct. -/
noncomputable def twoPointCoproductIso (R : C) :
    (∐ (fun _ : ULift.{w} Bool ↦ R)) ≅ (R ⊞ R) where
  hom := Sigma.desc fun b ↦
    match b.down with
    | false => biprod.inl
    | true => biprod.inr
  inv := biprod.desc
    (Sigma.ι (fun _ : ULift.{w} Bool ↦ R) (ULift.up false))
    (Sigma.ι (fun _ : ULift.{w} Bool ↦ R) (ULift.up true))
  hom_inv_id := by
    apply Sigma.hom_ext
    rintro ⟨b⟩
    cases b <;> simp
  inv_hom_id := by
    apply biprod.hom_ext' <;> simp

@[reassoc (attr := simp)]
lemma twoPointCoproductIso_hom_codiagonal (R : C) :
    (twoPointCoproductIso R).hom ≫ biprod.desc (𝟙 R) (𝟙 R) =
      Sigma.desc (fun _ : ULift.{w} Bool ↦ 𝟙 R) := by
  apply Sigma.hom_ext
  rintro ⟨b⟩
  cases b <;> simp [twoPointCoproductIso]

private lemma reindex_twoPointCoproductIso_hom_codiagonal
    {J : Type w} (e : J ≃ ULift.{w} Bool) (R : C) :
    (Sigma.reindex e (fun _ : ULift.{w} Bool ↦ R)).hom ≫
        (twoPointCoproductIso R).hom ≫
          biprod.desc (𝟙 R) (𝟙 R) =
      Sigma.desc (fun _ : J ↦ 𝟙 R) := by
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_reindex_hom_assoc]
  generalize hb : e j = b
  rcases b with ⟨b⟩
  cases b <;> simp [twoPointCoproductIso] <;>
    rw [Sigma.ι_comp_desc]

noncomputable local instance :
    TotallyDisconnectedSpace (TopCat.sphere.{w} 0) :=
  (TopCat.homeoOfIso zeroSphereIsoTwoPoint.{w}).symm.totallyDisconnectedSpace

private noncomputable def zeroSpherePointComponentEquiv :
    TopCat.sphere.{w} 0 ≃ ZerothHomotopy (TopCat.sphere.{w} 0) :=
  Equiv.ofBijective (ZerothHomotopy.mk (X := TopCat.sphere.{w} 0)) ⟨by
    intro x y hxy
    have hj : Joined x y := Quotient.exact hxy
    have hy : y ∈ connectedComponent x :=
      pathComponent_subset_component x ((mem_pathComponent_iff).2 hj)
    have hyx : y = x := by
      simpa only [connectedComponent_eq_singleton, Set.mem_singleton_iff] using hy
    exact hyx.symm, ZerothHomotopy.mk_surjective⟩

/-- The path components of the zero-sphere are its two explicit points. -/
noncomputable def zeroSphereComponentsEquivTwoPoint :
    ZerothHomotopy (TopCat.sphere.{w} 0) ≃ ULift.{w} Bool :=
  zeroSpherePointComponentEquiv.symm.trans
    (TopCat.homeoOfIso zeroSphereIsoTwoPoint.{w}).toEquiv

/-- Ordinary zeroth homology of the zero-sphere is the binary biproduct of
two copies of the coefficient object. -/
noncomputable def singularHomologyZeroIsoSphereZero (R : C) :
    ((singularHomologyFunctor.{w} C 0).obj R).obj (TopCat.sphere.{w} 0) ≅
      (R ⊞ R) :=
  (TopCat.sphere.{w} 0).singularHomology₀Iso R ≪≫
    Sigma.reindex zeroSphereComponentsEquivTwoPoint
      (fun _ : ULift.{w} Bool ↦ R) ≪≫
    twoPointCoproductIso R

@[reassoc (attr := simp)]
lemma singularHomologyZeroIsoSphereZero_hom_codiagonal (R : C) :
    (singularHomologyZeroIsoSphereZero R).hom ≫
        biprod.desc (𝟙 R) (𝟙 R) =
      (TopCat.sphere.{w} 0).singularHomology₀ε R := by
  rw [show (singularHomologyZeroIsoSphereZero R).hom =
    ((TopCat.sphere.{w} 0).singularHomology₀Iso R).hom ≫
      (Sigma.reindex zeroSphereComponentsEquivTwoPoint
        (fun _ : ULift.{w} Bool ↦ R)).hom ≫
      (twoPointCoproductIso R).hom from rfl]
  rw [Category.assoc, Category.assoc,
    reindex_twoPointCoproductIso_hom_codiagonal]
  exact (TopCat.sphere.{w} 0).singularHomology₀Iso_sigma_desc_id R

set_option backward.isDefEq.respectTransparency false in
private lemma singularHomologyZeroQuotient_comp_epsilon
    (R : C) (X : TopCat.{w}) :
    let K := (TopCat.toSSet.obj X).chainComplex R
    (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv) ≫ X.singularHomology₀ε R =
      Sigma.desc (fun _ : (TopCat.toSSet.obj X) _⦋0⦌ ↦ 𝟙 R) := by
  dsimp only
  let K := (TopCat.toSSet.obj X).chainComplex R
  change (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv) ≫
      SSet.homology₀ε (TopCat.toSSet.obj X) R =
    Sigma.desc (fun _ : (TopCat.toSSet.obj X) _⦋0⦌ ↦ 𝟙 R)
  have hquotient :
      K.pOpcycles 0 ≫ K.isoHomologyι₀.inv =
        K.cycles₀Iso.inv ≫ K.homologyπ 0 := by
    rw [← cancel_mono (K.homologyι 0)]
    simp
  rw [hquotient]
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro x
  have hlift :
      (TopCat.toSSet.obj X).ιChainComplex x ≫ K.cycles₀Iso.inv =
        K.liftCycles ((TopCat.toSSet.obj X).ιChainComplex x) 0
          (by simp) (by simp) := by
    rw [← cancel_mono (K.iCycles 0)]
    simp
    exact Category.comp_id _
  calc
    (TopCat.toSSet.obj X).ιChainComplex x ≫
          ((K.cycles₀Iso.inv ≫ K.homologyπ 0) ≫
            (TopCat.toSSet.obj X).homology₀ε R) =
        ((TopCat.toSSet.obj X).ιChainComplex x ≫ K.cycles₀Iso.inv) ≫
          (K.homologyπ 0 ≫ (TopCat.toSSet.obj X).homology₀ε R) := by
      simp only [Category.assoc]
    _ = K.liftCycles ((TopCat.toSSet.obj X).ιChainComplex x) 0
          (by simp) (by simp) ≫
            (K.homologyπ 0 ≫ (TopCat.toSSet.obj X).homology₀ε R) := by
      rw [hlift]
    _ = 𝟙 R :=
      SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
        (TopCat.toSSet.obj X) R x
    _ = (TopCat.toSSet.obj X).ιChainComplex x ≫
        Sigma.desc (fun _ : (TopCat.toSSet.obj X) _⦋0⦌ ↦ 𝟙 R) := by
      change 𝟙 R =
        Sigma.ι (fun _ : (TopCat.toSSet.obj X) _⦋0⦌ ↦ R) x ≫
          Sigma.desc (fun _ : (TopCat.toSSet.obj X) _⦋0⦌ ↦ 𝟙 R)
      rw [Sigma.ι_comp_desc]

private noncomputable def ordinaryHomologyZeroIsoAugmentedOpcycles
    (R : C) (X : TopCat.{w}) :
    ((singularHomologyFunctor.{w} C 0).obj R).obj X ≅
      ((Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj X).opcycles 1 := by
  let K := (TopCat.toSSet.obj X).chainComplex R
  let A := (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj X
  let hK := K.opcyclesIsCokernel 1 0 (by simp)
  let hA := A.opcyclesIsCokernel 2 1 (by simp)
  dsimp [A, Hatcher.Reduced.augmentedSingularChainComplexFunctor,
    ChainComplex.augment] at hA
  change K.homology 0 ≅ A.opcycles 1
  exact K.isoHomologyι₀ ≪≫
    IsColimit.coconePointUniqueUpToIso hK hA

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma ordinaryHomologyZeroIsoAugmentedOpcycles_hom_from
    (R : C) (X : TopCat.{w}) :
    (ordinaryHomologyZeroIsoAugmentedOpcycles R X).hom ≫
        ((Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj X).fromOpcycles 1 0 =
      X.singularHomology₀ε R := by
  let K := (TopCat.toSSet.obj X).chainComplex R
  let A := (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj X
  let e₀ : K.homology 0 ≅ K.opcycles 0 := K.isoHomologyι₀
  let hK := K.opcyclesIsCokernel 1 0 (by simp)
  let hA := A.opcyclesIsCokernel 2 1 (by simp)
  dsimp [A, Hatcher.Reduced.augmentedSingularChainComplexFunctor,
    ChainComplex.augment] at hA
  let e₁ : K.opcycles 0 ≅ A.opcycles 1 :=
    IsColimit.coconePointUniqueUpToIso hK hA
  change (e₀ ≪≫ e₁).hom ≫ A.fromOpcycles 1 0 =
    X.singularHomology₀ε R
  rw [← cancel_epi (K.pOpcycles 0 ≫ e₀.inv)]
  have hp : K.pOpcycles 0 ≫ e₁.hom = A.pOpcycles 1 :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hK hA
      WalkingParallelPair.one
  calc
    (K.pOpcycles 0 ≫ e₀.inv) ≫
          (e₀ ≪≫ e₁).hom ≫ A.fromOpcycles 1 0 =
        K.pOpcycles 0 ≫ e₁.hom ≫ A.fromOpcycles 1 0 := by simp
    _ = A.pOpcycles 1 ≫ A.fromOpcycles 1 0 := by
      rw [← Category.assoc, hp]
    _ = A.d 1 0 := A.p_fromOpcycles 1 0
    _ = Hatcher.Reduced.chainAugmentation R X := rfl
    _ = Sigma.desc (fun _ : (TopCat.toSSet.obj X) _⦋0⦌ ↦ 𝟙 R) := rfl
    _ = (K.pOpcycles 0 ≫ e₀.inv) ≫ X.singularHomology₀ε R :=
      by simpa only [e₀] using
        (singularHomologyZeroQuotient_comp_epsilon R X).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma ordinaryHomologyZeroIsoAugmentedOpcycles_inv_epsilon
    (R : C) (X : TopCat.{w}) :
    (ordinaryHomologyZeroIsoAugmentedOpcycles R X).inv ≫
        X.singularHomology₀ε R =
      ((Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj X).fromOpcycles 1 0 := by
  let A := (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj X
  let e := ordinaryHomologyZeroIsoAugmentedOpcycles R X
  change e.inv ≫ X.singularHomology₀ε R = A.fromOpcycles 1 0
  calc
    e.inv ≫ X.singularHomology₀ε R =
        e.inv ≫ (e.hom ≫ A.fromOpcycles 1 0) := by
      rw [ordinaryHomologyZeroIsoAugmentedOpcycles_hom_from]
    _ = A.fromOpcycles 1 0 := by simp

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from reduced zeroth homology of the zero-sphere to
ordinary zeroth homology. -/
noncomputable def reducedHomologyZeroSphereToOrdinary (R : C) :
    (Hatcher.Reduced.homologyFunctor.{w} R 0).obj (TopCat.sphere.{w} 0) ⟶
      ((singularHomologyFunctor.{w} C 0).obj R).obj (TopCat.sphere.{w} 0) :=
  ((Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj
      (TopCat.sphere.{w} 0)).homologyι 1 ≫
    (ordinaryHomologyZeroIsoAugmentedOpcycles R (TopCat.sphere.{w} 0)).inv

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma reducedHomologyZeroSphereToOrdinary_comp_epsilon (R : C) :
    reducedHomologyZeroSphereToOrdinary R ≫
      (TopCat.sphere.{w} 0).singularHomology₀ε R = 0 := by
  let A := (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj
    (TopCat.sphere.{w} 0)
  let e := ordinaryHomologyZeroIsoAugmentedOpcycles R (TopCat.sphere.{w} 0)
  change (A.homologyι 1 ≫ e.inv) ≫
    (TopCat.sphere.{w} 0).singularHomology₀ε R = 0
  calc
    (A.homologyι 1 ≫ e.inv) ≫
        (TopCat.sphere.{w} 0).singularHomology₀ε R =
      A.homologyι 1 ≫
        (e.inv ≫ (TopCat.sphere.{w} 0).singularHomology₀ε R) :=
      Category.assoc _ _ _
    _ = A.homologyι 1 ≫ A.fromOpcycles 1 0 := by
      rw [ordinaryHomologyZeroIsoAugmentedOpcycles_inv_epsilon]
    _ = 0 := HomologicalComplex.homologyι_comp_fromOpcycles A 1 0

set_option backward.isDefEq.respectTransparency false in
/-- Reduced zeroth homology of the zero-sphere is the kernel of the ordinary
zeroth-homology augmentation. -/
noncomputable def reducedHomologyZeroSphereToOrdinaryIsKernel (R : C) :
    IsLimit (KernelFork.ofι (reducedHomologyZeroSphereToOrdinary R)
      (reducedHomologyZeroSphereToOrdinary_comp_epsilon R)) := by
  let A := (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj
    (TopCat.sphere.{w} 0)
  let e := ordinaryHomologyZeroIsoAugmentedOpcycles R (TopCat.sphere.{w} 0)
  have h := KernelFork.isLimitOfIsLimitOfIff
    (A.homologyIsKernel 1 0 (by simp))
    ((TopCat.sphere.{w} 0).singularHomology₀ε R) e.symm
    (fun {_} φ ↦ by
      change φ ≫ A.fromOpcycles 1 0 = 0 ↔
        φ ≫ e.inv ≫
          (TopCat.sphere.{w} 0).singularHomology₀ε R = 0
      have heq :
          φ ≫ (e.inv ≫ (TopCat.sphere.{w} 0).singularHomology₀ε R) =
            φ ≫ A.fromOpcycles 1 0 := by
        rw [ordinaryHomologyZeroIsoAugmentedOpcycles_inv_epsilon]
      constructor
      · intro hφ
        exact heq.trans hφ
      · intro hφ
        exact heq.symm.trans hφ)
  simpa only [reducedHomologyZeroSphereToOrdinary, A, e,
    KernelFork.ι_ofι, Iso.symm_hom] using h

private noncomputable def antidiagonalIsKernelCodiagonal (R : C) :
    IsLimit (KernelFork.ofι (biprod.lift (𝟙 R) (-𝟙 R)) (by simp) :
      KernelFork (biprod.desc (𝟙 R) (𝟙 R))) := by
  let S : ShortComplex C := ShortComplex.mk
    (biprod.lift (𝟙 R) (-𝟙 R))
    (biprod.desc (𝟙 R) (𝟙 R)) (by simp)
  let s : S.Splitting :=
    { r := biprod.fst
      s := biprod.inr
      f_r := by dsimp [S]; simp
      s_g := by dsimp [S]; simp
      id := by dsimp [S]; ext <;> simp }
  simpa only [S] using s.fIsKernel

private noncomputable def reducedHomologyZeroSphereToBiprodIsKernel (R : C) :
    IsLimit (KernelFork.ofι
      (reducedHomologyZeroSphereToOrdinary R ≫
        (singularHomologyZeroIsoSphereZero R).hom)
      (by simp) : KernelFork (biprod.desc (𝟙 R) (𝟙 R))) := by
  have h := KernelFork.isLimitOfIsLimitOfIff
    (reducedHomologyZeroSphereToOrdinaryIsKernel R)
    (biprod.desc (𝟙 R) (𝟙 R))
    (singularHomologyZeroIsoSphereZero R)
    (fun {_} φ ↦ by
      have heq :
          φ ≫ ((singularHomologyZeroIsoSphereZero R).hom ≫
              biprod.desc (𝟙 R) (𝟙 R)) =
            φ ≫ (TopCat.sphere.{w} 0).singularHomology₀ε R := by
        rw [singularHomologyZeroIsoSphereZero_hom_codiagonal]
      constructor
      · intro hφ
        exact heq.trans hφ
      · intro hφ
        exact heq.symm.trans hφ)
  simpa using h

/-- Reduced zeroth homology of the zero-sphere is the antidiagonal copy of
the coefficient object in ordinary zeroth homology. -/
noncomputable def reducedHomologyZeroSphereIso (R : C) :
    (Hatcher.Reduced.homologyFunctor.{w} R 0).obj (TopCat.sphere.{w} 0) ≅ R :=
  (reducedHomologyZeroSphereToBiprodIsKernel R).conePointUniqueUpToIso
    (antidiagonalIsKernelCodiagonal R)

/-- Positive-degree reduced homology of the zero-sphere vanishes. -/
lemma isZero_reducedHomology_sphere_zero (R : C) (i : ℕ) (hi : i ≠ 0) :
    IsZero ((Hatcher.Reduced.homologyFunctor.{w} R i).obj
      (TopCat.sphere.{w} 0)) :=
  (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      C i R (TopCat.sphere.{w} 0) hi).of_iso
    ((Hatcher.Reduced.homologyIsoOfPositiveDegree R i
      (Nat.pos_of_ne_zero hi)).app (TopCat.sphere.{w} 0))

/-- **Hatcher, Corollary 2.14 (page 114), base case.** The reduced homology
of `S⁰` is the coefficient object in degree zero and vanishes in every
positive degree. -/
theorem reducedHomology_sphere_zero (R : C) :
    Nonempty
        ((Hatcher.Reduced.homologyFunctor.{w} R 0).obj
          (TopCat.sphere.{w} 0) ≅ R) ∧
      ∀ i, i ≠ 0 →
        IsZero ((Hatcher.Reduced.homologyFunctor.{w} R i).obj
          (TopCat.sphere.{w} 0)) :=
  ⟨⟨reducedHomologyZeroSphereIso R⟩,
    isZero_reducedHomology_sphere_zero R⟩

end Hatcher.Sphere
