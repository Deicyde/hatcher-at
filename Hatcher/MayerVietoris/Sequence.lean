/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Excision.BinaryCover
import Hatcher.MayerVietoris.ShortExact
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# The Mayer--Vietoris sequence

This file transports the homology sequence of the binary small-chain short
complex to singular homology of the actual subspaces and ambient space.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Simplicial Opposite Topology

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

namespace Hatcher.MayerVietoris

universe w v u

variable {X : TopCat.{w}}
variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]

local instance sequenceHasFiniteCoproducts : HasFiniteCoproducts C :=
  hasFiniteCoproducts_of_hasCoproducts C

local instance sequenceHasBinaryBiproducts : HasBinaryBiproducts C :=
  HasBinaryBiproducts.of_hasBinaryCoproducts

private noncomputable abbrev subspaceInclusion (V : Set X) :
    TopCat.of ↥V ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, by fun_prop⟩

private noncomputable abbrev intersectionToLeft (A B : Set X) :
    TopCat.of ↥(A ∩ B) ⟶ TopCat.of ↥A :=
  TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left)

private noncomputable abbrev intersectionToRight (A B : Set X) :
    TopCat.of ↥(A ∩ B) ⟶ TopCat.of ↥B :=
  TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_right)

private lemma mono_toSSetMap_of_injective {Y Z : TopCat.{w}}
    (f : Y ⟶ Z) (hf : Function.Injective f) :
    Mono (TopCat.toSSet.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro ⟨⟨n⟩⟩
  rw [CategoryTheory.mono_iff_injective]
  intro x y hxy
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext t
  exact hf
    (DFunLike.congr_fun
      ((TopCat.toSSetObjEquiv Z (op ⦋n⦌)).congr_arg hxy) t)

private noncomputable def subspaceChainIso (V : Set X) (R : C) :
    Hatcher.Excision.singularChains (TopCat.of ↥V) R ≅
      ((Hatcher.Excision.smallSubcomplexOfSet V : SSet.{w})).chainComplex R := by
  letI : Mono (TopCat.toSSet.map (subspaceInclusion V)) :=
    mono_toSSetMap_of_injective _ Subtype.val_injective
  exact ((SSet.chainComplexFunctor C).obj R).mapIso
    (asIso (SSet.Subcomplex.toRange
      (TopCat.toSSet.map (subspaceInclusion V))))

private noncomputable abbrev subspaceChains (V : Set X) (R : C) :
    ChainComplex C ℕ :=
  Hatcher.Excision.singularChains (TopCat.of ↥V) R

private noncomputable abbrev subspaceChainMap (V : Set X) (R : C) :
    subspaceChains V R ⟶
      Hatcher.Excision.singularChains X R :=
  Hatcher.Excision.singularChainMap (subspaceInclusion V) R

private noncomputable abbrev intersectionToLeftSubspaceChainMap
    (A B : Set X) (R : C) :
    subspaceChains (A ∩ B) R ⟶ subspaceChains A R :=
  Hatcher.Excision.singularChainMap (intersectionToLeft A B) R

private noncomputable abbrev intersectionToRightSubspaceChainMap
    (A B : Set X) (R : C) :
    subspaceChains (A ∩ B) R ⟶ subspaceChains B R :=
  Hatcher.Excision.singularChainMap (intersectionToRight A B) R

private noncomputable def subspaceBiprodChainIso
    (A B : Set X) (R : C) :
    subspaceChains A R ⊞ subspaceChains B R ≅
      ((Hatcher.Excision.smallSubcomplexOfSet A : SSet.{w})).chainComplex R ⊞
        ((Hatcher.Excision.smallSubcomplexOfSet B : SSet.{w})).chainComplex R :=
  biprod.mapIso (subspaceChainIso A R) (subspaceChainIso B R)

@[reassoc]
private lemma subspaceChainIso_hom_comp_intersectionToLeftChainMap
    (A B : Set X) (R : C) :
    (subspaceChainIso (A ∩ B) R).hom ≫
        intersectionToLeftChainMap A B R =
      intersectionToLeftSubspaceChainMap A B R ≫
        (subspaceChainIso A R).hom := by
  change
    SSet.chainComplexMap
          (SSet.Subcomplex.toRange
            (TopCat.toSSet.map (subspaceInclusion (A ∩ B)))) R ≫
        SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (smallCoverBicartSq A B).le₁₂) R =
      SSet.chainComplexMap (TopCat.toSSet.map (intersectionToLeft A B)) R ≫
        SSet.chainComplexMap
          (SSet.Subcomplex.toRange
            (TopCat.toSSet.map (subspaceInclusion A))) R
  simp only [← Functor.map_comp]
  congr 1

@[reassoc]
private lemma subspaceChainIso_hom_comp_intersectionToRightChainMap
    (A B : Set X) (R : C) :
    (subspaceChainIso (A ∩ B) R).hom ≫
        intersectionToRightChainMap A B R =
      intersectionToRightSubspaceChainMap A B R ≫
        (subspaceChainIso B R).hom := by
  change
    SSet.chainComplexMap
          (SSet.Subcomplex.toRange
            (TopCat.toSSet.map (subspaceInclusion (A ∩ B)))) R ≫
        SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (smallCoverBicartSq A B).le₁₃) R =
      SSet.chainComplexMap (TopCat.toSSet.map (intersectionToRight A B)) R ≫
        SSet.chainComplexMap
          (SSet.Subcomplex.toRange
            (TopCat.toSSet.map (subspaceInclusion B))) R
  simp only [← Functor.map_comp]
  congr 1

/-- The signed intersection map on the singular chain complexes of the
actual subspaces, obtained from the canonical small-subcomplex map. -/
noncomputable def singularChainComplexIntersectionMap
    (A B : Set X) (R : C) :
    Hatcher.Excision.singularChains (TopCat.of ↥(A ∩ B)) R ⟶
      Hatcher.Excision.singularChains (TopCat.of ↥A) R ⊞
        Hatcher.Excision.singularChains (TopCat.of ↥B) R :=
  (subspaceChainIso (A ∩ B) R).hom ≫
    chainComplexIntersectionMap A B R ≫
    (subspaceBiprodChainIso A B R).inv

/-- The addition map from the singular chains of the two actual subspaces to
the small-cover chain complex. -/
noncomputable def singularChainComplexUnionMap
    (A B : Set X) (R : C) :
    Hatcher.Excision.singularChains (TopCat.of ↥A) R ⊞
        Hatcher.Excision.singularChains (TopCat.of ↥B) R ⟶
      smallCoverChains A B R :=
  (subspaceBiprodChainIso A B R).hom ≫ chainComplexUnionMap A B R

private lemma singularChainComplexIntersectionMap_eq
    (A B : Set X) (R : C) :
    singularChainComplexIntersectionMap A B R =
      biprod.lift
        (intersectionToLeftSubspaceChainMap A B R)
        (-intersectionToRightSubspaceChainMap A B R) := by
  apply biprod.hom_ext
  · simp only [singularChainComplexIntersectionMap, subspaceBiprodChainIso,
      chainComplexIntersectionMap, Category.assoc, biprod.mapIso_inv,
      biprod.map_fst, biprod.lift_fst_assoc]
    rw [← Category.assoc,
      subspaceChainIso_hom_comp_intersectionToLeftChainMap]
    simp
  · simp only [singularChainComplexIntersectionMap, subspaceBiprodChainIso,
      chainComplexIntersectionMap, Category.assoc, biprod.mapIso_inv,
      biprod.map_snd, biprod.lift_snd_assoc]
    rw [biprod.lift_snd]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp]
    congr 1
    rw [← Category.assoc,
      subspaceChainIso_hom_comp_intersectionToRightChainMap]
    simp

@[reassoc (attr := simp)]
private lemma singularChainComplexIntersectionMap_comp_unionMap
    (A B : Set X) (R : C) :
    singularChainComplexIntersectionMap A B R ≫
      singularChainComplexUnionMap A B R = 0 := by
  simp [singularChainComplexIntersectionMap, singularChainComplexUnionMap,
    Category.assoc]

/-- The binary-cover chain short complex expressed using singular chains of
the actual subspaces and the small-cover complex in the third term. -/
private noncomputable abbrev singularChainComplexShortComplex
    (A B : Set X) (R : C) : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (singularChainComplexIntersectionMap A B R)
    (singularChainComplexUnionMap A B R)
    (singularChainComplexIntersectionMap_comp_unionMap A B R)

private noncomputable def chainComplexShortComplexIso
    (A B : Set X) (R : C) :
    chainComplexShortComplex A B R ≅ singularChainComplexShortComplex A B R :=
  ShortComplex.isoMk (subspaceChainIso (A ∩ B) R).symm
    (subspaceBiprodChainIso A B R).symm (Iso.refl _)
    (by simp [chainComplexShortComplex, singularChainComplexShortComplex,
      singularChainComplexIntersectionMap])
    (by simp [chainComplexShortComplex, singularChainComplexShortComplex,
      singularChainComplexUnionMap])

private theorem singularChainComplexShortComplex_shortExact
    (A B : Set X) (R : C) :
    (singularChainComplexShortComplex A B R).ShortExact :=
  ShortComplex.shortExact_of_iso (chainComplexShortComplexIso A B R)
    (chainComplexShortComplex_shortExact (C := C) A B R)

private noncomputable abbrev homologyBiprodIso
    (A B : Set X) (R : C) (n : ℕ) :
    (subspaceChains A R ⊞ subspaceChains B R).homology n ≅
      (subspaceChains A R).homology n ⊞
        (subspaceChains B R).homology n :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).mapBiprod _ _

/-- For a binary interior cover, the homology of the small-cover chain
complex is canonically isomorphic to the singular homology of the ambient
space. -/
noncomputable def smallCoverHomologyIso
    {A B : Set X} (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (n : ℕ) :
  (smallCoverChains A B R).homology n ≅
      (Hatcher.Excision.singularChains X R).homology n :=
  (Hatcher.Excision.smallChainInclusionHomotopyEquiv
    h.smallSimplicesCondition R).toHomologyIso n

/-- The first map in the Mayer--Vietoris sequence, with Hatcher's sign
convention `x ↦ (x, -x)`. -/
noncomputable def intersectionMap (A B : Set X) (R : C) (n : ℕ) :
    (Hatcher.Excision.singularChains (TopCat.of ↥(A ∩ B)) R).homology n ⟶
      (Hatcher.Excision.singularChains (TopCat.of ↥A) R).homology n ⊞
        (Hatcher.Excision.singularChains (TopCat.of ↥B) R).homology n :=
  biprod.lift
    (HomologicalComplex.homologyMap
      (intersectionToLeftSubspaceChainMap A B R) n)
    (-HomologicalComplex.homologyMap
      (intersectionToRightSubspaceChainMap A B R) n)

/-- The second map in the Mayer--Vietoris sequence, induced by addition of
the two inclusion maps into the ambient space. -/
noncomputable def unionMap (A B : Set X) (R : C) (n : ℕ) :
    (Hatcher.Excision.singularChains (TopCat.of ↥A) R).homology n ⊞
        (Hatcher.Excision.singularChains (TopCat.of ↥B) R).homology n ⟶
      (Hatcher.Excision.singularChains X R).homology n :=
  biprod.desc
    (HomologicalComplex.homologyMap (subspaceChainMap A R) n)
    (HomologicalComplex.homologyMap (subspaceChainMap B R) n)

@[reassoc]
private lemma subspaceChainIso_hom_comp_leftToSmallCoverChainMap_comp_inclusion
    {A B : Set X} (h : Hatcher.Excision.CoverCondition A B) (R : C) :
    (subspaceChainIso A R).hom ≫ leftToSmallCoverChainMap A B R ≫
        (Hatcher.Excision.smallChainInclusionHomotopyEquiv
          h.smallSimplicesCondition R).hom =
      subspaceChainMap A R := by
  rw [Hatcher.Excision.smallChainInclusionHomotopyEquiv_hom]
  dsimp [subspaceChainIso, leftToSmallCoverChainMap, subspaceChainMap,
    Hatcher.Excision.singularChainMap, Hatcher.Excision.singularChains,
    AlgebraicTopology.singularChainComplexFunctor, smallCoverChains]
  simp only [← Functor.map_comp]
  congr 1

@[reassoc]
private lemma subspaceChainIso_hom_comp_rightToSmallCoverChainMap_comp_inclusion
    {A B : Set X} (h : Hatcher.Excision.CoverCondition A B) (R : C) :
    (subspaceChainIso B R).hom ≫ rightToSmallCoverChainMap A B R ≫
        (Hatcher.Excision.smallChainInclusionHomotopyEquiv
          h.smallSimplicesCondition R).hom =
      subspaceChainMap B R := by
  rw [Hatcher.Excision.smallChainInclusionHomotopyEquiv_hom]
  dsimp [subspaceChainIso, rightToSmallCoverChainMap, subspaceChainMap,
    Hatcher.Excision.singularChainMap, Hatcher.Excision.singularChains,
    AlgebraicTopology.singularChainComplexFunctor, smallCoverChains]
  simp only [← Functor.map_comp]
  congr 1

@[reassoc]
private lemma singularChainComplexUnionMap_comp_inclusion
    {A B : Set X} (h : Hatcher.Excision.CoverCondition A B) (R : C) :
    singularChainComplexUnionMap A B R ≫
        (Hatcher.Excision.smallChainInclusionHomotopyEquiv
          h.smallSimplicesCondition R).hom =
      biprod.desc (subspaceChainMap A R) (subspaceChainMap B R) := by
  apply biprod.hom_ext'
  · simpa only [singularChainComplexUnionMap, subspaceBiprodChainIso,
      chainComplexUnionMap, biprod.mapIso_hom, Category.assoc,
      biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc] using
      subspaceChainIso_hom_comp_leftToSmallCoverChainMap_comp_inclusion h R
  · simpa only [singularChainComplexUnionMap, subspaceBiprodChainIso,
      chainComplexUnionMap, biprod.mapIso_hom, Category.assoc,
      biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc] using
      subspaceChainIso_hom_comp_rightToSmallCoverChainMap_comp_inclusion h R

private lemma homologyMap_intersection_comp_homologyBiprodIso
    (A B : Set X) (R : C) (n : ℕ) :
    HomologicalComplex.homologyMap
        (singularChainComplexIntersectionMap A B R) n ≫
      (homologyBiprodIso A B R n).hom = intersectionMap A B R n := by
  rw [singularChainComplexIntersectionMap_eq]
  exact
    (biprod.map_lift_mapBiprod
      (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n)
      (subspaceChains A R) (subspaceChains B R)
      (intersectionToLeftSubspaceChainMap A B R)
      (-intersectionToRightSubspaceChainMap A B R)).trans
      (by rw [Functor.map_neg]; rfl)

private lemma homologyBiprodIso_hom_comp_unionMap
    {A B : Set X} (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (n : ℕ) :
    (homologyBiprodIso A B R n).hom ≫ unionMap A B R n =
      HomologicalComplex.homologyMap
          (singularChainComplexUnionMap A B R) n ≫
        (smallCoverHomologyIso h R n).hom := by
  rw [smallCoverHomologyIso]
  change _ = HomologicalComplex.homologyMap
      (singularChainComplexUnionMap A B R) n ≫
        HomologicalComplex.homologyMap
          (Hatcher.Excision.smallChainInclusionHomotopyEquiv
            h.smallSimplicesCondition R).hom n
  rw [← HomologicalComplex.homologyMap_comp,
    singularChainComplexUnionMap_comp_inclusion h R]
  change (homologyBiprodIso A B R n).hom ≫
      biprod.desc
        (HomologicalComplex.homologyMap (subspaceChainMap A R) n)
        (HomologicalComplex.homologyMap (subspaceChainMap B R) n) = _
  exact
    biprod.mapBiprod_hom_desc
      (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n)
      (subspaceChains A R) (subspaceChains B R)
      (subspaceChainMap A R) (subspaceChainMap B R)

/-- The Mayer--Vietoris connecting morphism. -/
noncomputable def connecting {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (n m : ℕ) (hnm : m + 1 = n) :
    (Hatcher.Excision.singularChains X R).homology n ⟶
      (Hatcher.Excision.singularChains (TopCat.of ↥(A ∩ B)) R).homology m :=
  (smallCoverHomologyIso h R n).inv ≫
    (singularChainComplexShortComplex_shortExact A B R).δ n m
      (by simpa using hnm)

private noncomputable abbrev smallSequence
    (A B : Set X) (R : C) (n m : ℕ) (hnm : m + 1 = n) :
    ComposableArrows C 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    (singularChainComplexShortComplex_shortExact A B R)
    n m (by simpa using hnm)

/-- Six consecutive terms in the binary-cover Mayer--Vietoris sequence. -/
noncomputable def sequence {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (n m : ℕ) (hnm : m + 1 = n) :
    ComposableArrows C 5 :=
  ComposableArrows.mk₅
    (intersectionMap A B R n)
    (unionMap A B R n)
    (connecting h R n m hnm)
    (intersectionMap A B R m)
    (unionMap A B R m)

private noncomputable def smallSequenceIso {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (n m : ℕ) (hnm : m + 1 = n) :
    smallSequence A B R n m hnm ≅ sequence h R n m hnm :=
  ComposableArrows.isoMk₅
    (Iso.refl _) (homologyBiprodIso A B R n)
    (smallCoverHomologyIso h R n) (Iso.refl _)
    (homologyBiprodIso A B R m) (smallCoverHomologyIso h R m)
    (by
      dsimp [smallSequence, sequence, singularChainComplexShortComplex,
        intersectionMap]
      rw [Category.id_comp]
      exact homologyMap_intersection_comp_homologyBiprodIso A B R n)
    (by
      simpa [smallSequence, sequence, singularChainComplexShortComplex] using
        (homologyBiprodIso_hom_comp_unionMap h R n).symm)
    (by
      simp [smallSequence, sequence, connecting])
    (by
      dsimp [smallSequence, sequence, singularChainComplexShortComplex,
        intersectionMap]
      rw [Category.id_comp]
      exact homologyMap_intersection_comp_homologyBiprodIso A B R m)
    (by
      simpa [smallSequence, sequence, singularChainComplexShortComplex] using
        (homologyBiprodIso_hom_comp_unionMap h R m).symm)

/-- **Hatcher, §2.2.** Every adjacent-degree six-term window in the
binary-cover Mayer--Vietoris sequence is exact. -/
theorem sequence_exact {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (n m : ℕ) (hnm : m + 1 = n) :
    (sequence h R n m hnm).Exact := by
  apply ComposableArrows.exact_of_iso (smallSequenceIso h R n m hnm)
  exact HomologicalComplex.HomologySequence.composableArrows₅_exact
    (singularChainComplexShortComplex_shortExact A B R)
    n m (by simpa using hnm)

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero map from the homology of the two cover members onto the
homology of the ambient space is an epimorphism. -/
theorem unionMap_zero_epi {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B) (R : C) :
    Epi (unionMap A B R 0) := by
  letI : Epi (singularChainComplexUnionMap A B R) :=
    (singularChainComplexShortComplex_shortExact A B R).epi_g
  have hEpi : Epi
      (HomologicalComplex.homologyMap
          (singularChainComplexUnionMap A B R) 0 ≫
        (smallCoverHomologyIso h R 0).hom) := by
    have : Epi (HomologicalComplex.homologyMap
        (singularChainComplexUnionMap A B R) 0) :=
      HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)
    infer_instance
  rw [← homologyBiprodIso_hom_comp_unionMap h R 0] at hEpi
  exact (epi_comp_iff_of_epi (homologyBiprodIso A B R 0).hom _).1 hEpi

/-- The connecting morphism sends a small cycle decomposed into an `A`-chain
and a `B`-chain to the class of the common boundary in `A ∩ B`. -/
theorem connecting_eq {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (n m : ℕ) (hnm : m + 1 = n)
    {T : C}
    (z : T ⟶ (smallCoverChains A B R).X n)
    (hz : z ≫ (smallCoverChains A B R).d n m = 0)
    (xy : T ⟶ (Hatcher.Excision.singularChains (TopCat.of ↥A) R ⊞
      Hatcher.Excision.singularChains (TopCat.of ↥B) R).X n)
    (hxy : xy ≫ (singularChainComplexUnionMap A B R).f n = z)
    (boundary : T ⟶
      (Hatcher.Excision.singularChains (TopCat.of ↥(A ∩ B)) R).X m)
    (hboundary :
      boundary ≫ (singularChainComplexIntersectionMap A B R).f m =
        xy ≫ (Hatcher.Excision.singularChains (TopCat.of ↥A) R ⊞
          Hatcher.Excision.singularChains (TopCat.of ↥B) R).d n m)
    (k : ℕ) (hk : (ComplexShape.down ℕ).next m = k)
    (hboundaryCycle :
      boundary ≫
        (Hatcher.Excision.singularChains (TopCat.of ↥(A ∩ B)) R).d m k = 0) :
    (smallCoverChains A B R).liftCycles z m
          ((ComplexShape.down ℕ).next_eq' (by simpa using hnm)) hz ≫
        (smallCoverChains A B R).homologyπ n ≫
        (smallCoverHomologyIso h R n).hom ≫
        connecting h R n m hnm =
      (Hatcher.Excision.singularChains
          (TopCat.of ↥(A ∩ B)) R).liftCycles
          boundary k hk hboundaryCycle ≫
        (Hatcher.Excision.singularChains
          (TopCat.of ↥(A ∩ B)) R).homologyπ m := by
  let hS := singularChainComplexShortComplex_shortExact A B R
  have hδ := hS.δ_eq n m (by simpa using hnm)
    z hz xy hxy boundary hboundary k hk
  simpa [connecting, Category.assoc] using hδ

end Hatcher.MayerVietoris
