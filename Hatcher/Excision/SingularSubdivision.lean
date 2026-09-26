/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Joël Riou, Jack McCarthy

This file adapts the singular-subdivision construction from
`joelriou/excision` at commit `8b56cd0c8e5f39a7c2f36418c80b298e469596a6`
to the Mathlib version pinned by this project.
-/

import Hatcher.Excision.AffineChains
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology

/-!
# Barycentric subdivision of singular chains

Affine subdivision of the standard simplex is transported along each singular
simplex.  This produces a natural subdivision endomorphism of singular chains
and a homotopy from the identity to every finite iterate.
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Convexity
  Simplicial Opposite

namespace Hatcher.Excision

universe w v u

section AffineTopology

@[fun_prop]
lemma continuous_stdSimplexAffineMap {ι₁ ι₂ : Type*} [Finite ι₂]
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ ι₁) (StdSimplex ℝ ι₂)) :
    Continuous s := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ ι₂).continuous_iff]
  rw [continuous_pi_iff]
  intro i
  apply StdSimplex.continuous_of_isAffineMap
  exact ((StdSimplex.isAffineMap_weights ℝ ι₂).finsuppEval i).comp
    s.isAffineMap_toFun

/-- An affine map between finite standard simplices, regarded as a continuous
map. -/
def affineToContinuousMap {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ ι₁) (StdSimplex ℝ ι₂)) :
    C(StdSimplex ℝ ι₁, StdSimplex ℝ ι₂) where
  toFun := s
  continuous_toFun := continuous_stdSimplexAffineMap s

lemma affineToContinuousMap_comp
    {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ ι₂) (StdSimplex ℝ ι₃))
    (t : ConvexSpace.AffineMap ℝ (StdSimplex ℝ ι₁) (StdSimplex ℝ ι₂)) :
    affineToContinuousMap (s.comp t) =
      (affineToContinuousMap s).comp (affineToContinuousMap t) := by
  ext
  rfl

@[simp]
lemma affineToContinuousMap_id (ι : Type*) [Fintype ι] :
    affineToContinuousMap
      (ConvexSpace.AffineMap.id (StdSimplex ℝ ι)) = .id _ :=
  rfl

end AffineTopology

section SingularBasics

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C]

/-- The singular chain complex, exposed under the local excision namespace. -/
abbrev singularChains (X : TopCat.{w}) (R : C) : ChainComplex C ℕ :=
  ((singularChainComplexFunctor C).obj R).obj X

/-- The chain map induced by a continuous map. -/
abbrev singularChainMap {X Y : TopCat.{w}} (f : X ⟶ Y) (R : C) :
    singularChains X R ⟶ singularChains Y R :=
  ((singularChainComplexFunctor C).obj R).map f

/-- Inclusion of the summand indexed by a singular simplex. -/
def iotaSingularChain (X : TopCat.{w}) {R : C} {n : ℕ}
    (x : TopCat.toSSet.obj X _⦋n⦌) : R ⟶ (singularChains X R).X n :=
  Sigma.ι (fun _ ↦ R) x

lemma singularChains_hom_ext {X : TopCat.{w}} {R : C} {n : ℕ} {T : C}
    {f g : (singularChains X R).X n ⟶ T}
    (h : ∀ x, iotaSingularChain X x ≫ f = iotaSingularChain X x ≫ g) :
    f = g :=
  Sigma.hom_ext _ _ h

@[reassoc (attr := simp)]
lemma iotaSingularChain_d (X : TopCat.{w}) {R : C} {n : ℕ}
    (x : TopCat.toSSet.obj X _⦋n + 1⦌) :
    iotaSingularChain X (R := R) x ≫ (singularChains X R).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        iotaSingularChain X ((TopCat.toSSet.obj X).δ i x) := by
  simp [singularChains, iotaSingularChain, singularChainComplexFunctor,
    SSet.chainComplexFunctor, Preadditive.comp_sum]
  rfl

@[reassoc (attr := simp)]
lemma iota_singularChainMap {X Y : TopCat.{w}} (f : X ⟶ Y)
    {R : C} {n : ℕ} (x : TopCat.toSSet.obj X _⦋n⦌) :
    iotaSingularChain X (R := R) x ≫ (singularChainMap f R).f n =
      iotaSingularChain Y ((TopCat.toSSet.map f).app _ x) := by
  simp [singularChains, singularChainMap, iotaSingularChain,
    singularChainComplexFunctor, SSet.chainComplexFunctor]

/-- The universal singular `n`-simplex. -/
def universalSingularSimplex (n : ℕ) :
    TopCat.toSSet.{w}.obj (SimplexCategory.toTop ^⦋n⦌) _⦋n⦌ :=
  ⟨𝟙 _⟩

lemma singularSimplex_from_universal {X : TopCat.{w}} {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) :
    ∃ f : SimplexCategory.toTop ^⦋n⦌ ⟶ X,
      (TopCat.toSSet.map f).app _ (universalSingularSimplex n) = s := by
  obtain ⟨s, rfl⟩ := (TopCat.toSSetObjEquiv _ _).symm.surjective s
  exact ⟨TopCat.ofHom (s.comp ⟨ULift.down, by fun_prop⟩), rfl⟩

section NatTrans

variable {R : C} {n : ℕ} {F : TopCat.{w} ⥤ C}

/-- Construct a natural transformation out of degree-`n` singular chains from
its value on the universal singular simplex. -/
def singularChainNatTransMk
    (f : R ⟶ F.obj (SimplexCategory.toTop.{w} ^⦋n⦌)) :
    (singularChainComplexFunctor C).obj R ⋙ eval _ _ n ⟶ F where
  app X := Sigma.desc (fun s ↦ f ≫ F.map s.down)
  naturality {X Y} g := Sigma.hom_ext _ _ (fun s ↦ by
    simp [singularChainComplexFunctor, SSet.chainComplexFunctor,
      ← Functor.map_comp]
    rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma iota_singularChainNatTransMk
    (f : R ⟶ F.obj (SimplexCategory.toTop.{w} ^⦋n⦌))
    (X : TopCat.{w}) (s : TopCat.toSSet.obj X _⦋n⦌) :
    iotaSingularChain X s ≫ (singularChainNatTransMk f).app X =
      f ≫ F.map s.down :=
  Sigma.ι_comp_desc ..

@[simp]
lemma singularChainNatTransMk_zero :
    singularChainNatTransMk (C := C) (R := R) (F := F) (n := n) 0 = 0 := by
  ext X
  apply Sigma.hom_ext
  intro s
  change iotaSingularChain X (R := R) s ≫
      (singularChainNatTransMk (C := C) (R := R) (F := F) (n := n) 0).app X =
    iotaSingularChain X s ≫ (0 :
      ((singularChainComplexFunctor C).obj R ⋙ eval _ _ n ⟶ F)).app X
  rw [iota_singularChainNatTransMk]
  simp

end NatTrans

end SingularBasics

section UniversalAffineChains

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C]

local instance : HasCoproducts.{0} C := hasCoproducts_shrink

/-- The singular simplex of the universe-`w` topological standard simplex
obtained by lifting an affine simplex. -/
def universalSingularOfAffine (n m : ℕ)
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (m + 1)))
      (StdSimplex ℝ (Fin (n + 1)))) :
    TopCat.toSSet.obj (SimplexCategory.toTop.{w} ^⦋n⦌) _⦋m⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm
    ⟨fun x ↦ ULift.up (s x), continuous_uliftUp.comp
      (continuous_stdSimplexAffineMap s)⟩

@[simp]
lemma universalSingularOfAffine_id (n : ℕ) :
    universalSingularOfAffine.{w} n n
      (ConvexSpace.AffineMap.id _) = universalSingularSimplex n := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext x
  rfl

lemma universalSingularOfAffine_face (n m : ℕ)
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (m + 2)))
      (StdSimplex ℝ (Fin (n + 1)))) (i : Fin (m + 2)) :
    universalSingularOfAffine.{w} n m (affineFace s i) =
      (TopCat.toSSet.obj (SimplexCategory.toTop.{w} ^⦋n⦌)).δ i
        (universalSingularOfAffine.{w} n (m + 1) s) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext x
  rfl

/-- The degreewise map from affine chains on the standard `n`-simplex to
singular chains on its universe lift. -/
def affineToUniversalSingularDegreeMap (R : C) (n m : ℕ) :
    ((affineSimplexSSet (StdSimplex ℝ (Fin (n + 1)))).chainComplex R).X m ⟶
      (singularChains (SimplexCategory.toTop.{w} ^⦋n⦌) R).X m :=
  Sigma.map'
    (f := fun (_ : TopCat.toSSet.obj
      (SimplexCategory.toTop.{w} ^⦋n⦌) _⦋m⦌) ↦ R)
    (g := fun (_ : affineSimplexSSet
      (StdSimplex ℝ (Fin (n + 1))) _⦋m⦌) ↦ R)
    (universalSingularOfAffine.{w} n m) (fun _ ↦ 𝟙 R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma iota_affineToUniversalSingularDegreeMap (R : C) (n m : ℕ)
    (s : affineSimplexSSet (StdSimplex ℝ (Fin (n + 1))) _⦋m⦌) :
    SSet.ιChainComplex _ s ≫
        affineToUniversalSingularDegreeMap.{w} R n m =
      iotaSingularChain (SimplexCategory.toTop.{w} ^⦋n⦌)
        (universalSingularOfAffine.{w} n m s) := by
  dsimp [affineToUniversalSingularDegreeMap, iotaSingularChain,
    SSet.ιChainComplex]
  erw [Sigma.ι_comp_map']
  simp

/-- The chain map from affine chains on the standard `n`-simplex to singular
chains on its universe lift. -/
def affineToUniversalSingularChainMap (R : C) (n : ℕ) :
    (affineSimplexSSet (StdSimplex ℝ (Fin (n + 1)))).chainComplex R ⟶
      singularChains (SimplexCategory.toTop.{w} ^⦋n⦌) R :=
  ChainComplex.ofHom
    (affineToUniversalSingularDegreeMap.{w} R n)
    (fun m ↦ by
      apply SSet.chainComplex_hom_ext
      intro s
      simp only [iota_affineToUniversalSingularDegreeMap_assoc,
        iotaSingularChain_d, SSet.ιChainComplex_d_assoc,
        Preadditive.sum_comp, Linear.smul_comp,
        iota_affineToUniversalSingularDegreeMap]
      apply Finset.sum_congr rfl
      intro i hi
      congr 2)

@[reassoc (attr := simp)]
lemma iota_affineToUniversalSingularChainMap (R : C) (n m : ℕ)
    (s : affineSimplexSSet (StdSimplex ℝ (Fin (n + 1))) _⦋m⦌) :
    SSet.ιChainComplex _ s ≫
        (affineToUniversalSingularChainMap.{w} R n).f m =
      iotaSingularChain (SimplexCategory.toTop.{w} ^⦋n⦌)
        (universalSingularOfAffine.{w} n m s) :=
  iota_affineToUniversalSingularDegreeMap R n m s

end UniversalAffineChains

section SingularSubdivisionHomotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C]

local instance : HasCoproducts.{0} C := hasCoproducts_shrink

/-- The natural degree-raising operator on singular chains obtained by
transporting the affine subdivision homotopy on the universal simplex. -/
def singularSubdivisionHomotopyNat (R : C) (n : ℕ) :
    (singularChainComplexFunctor C).obj R ⋙ eval _ _ n ⟶
      (singularChainComplexFunctor C).obj R ⋙ eval _ _ (n + 1) :=
  singularChainNatTransMk
    (SSet.ιChainComplex
        (affineSimplexSSet.{0} (StdSimplex ℝ (Fin (n + 1))))
        (ConvexSpace.AffineMap.id (StdSimplex ℝ (Fin (n + 1)))) ≫
      (affineChainHomotopyIdSubdivision
        (StdSimplex ℝ (Fin (n + 1))) R).hom n (n + 1) ≫
      (affineToUniversalSingularChainMap.{w} R n).f (n + 1))

/-- The subdivision homotopy component, extended by zero away from adjacent
degrees. -/
def singularSubdivisionHomotopyComponent (R : C) (n m : ℕ) :
    (singularChainComplexFunctor C).obj R ⋙ eval _ _ n ⟶
      (singularChainComplexFunctor C).obj R ⋙ eval _ _ m :=
  if h : n + 1 = m then
    singularSubdivisionHomotopyNat R n ≫ eqToHom (by simp [h])
  else 0

@[simp]
lemma singularSubdivisionHomotopyComponent_eq (R : C) (n : ℕ) :
    singularSubdivisionHomotopyComponent R n (n + 1) =
      singularSubdivisionHomotopyNat R n := by
  simp [singularSubdivisionHomotopyComponent]

lemma singularSubdivisionHomotopyComponent_eq_zero
    (R : C) (n m : ℕ) (h : n + 1 ≠ m) :
    singularSubdivisionHomotopyComponent R n m = 0 := by
  grind [singularSubdivisionHomotopyComponent]

@[simp]
lemma singularSubdivisionHomotopyNat_zero (R : C) :
    singularSubdivisionHomotopyNat.{w} R 0 = 0 := by
  ext X
  apply Sigma.hom_ext
  intro s
  simp [singularSubdivisionHomotopyNat,
    affineChainHomotopyIdSubdivision_hom_eq,
    affineSubdivisionHomotopyComponent_eq]

set_option backward.isDefEq.respectTransparency false in
/-- The natural barycentric-subdivision endomorphism of singular chains. -/
def singularChainSubdivisionNat (R : C) :
    (singularChainComplexFunctor C).obj R ⟶
      (singularChainComplexFunctor C).obj R where
  app X := 𝟙 _ - Homotopy.nullHomotopicMap
    (fun n m ↦ (singularSubdivisionHomotopyComponent R n m).app X)
  naturality {X Y} f := by
    simp only [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp,
      Category.id_comp, sub_right_inj]
    rw [Homotopy.nullHomotopicMap_comp, Homotopy.comp_nullHomotopicMap]
    congr
    ext n m
    exact (singularSubdivisionHomotopyComponent R n m).naturality f

/-- Barycentric subdivision as an endomorphism of the singular chain complex
of `X`. -/
abbrev singularChainSubdivision (X : TopCat.{w}) (R : C) :
    singularChains X R ⟶ singularChains X R :=
  (singularChainSubdivisionNat R).app X

@[reassoc]
lemma singularChainSubdivision_naturality
    {X Y : TopCat.{w}} (f : X ⟶ Y) (R : C) :
    singularChainSubdivision X R ≫ singularChainMap f R =
      singularChainMap f R ≫ singularChainSubdivision Y R :=
  ((singularChainSubdivisionNat R).naturality f).symm

@[reassoc]
lemma iota_singularChainSubdivision_naturality
    {X Y : TopCat.{w}} (f : X ⟶ Y) (R : C) {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) :
    iotaSingularChain Y (R := R) ((TopCat.toSSet.map f).app _ s) ≫
        (singularChainSubdivision Y R).f n =
      iotaSingularChain X s ≫ (singularChainSubdivision X R).f n ≫
        (singularChainMap f R).f n := by
  rw [← HomologicalComplex.comp_f,
    ← (singularChainSubdivisionNat R).naturality f,
    HomologicalComplex.comp_f, ← iota_singularChainMap_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical one-step homotopy from the identity to singular
subdivision. -/
def singularChainHomotopyIdSubdivision (X : TopCat.{w}) (R : C) :
    Homotopy (𝟙 (singularChains X R)) (singularChainSubdivision X R) :=
  Homotopy.equivSubZero.symm
    (.trans (.ofEq (by simp [singularChainSubdivision,
      singularChainSubdivisionNat]))
      (Homotopy.nullHomotopy
        (fun n m ↦ (singularSubdivisionHomotopyComponent R n m).app X)
        (fun n m h ↦ by
          simp [singularSubdivisionHomotopyComponent_eq_zero _ _ _ h])))

private lemma singularChainHomotopyIdSubdivision_hom_eq
    (X : TopCat.{w}) (R : C) (n m : ℕ) :
    (singularChainHomotopyIdSubdivision X R).hom n m =
      (singularSubdivisionHomotopyComponent R n m).app X := by
  dsimp [singularChainHomotopyIdSubdivision, Homotopy.equivSubZero]
  simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Pi.zero_apply, zero_add]
  apply Homotopy.nullHomotopy_hom

@[reassoc]
lemma singularChainHomotopyIdSubdivision_naturality
    {X Y : TopCat.{w}} (f : X ⟶ Y) (R : C) (n m : ℕ) :
    (singularChainMap f R).f n ≫
        (singularChainHomotopyIdSubdivision Y R).hom n m =
      (singularChainHomotopyIdSubdivision X R).hom n m ≫
        (singularChainMap f R).f m := by
  simp only [singularChainHomotopyIdSubdivision_hom_eq]
  exact (singularSubdivisionHomotopyComponent R n m).naturality f

@[reassoc]
lemma iota_singularChainHomotopyIdSubdivision_naturality
    {X Y : TopCat.{w}} (f : X ⟶ Y) (R : C) {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) (m : ℕ) :
    iotaSingularChain Y ((TopCat.toSSet.map f).app _ s) ≫
        (singularChainHomotopyIdSubdivision Y R).hom n m =
      iotaSingularChain X s ≫
        (singularChainHomotopyIdSubdivision X R).hom n m ≫
          (singularChainMap f R).f m := by
  simpa using iotaSingularChain X (R := R) s ≫=
    singularChainHomotopyIdSubdivision_naturality f R n m

end SingularSubdivisionHomotopy

section SingularSimplices

variable {X Y : TopCat.{w}}

lemma singularFace_toSSetObjEquiv_symm {n : ℕ}
    (s : C(StdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ i ((TopCat.toSSetObjEquiv _ _).symm s) =
      (TopCat.toSSetObjEquiv _ _).symm
        (s.comp (affineToContinuousMap
          (StdSimplex.affineMap (R := ℝ) i.succAbove))) :=
  rfl

lemma affineMap_comp_affineSubdivision {n : ℕ} {Z₁ Z₂ : Type*}
    [ConvexSpace ℝ Z₁] [ConvexSpace ℝ Z₂]
    (g : ConvexSpace.AffineMap ℝ Z₁ Z₂)
    (f : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) Z₁)
    (σ : Equiv.Perm (Fin (n + 1))) :
    g.comp (affineSubdivision f σ) = affineSubdivision (g.comp f) σ := by
  rw [affineSubdivision, StdSimplex.comp_affineMapMk]
  rfl

lemma affineMap_comp_affineSubdivisionIter
    {n k : ℕ} {Z₁ Z₂ : Type*}
    [ConvexSpace ℝ Z₁] [ConvexSpace ℝ Z₂]
    (g : ConvexSpace.AffineMap ℝ Z₁ Z₂)
    (f : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) Z₁)
    (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    g.comp (affineSubdivisionIter f σ) =
      affineSubdivisionIter (g.comp f) σ := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [affineSubdivisionIter_succ, affineSubdivisionIter_succ,
      affineMap_comp_affineSubdivision, ih]

lemma affineSubdivision_eq_comp_id {n : ℕ} {Z : Type*}
    [ConvexSpace ℝ Z]
    (f : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) Z)
    (σ : Equiv.Perm (Fin (n + 1))) :
    affineSubdivision f σ =
      f.comp (affineSubdivision (ConvexSpace.AffineMap.id _) σ) := by
  rw [affineMap_comp_affineSubdivision]
  rfl

lemma affineSubdivisionIter_eq_comp_id {n k : ℕ} {Z : Type*}
    [ConvexSpace ℝ Z]
    (f : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) Z)
    (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    affineSubdivisionIter f σ =
      f.comp (affineSubdivisionIter (ConvexSpace.AffineMap.id _) σ) := by
  rw [affineMap_comp_affineSubdivisionIter]
  rfl

/-- The singular subsimplex selected by a permutation. -/
def singularSubdivision {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌)
    (σ : Equiv.Perm (Fin (n + 1))) :
    TopCat.toSSet.obj X _⦋n⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm
    ((TopCat.toSSetObjEquiv _ _ s).comp
      (affineToContinuousMap
        (affineSubdivision
          (ConvexSpace.AffineMap.id (StdSimplex ℝ (Fin (n + 1)))) σ)))

lemma singularSubdivision_toSSetObjEquiv_symm {n : ℕ}
    (s : C(StdSimplex ℝ (Fin (n + 1)), X))
    (σ : Equiv.Perm (Fin (n + 1))) :
    singularSubdivision ((TopCat.toSSetObjEquiv _ (op ⦋n⦌)).symm s) σ =
      (TopCat.toSSetObjEquiv _ (op ⦋n⦌)).symm
        (s.comp (affineToContinuousMap
          (affineSubdivision
            (ConvexSpace.AffineMap.id (StdSimplex ℝ (Fin (n + 1)))) σ))) :=
  rfl

@[simp]
lemma singularSubdivision_zero
    (s : TopCat.toSSet.obj X _⦋0⦌) (σ : Equiv.Perm (Fin 1)) :
    singularSubdivision s σ = s := by
  obtain ⟨x, rfl⟩ := TopCat.toSSetObj₀Equiv.symm.surjective s
  apply (TopCat.toSSetObjEquiv _ _).injective
  simp [singularSubdivision, affineSubdivision_fin_one]

lemma singularSubdivision_range_subset {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌)
    (σ : Equiv.Perm (Fin (n + 1))) :
    Set.range (TopCat.toSSetObjEquiv _ _ (singularSubdivision s σ)) ⊆
      Set.range (TopCat.toSSetObjEquiv _ _ s) := by
  obtain ⟨s, rfl⟩ := (TopCat.toSSetObjEquiv _ _).symm.surjective s
  simp only [singularSubdivision_toSSetObjEquiv_symm, Equiv.apply_symm_apply,
    ContinuousMap.coe_comp]
  exact Set.range_comp_subset_range _ _

@[simp]
lemma singularSubdivision_naturality (f : X ⟶ Y) {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌)
    (σ : Equiv.Perm (Fin (n + 1))) :
    singularSubdivision ((TopCat.toSSet.map f).app _ s) σ =
      (TopCat.toSSet.map f).app _ (singularSubdivision s σ) := by
  obtain ⟨s, rfl⟩ := (TopCat.toSSetObjEquiv _ _).symm.surjective s
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext x
  rfl

/-- The singular subsimplex selected by a finite tail-first sequence of
permutations. -/
def singularSubdivisionIter {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) {k : ℕ}
    (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    TopCat.toSSet.obj X _⦋n⦌ :=
  Nat.rec (motive := fun k ↦
      (Fin k → Equiv.Perm (Fin (n + 1))) → TopCat.toSSet.obj X _⦋n⦌)
    (fun _ ↦ s)
    (fun _k ih σ ↦ singularSubdivision (ih (σ ∘ Fin.succ)) (σ 0))
    k σ

@[simp]
lemma singularSubdivisionIter_zero {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌)
    (σ : Fin 0 → Equiv.Perm (Fin (n + 1))) :
    singularSubdivisionIter s σ = s :=
  rfl

lemma singularSubdivisionIter_succ {n k : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌)
    (σ : Fin (k + 1) → Equiv.Perm (Fin (n + 1))) :
    singularSubdivisionIter s σ =
      singularSubdivision (singularSubdivisionIter s (σ ∘ Fin.succ)) (σ 0) :=
  rfl

@[simp]
lemma singularSubdivisionIter_one {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌)
    (σ : Fin 1 → Equiv.Perm (Fin (n + 1))) :
    singularSubdivisionIter s σ = singularSubdivision s (σ 0) :=
  rfl

lemma singularSubdivisionIter_toSSetObjEquiv_symm {n k : ℕ}
    (s : C(StdSimplex ℝ (Fin (n + 1)), X))
    (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    singularSubdivisionIter
        ((TopCat.toSSetObjEquiv _ (op ⦋n⦌)).symm s) σ =
      (TopCat.toSSetObjEquiv _ (op ⦋n⦌)).symm
        (s.comp (affineToContinuousMap
          (affineSubdivisionIter
            (ConvexSpace.AffineMap.id _) σ))) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    simp only [singularSubdivisionIter_succ, ih,
      singularSubdivision_toSSetObjEquiv_symm,
      affineSubdivisionIter_succ, ContinuousMap.comp_assoc,
      ← affineToContinuousMap_comp]
    congr 2
    exact congrArg (fun q ↦ affineToContinuousMap q)
      (affineSubdivision_eq_comp_id
        (f := affineSubdivisionIter
          (ConvexSpace.AffineMap.id (StdSimplex ℝ (Fin (n + 1))))
          (σ ∘ Fin.succ)) (σ := σ 0)).symm

lemma singularSubdivisionIter_range_subset {n k : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌)
    (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    Set.range (TopCat.toSSetObjEquiv _ _ (singularSubdivisionIter s σ)) ⊆
      Set.range (TopCat.toSSetObjEquiv _ _ s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [singularSubdivisionIter_succ]
    exact (singularSubdivision_range_subset _ _).trans (ih (σ ∘ Fin.succ))

@[simp]
lemma singularSubdivisionIter_naturality (f : X ⟶ Y) {n k : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌)
    (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    singularSubdivisionIter ((TopCat.toSSet.map f).app _ s) σ =
      (TopCat.toSSet.map f).app _ (singularSubdivisionIter s σ) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [singularSubdivisionIter_succ, ih]

/-- Every iterated subdivision of a face is itself a face of an iterated
subdivision of the original singular simplex. -/
lemma exists_singularSubdivisionIter_face
    {n : ℕ} (s : TopCat.toSSet.obj X _⦋n + 1⦌)
    (i : Fin (n + 2)) {k : ℕ}
    (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    ∃ (σ' : Fin k → Equiv.Perm (Fin (n + 2))) (i' : Fin (n + 2)),
      singularSubdivisionIter ((TopCat.toSSet.obj X).δ i s) σ =
        (TopCat.toSSet.obj X).δ i' (singularSubdivisionIter s σ') := by
  obtain ⟨s, rfl⟩ :=
    (TopCat.toSSetObjEquiv _ (op ⦋n + 1⦌)).symm.surjective s
  obtain ⟨σ', i', h⟩ := affineSubdivisionIter_face
    (K := ℝ) (ConvexSpace.AffineMap.id _) i σ
  refine ⟨σ', i', ?_⟩
  simp only [singularSubdivisionIter_toSSetObjEquiv_symm,
    singularFace_toSSetObjEquiv_symm, ContinuousMap.comp_assoc,
    ← affineToContinuousMap_comp]
  congr 2
  rw [← affineSubdivisionIter_eq_comp_id]
  exact congrArg (fun q ↦ affineToContinuousMap q)
    (by simpa [affineFace] using h)

end SingularSimplices

section SingularChainFormula

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C]

local instance : HasCoproducts.{0} C := hasCoproducts_shrink

@[simp]
lemma universalSingularSimplex_face (n : ℕ) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (SimplexCategory.toTop.{w} ^⦋n + 1⦌)).δ i
        (universalSingularSimplex.{w} (n + 1)) =
      (TopCat.toSSet.map
        (SimplexCategory.toTop.{w}.map (SimplexCategory.δ i))).app _
          (universalSingularSimplex.{w} n) :=
  rfl

@[simp]
lemma singularSubdivision_universal (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    singularSubdivision (universalSingularSimplex.{w} n) σ =
      universalSingularOfAffine.{w} n n
        (affineSubdivision (ConvexSpace.AffineMap.id _) σ) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext x
  rfl

@[reassoc]
lemma affineToUniversalSingularChainMap_face
    (R : C) (n m : ℕ) (i : Fin (n + 2)) :
    (SSet.chainComplexMap
        (affineMapToSSet (StdSimplex ℝ (Fin (n + 1)))
          (StdSimplex.affineMap (R := ℝ) (SimplexCategory.δ i))) R).f m ≫
        (affineToUniversalSingularChainMap.{w} R (n + 1)).f m =
      (affineToUniversalSingularChainMap.{w} R n).f m ≫
        (singularChainMap
          (SimplexCategory.toTop.{w}.map (SimplexCategory.δ i)) R).f m := by
  apply SSet.chainComplex_hom_ext
  intro s
  simp only [SSet.ι_chainComplexMap_f_assoc,
    iota_affineToUniversalSingularChainMap_assoc,
    iota_singularChainMap, iota_affineToUniversalSingularChainMap,
    affineMapToSSet_app]
  congr 1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma iota_universal_singularChainHomotopyIdSubdivision
    (R : C) (n : ℕ) :
    iotaSingularChain (SimplexCategory.toTop.{w} ^⦋n⦌) (R := R)
        (universalSingularSimplex.{w} n) ≫
      (singularChainHomotopyIdSubdivision
        (SimplexCategory.toTop.{w} ^⦋n⦌) R).hom n (n + 1) =
    SSet.ιChainComplex
        (affineSimplexSSet (StdSimplex ℝ (Fin (n + 1))))
        (ConvexSpace.AffineMap.id _) ≫
      (affineChainHomotopyIdSubdivision
        (StdSimplex ℝ (Fin (n + 1))) R).hom n (n + 1) ≫
      (affineToUniversalSingularChainMap.{w} R n).f (n + 1) := by
  simp [singularChainHomotopyIdSubdivision_hom_eq,
    singularSubdivisionHomotopyComponent_eq,
    singularSubdivisionHomotopyNat, universalSingularSimplex]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma iota_universal_face_singularChainHomotopyIdSubdivision
    (R : C) (n : ℕ) (i : Fin (n + 2)) :
    iotaSingularChain (SimplexCategory.toTop.{w} ^⦋n + 1⦌) (R := R)
        ((TopCat.toSSet.obj
          (SimplexCategory.toTop.{w} ^⦋n + 1⦌)).δ i
            (universalSingularSimplex.{w} (n + 1))) ≫
      (singularChainHomotopyIdSubdivision
        (SimplexCategory.toTop.{w} ^⦋n + 1⦌) R).hom n (n + 1) =
    SSet.ιChainComplex
        (affineSimplexSSet (StdSimplex ℝ (Fin (n + 2))))
        ((affineSimplexSSet (StdSimplex ℝ (Fin (n + 2)))).δ i
          (ConvexSpace.AffineMap.id _)) ≫
      (affineChainHomotopyIdSubdivision
        (StdSimplex ℝ (Fin (n + 2))) R).hom n (n + 1) ≫
      (affineToUniversalSingularChainMap.{w} R (n + 1)).f (n + 1) := by
  rw [universalSingularSimplex_face,
    iota_singularChainHomotopyIdSubdivision_naturality,
    iota_universal_singularChainHomotopyIdSubdivision_assoc,
    ← affineToUniversalSingularChainMap_face,
    ← affineChainHomotopyIdSubdivision_naturality_assoc]
  simp
  rw [show
    ((affineSimplexSSet (StdSimplex ℝ (Fin (n + 2)))).δ i
      (ConvexSpace.AffineMap.id _)) =
        StdSimplex.affineMap (R := ℝ) (SimplexCategory.δ i) by
      apply StdSimplex.affineMap_ext
      intro j
      rfl]

@[simp]
lemma singularChainSubdivision_f_zero (X : TopCat.{w}) (R : C) :
    (singularChainSubdivision X R).f 0 = 𝟙 _ := by
  simp [singularChainSubdivision, singularChainSubdivisionNat,
    ChainComplex.nullHomotopicMap_f_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma iota_universal_singularChainSubdivision_eq_sum
    (R : C) (n : ℕ) :
    iotaSingularChain (SimplexCategory.toTop.{w} ^⦋n⦌) (R := R)
        (universalSingularSimplex.{w} n) ≫
      (singularChainSubdivision
        (SimplexCategory.toTop.{w} ^⦋n⦌) R).f n =
    ∑ σ : Equiv.Perm (Fin (n + 1)), σ.sign •
      iotaSingularChain (SimplexCategory.toTop.{w} ^⦋n⦌)
        (singularSubdivision (universalSingularSimplex.{w} n) σ) := by
  obtain _ | n := n
  · simp
  · convert! iota_affineChainSubdivision_eq_sum
        (StdSimplex ℝ (Fin (n + 2))) R (n := n + 1)
        (s := ConvexSpace.AffineMap.id _) =≫
      (affineToUniversalSingularChainMap.{w} R (n + 1)).f (n + 1) using 1
    · have hs := congrArg (fun q ↦ q.f (n + 1))
          ((singularChainHomotopyIdSubdivision
            (SimplexCategory.toTop.{w} ^⦋n + 1⦌) R).eq_sub_nullHomotopicMap)
      have ha := congrArg (fun q ↦ q.f (n + 1))
          ((affineChainHomotopyIdSubdivision
            (StdSimplex ℝ (Fin (n + 2))) R).eq_sub_nullHomotopicMap)
      rw [hs, ha]
      dsimp
      simp only [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp,
        Category.assoc]
      congr 1
      · rw [iota_affineToUniversalSingularChainMap]
        simp
      · simp only [ChainComplex.nullHomotopicMap_f_succ,
          Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
          SSet.ιChainComplex_d_assoc, iotaSingularChain_d_assoc,
          Preadditive.sum_comp, Linear.smul_comp]
        congr 1
        · congr 1
          ext i
          congr 1
          exact iota_universal_face_singularChainHomotopyIdSubdivision
            R n i
        · erw [iota_universal_singularChainHomotopyIdSubdivision_assoc]
          simpa only [Category.assoc, Nat.add_assoc,
            SimplexCategory.toTop_obj] using
            ((SSet.ιChainComplex
                (affineSimplexSSet (StdSimplex ℝ (Fin (n + 2))))
                (ConvexSpace.AffineMap.id _) ≫
              (affineChainHomotopyIdSubdivision
                (StdSimplex ℝ (Fin (n + 2))) R).hom (n + 1) (n + 2)) ≫=
              ((affineToUniversalSingularChainMap.{w} R (n + 1)).comm
                (n + 2) (n + 1)))
    · simp only [Preadditive.sum_comp]
      congr 1
      ext σ
      simp only [Linear.units_smul_comp]
      congr 1
      rw [iota_affineToUniversalSingularChainMap]
      simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma iota_singularChainSubdivision_eq_sum
    (X : TopCat.{w}) (R : C) {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) :
    iotaSingularChain X (R := R) s ≫
        (singularChainSubdivision X R).f n =
      ∑ σ : Equiv.Perm (Fin (n + 1)), σ.sign •
        iotaSingularChain X (singularSubdivision s σ) := by
  obtain ⟨f, hf⟩ := singularSimplex_from_universal s
  rw [← hf, iota_singularChainSubdivision_naturality,
    iota_universal_singularChainSubdivision_eq_sum_assoc,
    Preadditive.sum_comp]
  congr 1
  ext σ
  simp [singularSubdivision_naturality]

end SingularChainFormula

section SingularChainIterates

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C]

/-- The `k`-fold iterate of the singular-chain subdivision operator. -/
def singularChainSubdivisionIter (X : TopCat.{w}) (R : C) (k : ℕ) :
    singularChains X R ⟶ singularChains X R :=
  let x : End (singularChains X R) := singularChainSubdivision X R
  x ^ k

@[simp]
lemma singularChainSubdivisionIter_zero (X : TopCat.{w}) (R : C) :
    singularChainSubdivisionIter X R 0 = 𝟙 _ := by
  simp [singularChainSubdivisionIter]

@[simp]
lemma singularChainSubdivisionIter_one (X : TopCat.{w}) (R : C) :
    singularChainSubdivisionIter X R 1 = singularChainSubdivision X R := by
  simp [singularChainSubdivisionIter]

@[reassoc]
lemma singularChainSubdivisionIter_add (X : TopCat.{w}) (R : C)
    (k l : ℕ) :
    singularChainSubdivisionIter X R (k + l) =
      singularChainSubdivisionIter X R k ≫
        singularChainSubdivisionIter X R l := by
  simp [add_comm k l, singularChainSubdivisionIter, pow_add]

@[reassoc]
lemma singularChainSubdivisionIter_succ (X : TopCat.{w}) (R : C)
    (k : ℕ) :
    singularChainSubdivisionIter X R (k + 1) =
      singularChainSubdivisionIter X R k ≫
        singularChainSubdivision X R := by
  simp [singularChainSubdivisionIter_add]

@[reassoc]
lemma singularChainSubdivisionIter_naturality
    {X Y : TopCat.{w}} (f : X ⟶ Y) (R : C) (k : ℕ) :
    singularChainSubdivisionIter X R k ≫ singularChainMap f R =
      singularChainMap f R ≫ singularChainSubdivisionIter Y R k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [singularChainSubdivisionIter_succ,
      singularChainSubdivisionIter_succ, Category.assoc,
      singularChainSubdivision_naturality, ← Category.assoc, ih,
      Category.assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma iota_singularChainSubdivisionIter_eq_sum
    (X : TopCat.{w}) (R : C) {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) (k : ℕ) :
    iotaSingularChain X (R := R) s ≫
        (singularChainSubdivisionIter X R k).f n =
      ∑ σ : Fin k → Equiv.Perm (Fin (n + 1)),
        (∏ i, (σ i).sign) •
          iotaSingularChain X (singularSubdivisionIter s σ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    let e : (Fin (k + 1) → Equiv.Perm (Fin (n + 1))) ≃
        (Fin k → Equiv.Perm (Fin (n + 1))) ×
          Equiv.Perm (Fin (n + 1)) :=
      { toFun σ := ⟨σ ∘ Fin.succ, σ 0⟩
        invFun := fun ⟨σ, σ'⟩ ↦ Fin.cases σ' σ
        left_inv σ := by
          ext l : 1
          obtain rfl | ⟨l, rfl⟩ := l.eq_zero_or_eq_succ <;> rfl }
    simp only [singularChainSubdivisionIter_succ,
      HomologicalComplex.comp_f, reassoc_of% ih, Preadditive.sum_comp,
      Linear.units_smul_comp, iota_singularChainSubdivision_eq_sum,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_bijective
      (g := fun ⟨σ, σ₀⟩ ↦
        ((∏ i, Equiv.Perm.sign (σ i)) * Equiv.Perm.sign σ₀) •
          iotaSingularChain X
            (singularSubdivision (singularSubdivisionIter s σ) σ₀))
      (t := .univ) _ e.bijective (by simp) ?_,
      Finset.sum_finset_product .univ .univ (fun _ ↦ .univ) (by simp)]
    simp only [Finset.mem_univ, forall_const]
    intro σ
    congr
    · rw [mul_comm]
      simp [e, Fin.prod_univ_succ]

@[simp]
lemma singularChainSubdivisionIter_f_zero
    (X : TopCat.{w}) (R : C) (k : ℕ) :
    (singularChainSubdivisionIter X R k).f 0 = 𝟙 _ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [singularChainSubdivisionIter_succ, HomologicalComplex.comp_f,
      ih, singularChainSubdivision_f_zero, Category.comp_id]

/-- The homotopy from the identity to every finite iterate of the canonical
singular-chain subdivision map. -/
def singularChainHomotopyIdSubdivisionIter
    (X : TopCat.{w}) (R : C) (k : ℕ) :
    Homotopy (𝟙 (singularChains X R))
      (singularChainSubdivisionIter X R k) :=
  Nat.rec (motive := fun k ↦ Homotopy (𝟙 (singularChains X R))
      (singularChainSubdivisionIter X R k))
    (.ofEq (by simp))
    (fun k hk ↦ hk.trans
      ((Homotopy.ofEq (by simp)).trans
        (((Homotopy.refl (singularChainSubdivisionIter X R k)).comp
          (singularChainHomotopyIdSubdivision X R)).trans
            (.ofEq ((singularChainSubdivisionIter_succ X R k).symm))))
      )
    k

lemma singularChainHomotopyIdSubdivisionIter_succ
    (X : TopCat.{w}) (R : C) (k : ℕ) :
    singularChainHomotopyIdSubdivisionIter X R (k + 1) =
      (singularChainHomotopyIdSubdivisionIter X R k).trans
        ((Homotopy.ofEq (by simp)).trans
          (((Homotopy.refl (singularChainSubdivisionIter X R k)).comp
            (singularChainHomotopyIdSubdivision X R)).trans
              (.ofEq ((singularChainSubdivisionIter_succ X R k).symm)))) :=
  rfl

lemma singularChainHomotopyIdSubdivisionIter_hom
    (X : TopCat.{w}) (R : C) (k n m : ℕ) :
    (singularChainHomotopyIdSubdivisionIter X R k).hom n m =
      ∑ i : Fin k,
        (singularChainSubdivisionIter X R i.val).f n ≫
          (singularChainHomotopyIdSubdivision X R).hom n m := by
  induction k with
  | zero => simp [singularChainHomotopyIdSubdivisionIter]
  | succ k ih =>
    rw [singularChainHomotopyIdSubdivisionIter_succ,
      Homotopy.trans_hom, ih]
    simp [Fin.sum_univ_castSucc]

end SingularChainIterates

end Hatcher.Excision
