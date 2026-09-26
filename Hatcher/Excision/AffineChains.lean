/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Joël Riou, Jack McCarthy

This file adapts the affine-chain construction from `joelriou/excision` at
commit `8b56cd0c8e5f39a7c2f36418c80b298e469596a6` to the Mathlib version pinned
by this project.
-/

import Hatcher.Excision.AffineSubdivision
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.GroupTheory.Perm.Sign

/-!
# Affine chains and barycentric subdivision

For a convex real space, this file constructs the simplicial set of affine
simplices, its cone operator, barycentric subdivision on affine chains, and a
natural chain homotopy from the identity to subdivision.
-/

noncomputable section

open CategoryTheory Limits Simplicial Convexity

namespace Hatcher.Excision

universe w v u

variable (Y : Type w) [ConvexSpace ℝ Y]
  {Z : Type w} [ConvexSpace ℝ Z]

private lemma simplexCategory_delta_apply {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    SimplexCategory.δ i j = Fin.succAbove i j := rfl

private lemma simplexCategory_sigma_apply {n : ℕ}
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    SimplexCategory.σ i j = Fin.predAbove i j := rfl

/-- The cone of an affine simplex with a specified initial vertex. -/
def affineCone {n : ℕ}
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin n)) Y) (y : Y) :
    ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) Y :=
  StdSimplex.affineMapMk (Fin.cases y (fun i ↦ s (.single i)))

lemma affineCone_def {n : ℕ}
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin n)) Y) (y : Y) :
    affineCone Y s y =
      StdSimplex.affineMapMk (Fin.cases y (fun i ↦ s (.single i))) :=
  rfl

@[simp]
lemma affineCone_single_zero {n : ℕ}
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin n)) Y) (y : Y) :
    affineCone Y s y (.single 0) = y := by
  simp [affineCone_def]

@[simp]
lemma affineCone_single_succ {n : ℕ}
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin n)) Y) (y : Y)
    (j : Fin n) :
    affineCone Y s y (.single j.succ) = s (.single j) := by
  simp [affineCone_def]

lemma affineCone_naturality {n : ℕ}
    (φ : ConvexSpace.AffineMap ℝ Y Z)
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) Y) (y : Y) :
    affineCone Z (φ.comp s) (φ y) = φ.comp (affineCone Y s y) := by
  apply StdSimplex.affineMap_ext
  intro i
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ <;> simp

/-- The simplicial set whose simplices are affine maps from standard
simplices to `Y`. -/
noncomputable abbrev affineSimplexSSet : SSet.{w} where
  obj n := ConvexSpace.AffineMap ℝ
    (StdSimplex ℝ (Fin (n.unop.len + 1))) Y
  map f := ↾fun g ↦ g.comp (StdSimplex.affineMap f.unop)
  map_comp _ _ := by
    ext
    dsimp
    rw [← StdSimplex.map_comp]
    rfl

/-- An affine map induces a map of affine-simplex simplicial sets. -/
@[simps]
def affineMapToSSet (φ : ConvexSpace.AffineMap ℝ Y Z) :
    affineSimplexSSet Y ⟶ affineSimplexSSet Z where
  app _ := ↾fun g ↦ φ.comp g

attribute [local simp] SimplicialObject.δ_def simplexCategory_delta_apply

lemma affineSimplex_delta_zero (y : Y) {n : ℕ}
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) Y) :
    (affineSimplexSSet Y).δ 0 (affineCone Y s y) = s := by
  apply StdSimplex.affineMap_ext
  intro i
  simp [SimplicialObject.δ_def, simplexCategory_delta_apply,
    affineCone_def, StdSimplex.affineMapMk_apply]

lemma affineSimplex_delta_affineMapMk {n : ℕ} (s : Fin (n + 2) → Y)
    (i : Fin (n + 2)) :
    (affineSimplexSSet Y).δ i (StdSimplex.affineMapMk s) =
      StdSimplex.affineMapMk (s ∘ i.succAbove) := by
  aesop

/-- The affine-simplex simplicial set, augmented to a point. -/
noncomputable abbrev affineSimplexAugmented : SSet.Augmented where
  left := affineSimplexSSet Y
  right := PUnit
  hom.app _ := ↾fun _ ↦ .unit

attribute [local simp] SimplicialObject.δ_def simplexCategory_delta_apply
  SimplicialObject.σ_def simplexCategory_sigma_apply affineCone_def
  StdSimplex.affineMapMk_apply in
/-- Coning at `y` is an extra degeneracy of the augmented affine-simplex
simplicial set. -/
def affineSimplexExtraDegeneracy (y : Y) :
    (affineSimplexAugmented Y).ExtraDegeneracy where
  s' := ↾fun _ ↦ .const y
  s n := ↾fun f ↦ affineCone Y f y
  s₀_comp_δ₁ := by ext _ i; fin_cases i; simp
  s_comp_δ _ _ := by
    ext _ j
    obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;> simp
  s_comp_σ _ _ := by
    ext _ j
    obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;> simp

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C]

/-- The chain cone which sends `[y₀, ..., yₙ]` to `[y, y₀, ..., yₙ]`. -/
def affineChainCone (y : Y) (R : C) (n : ℕ) :
    ((affineSimplexSSet Y).chainComplex R).X n ⟶
      ((affineSimplexSSet Y).chainComplex R).X (n + 1) :=
  ((affineSimplexExtraDegeneracy Y y).map (sigmaConst.obj R)).s n

@[simp]
lemma affineChain_d_comp_cone_add_cone_comp_d (y : Y) (R : C) {n : ℕ} :
    ((affineSimplexSSet Y).chainComplex R).d (n + 1) n ≫
        affineChainCone Y y R n +
      affineChainCone Y y R (n + 1) ≫
        ((affineSimplexSSet Y).chainComplex R).d (n + 2) (n + 1) = 𝟙 _ := by
  have := Preadditive.hasZeroObject_of_hasCoproduct C
  have h := (((affineSimplexExtraDegeneracy Y y).map
    (sigmaConst.obj R)).homotopyEquiv.homotopyHomInvId.symm.comm (n + 1)).symm
  rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex] at h
  simpa [-AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv] using! h

lemma affineChain_d_comp_cone_eq_sub (y : Y) (R : C) {n : ℕ} :
    ((affineSimplexSSet Y).chainComplex R).d (n + 1) n ≫
      affineChainCone Y y R n =
    𝟙 _ - affineChainCone Y y R (n + 1) ≫
      ((affineSimplexSSet Y).chainComplex R).d (n + 2) (n + 1) := by
  rw [← affineChain_d_comp_cone_add_cone_comp_d]
  abel

lemma affineChain_cone_comp_d_eq_sub (y : Y) (R : C) {n : ℕ} :
    affineChainCone Y y R (n + 1) ≫
        ((affineSimplexSSet Y).chainComplex R).d (n + 2) (n + 1) =
      𝟙 _ - ((affineSimplexSSet Y).chainComplex R).d (n + 1) n ≫
        affineChainCone Y y R n := by
  rw [← affineChain_d_comp_cone_add_cone_comp_d]
  abel

@[reassoc (attr := simp)]
lemma iota_affineChainCone (y : Y) (R : C) {n : ℕ}
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) Y) :
    SSet.ιChainComplex _ s ≫ affineChainCone Y y R n =
      SSet.ιChainComplex _ (affineCone Y s y) := by
  simp [affineChainCone, affineSimplexExtraDegeneracy,
    SimplicialObject.Augmented.ExtraDegeneracy.map, SSet.ιChainComplex]

@[reassoc]
lemma affineChainCone_naturality
    (φ : ConvexSpace.AffineMap ℝ Y Z) (y : Y) (R : C) (n : ℕ) :
    (SSet.chainComplexMap (affineMapToSSet Y φ) R).f n ≫
        affineChainCone Z (φ y) R n =
      affineChainCone Y y R n ≫
        (SSet.chainComplexMap (affineMapToSSet Y φ) R).f (n + 1) := by
  ext x
  simp [affineCone_naturality]

/-- The image of the barycenter of the standard simplex under an affine
simplex. -/
def affineBarycenter {M : Type*} [Nonempty M] [Fintype M]
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ M) Y) : Y :=
  s (StdSimplex.barycenter (K := ℝ) (M := M))

@[simp]
lemma affineBarycenter_comp {M : Type*} [Nonempty M] [Fintype M]
    (φ : ConvexSpace.AffineMap ℝ Y Z)
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ M) Y) :
    affineBarycenter Z (φ.comp s) = φ (affineBarycenter Y s) :=
  rfl

/-- Compatibility of face barycenters with an affine simplex presented by its
vertices. This is the form needed by the signed subdivision formula. -/
lemma affineSubBarycenter_mk_comp_of_injective
    {M N : Type*} [DecidableEq N] (f : N → Y)
    (S : Finset M) (hS : S.Nonempty) (g : M → N)
    (hg : Function.Injective g) :
    affineSubBarycenter (K := ℝ) (Y := Y)
        (StdSimplex.affineMapMk (R := ℝ) (f ∘ g)) S hS =
      affineSubBarycenter (K := ℝ) (Y := Y)
        (StdSimplex.affineMapMk (R := ℝ) f) (Finset.image g S)
          (by simpa) := by
  rw [← affineSubBarycenter_comp_of_injective _ _ hS _ hg]
  congr
  aesop

/-- Recursive cone data underlying the chain homotopy from the identity to
barycentric subdivision.  Writing the primitive recursion explicitly keeps
the kernel definition noncomputable without asking the equation compiler for
an unsafe executable implementation. -/
noncomputable def affineSubdivisionHomotopyAux (R : C) (n : ℕ) :
    ((affineSimplexSSet Y).chainComplex R).X n ⟶
      ((affineSimplexSSet Y).chainComplex R).X (n + 1) :=
  Nat.rec (motive := fun n ↦
      ((affineSimplexSSet Y).chainComplex R).X n ⟶
        ((affineSimplexSSet Y).chainComplex R).X (n + 1))
    0
    (fun n h ↦
      Sigma.desc (fun s ↦
        (SSet.ιChainComplex _ s - SSet.ιChainComplex _ s ≫
          ((affineSimplexSSet Y).chainComplex R).d (n + 1) n ≫ h) ≫
          affineChainCone Y (affineBarycenter Y s) R (n + 1)))
    n

@[simp]
lemma affineSubdivisionHomotopyAux_zero (R : C) :
    affineSubdivisionHomotopyAux Y R 0 = 0 :=
  rfl

@[reassoc (attr := simp)]
lemma iota_affineSubdivisionHomotopyAux_succ (R : C) {n : ℕ}
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 2))) Y) :
    SSet.ιChainComplex _ s ≫ affineSubdivisionHomotopyAux Y R (n + 1) =
      (SSet.ιChainComplex (affineSimplexSSet Y) s -
        SSet.ιChainComplex _ s ≫
          ((affineSimplexSSet Y).chainComplex R).d (n + 1) n ≫
            affineSubdivisionHomotopyAux Y R n) ≫
        affineChainCone Y (affineBarycenter Y s) R (n + 1) :=
  Sigma.ι_comp_desc ..

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma affineSubdivisionHomotopyAux_naturality
    (φ : ConvexSpace.AffineMap ℝ Y Z) (R : C) (n : ℕ) :
    (SSet.chainComplexMap (affineMapToSSet Y φ) R).f n ≫
        affineSubdivisionHomotopyAux Z R n =
      affineSubdivisionHomotopyAux Y R n ≫
        (SSet.chainComplexMap (affineMapToSSet Y φ) R).f (n + 1) := by
  induction n with
  | zero => simp
  | succ n hn =>
    ext x
    simp only [iota_affineSubdivisionHomotopyAux_succ_assoc,
      ← affineChainCone_naturality, Preadditive.sub_comp, Category.assoc,
      ← reassoc_of% hn, SSet.ι_chainComplexMap_f_assoc,
      iota_affineSubdivisionHomotopyAux_succ, affineMapToSSet_app,
      ← (SSet.chainComplexMap (affineMapToSSet Y φ) R).comm_assoc]
    rfl

/-- The homotopy component with arbitrary source and target degrees. -/
def affineSubdivisionHomotopyComponent (R : C) (n m : ℕ) :
    ((affineSimplexSSet Y).chainComplex R).X n ⟶
      ((affineSimplexSSet Y).chainComplex R).X m :=
  if h : n + 1 = m then
    affineSubdivisionHomotopyAux Y R n ≫ eqToHom (by simp [h])
  else 0

@[simp]
lemma affineSubdivisionHomotopyComponent_eq (R : C) (n : ℕ) :
    affineSubdivisionHomotopyComponent Y R n (n + 1) =
      affineSubdivisionHomotopyAux Y R n := by
  simp [affineSubdivisionHomotopyComponent]

lemma affineSubdivisionHomotopyComponent_zero (R : C) (n m : ℕ)
    (h : n + 1 ≠ m) :
    affineSubdivisionHomotopyComponent Y R n m = 0 := by
  grind [affineSubdivisionHomotopyComponent]

/-- Barycentric subdivision as an endomorphism of affine chains. -/
def affineChainSubdivision (R : C) :
    (affineSimplexSSet Y).chainComplex R ⟶
      (affineSimplexSSet Y).chainComplex R :=
  𝟙 _ - Homotopy.nullHomotopicMap
    (affineSubdivisionHomotopyComponent Y R)

/-- The canonical cone homotopy from the identity to barycentric subdivision
on affine chains. -/
def affineChainHomotopyIdSubdivision (R : C) :
    Homotopy (𝟙 _) (affineChainSubdivision Y R) :=
  Homotopy.equivSubZero.symm
    (.trans (.ofEq (by simp [affineChainSubdivision]))
      (.nullHomotopy (affineSubdivisionHomotopyComponent Y R)
        (affineSubdivisionHomotopyComponent_zero Y R)))

lemma affineChainHomotopyIdSubdivision_hom_eq (R : C) (n m : ℕ) :
    (affineChainHomotopyIdSubdivision Y R).hom n m =
      affineSubdivisionHomotopyComponent Y R n m := by
  simp only [affineChainHomotopyIdSubdivision, Homotopy.equivSubZero,
    Equiv.symm_mk, Equiv.coe_fn_mk, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Pi.zero_apply, zero_add]
  apply Homotopy.nullHomotopy_hom

@[reassoc]
lemma affineChainHomotopyIdSubdivision_naturality
    (φ : ConvexSpace.AffineMap ℝ Y Z) (R : C) (n m : ℕ) :
    (SSet.chainComplexMap (affineMapToSSet Y φ) R).f n ≫
        (affineChainHomotopyIdSubdivision Z R).hom n m =
      (affineChainHomotopyIdSubdivision Y R).hom n m ≫
        (SSet.chainComplexMap (affineMapToSSet Y φ) R).f m := by
  by_cases hm : n + 1 = m
  · subst hm
    simp only [affineChainHomotopyIdSubdivision_hom_eq,
      affineSubdivisionHomotopyComponent_eq,
      affineSubdivisionHomotopyAux_naturality]
  · rw [Homotopy.zero _ _ _ (by simpa), Homotopy.zero _ _ _ (by simpa),
      comp_zero, zero_comp]

@[reassoc]
lemma iota_affineMapToSSet_homotopy_hom
    (φ : ConvexSpace.AffineMap ℝ Y Z) (R : C) {n : ℕ}
    (x : affineSimplexSSet Y _⦋n⦌) (m : ℕ) :
    SSet.ιChainComplex _ ((affineMapToSSet Y φ).app _ x) ≫
        (affineChainHomotopyIdSubdivision Z R).hom n m =
      SSet.ιChainComplex _ x ≫
        (affineChainHomotopyIdSubdivision Y R).hom n m ≫
          (SSet.chainComplexMap (affineMapToSSet Y φ) R).f m := by
  simpa using SSet.ιChainComplex _ x ≫=
    affineChainHomotopyIdSubdivision_naturality Y φ R n m

@[simp]
lemma affineChainSubdivision_f_zero (R : C) :
    (affineChainSubdivision Y R).f 0 = 𝟙 _ := by
  simp [affineChainSubdivision,
    Homotopy.nullHomotopicMap_f_of_not_rel_left
      (ComplexShape.down_mk 1 0 rfl) (by simp)]

lemma affineChainSubdivision_f_succ (R : C) (n : ℕ) :
    (affineChainSubdivision Y R).f (n + 1) = 𝟙 _
      - ((affineSimplexSSet Y).chainComplex R).d (n + 1) n ≫
          affineSubdivisionHomotopyAux Y R n
      - affineSubdivisionHomotopyAux Y R (n + 1) ≫
          ((affineSimplexSSet Y).chainComplex R).d (n + 2) (n + 1) := by
  simp [affineChainSubdivision,
    Homotopy.nullHomotopicMap_f (ComplexShape.down_mk (n + 2) (n + 1) rfl)
      (ComplexShape.down_mk (n + 1) n rfl), sub_sub,
    affineSubdivisionHomotopyComponent_eq]

@[reassoc]
lemma iota_affineChainSubdivision_f_succ (R : C) {n : ℕ}
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 2))) Y) :
    SSet.ιChainComplex _ s ≫ (affineChainSubdivision Y R).f (n + 1) =
      SSet.ιChainComplex _ s ≫
        ((affineSimplexSSet Y).chainComplex R).d (n + 1) n ≫
          (affineChainSubdivision Y R).f n ≫
            affineChainCone Y (affineBarycenter Y s) R n := by
  obtain _ | n := n
  · simp [affineChainSubdivision_f_succ,
      affineChain_cone_comp_d_eq_sub]
  · simp [affineChainSubdivision_f_succ,
      iota_affineSubdivisionHomotopyAux_succ_assoc,
      affineChain_cone_comp_d_eq_sub]

@[simp]
lemma affineSubdivision_fin_one
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin 1)) Y)
    (σ : Equiv.Perm (Fin 1)) :
    affineSubdivision s σ = s := by
  apply StdSimplex.affineMap_ext
  intro i
  fin_cases i
  simp [affineSubdivision, affineSubdivisionVertex_def, affineSubBarycenter]

open Equiv.Perm in
@[reassoc]
lemma iota_affineChainSubdivision_eq_sum (R : C) {n : ℕ}
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) Y) :
    SSet.ιChainComplex _ s ≫ (affineChainSubdivision Y R).f n =
      ∑ (σ : Equiv.Perm (Fin (n + 1))),
        σ.sign • SSet.ιChainComplex _ (affineSubdivision s σ) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [iota_affineChainSubdivision_f_succ]
    obtain ⟨s, rfl⟩ := StdSimplex.affineMapMk_surjective s
    simp only [SSet.ιChainComplex_d_assoc, Preadditive.sum_comp,
      Linear.smul_comp, reassoc_of% hn, iota_affineChainCone,
      ← decomposeFin'.symm.sum_comp,
      Finset.sum_finset_product .univ .univ (fun _ ↦ .univ) (by simp),
      Equiv.Perm.decomposeFin'_symm, Finset.smul_sum, Units.smul_def,
      smul_smul, Equiv.Perm.sign_decomposeFin'Symm]
    congr 1
    ext i
    congr 1
    ext σ
    congr 2
    apply StdSimplex.affineMap_ext
    intro j
    obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
    · simp [affineBarycenter, affineSubdivision,
        affineSubdivisionVertex_def, affineSubBarycenter]
    · rw [affineSimplex_delta_affineMapMk]
      simp only [affineCone_single_succ, affineSubdivision,
        StdSimplex.affineMapMk_single, affineSubdivisionVertex_def,
        Equiv.Perm.coe_inv]
      rw [affineSubBarycenter_mk_comp_of_injective Y _ _ _ _
        Fin.succAbove_right_injective]
      congr 1
      ext k
      obtain ⟨k, rfl⟩ := (decomposeFin'Symm i σ).surjective k
      obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_eq_succ <;> simp

/-- The `k`-fold iterate of barycentric subdivision on affine chains. -/
def affineChainSubdivisionIter (R : C) (k : ℕ) :
    (affineSimplexSSet Y).chainComplex R ⟶
      (affineSimplexSSet Y).chainComplex R :=
  let x : End _ := affineChainSubdivision Y R
  x ^ k

@[simp]
lemma affineChainSubdivisionIter_zero (R : C) :
    affineChainSubdivisionIter Y R 0 = 𝟙 _ := by
  simp [affineChainSubdivisionIter]

@[simp]
lemma affineChainSubdivisionIter_one (R : C) :
    affineChainSubdivisionIter Y R 1 = affineChainSubdivision Y R := by
  simp [affineChainSubdivisionIter]

@[reassoc]
lemma affineChainSubdivisionIter_add (R : C) (k l : ℕ) :
    affineChainSubdivisionIter Y R (k + l) =
      affineChainSubdivisionIter Y R k ≫
        affineChainSubdivisionIter Y R l := by
  simp [add_comm k l, affineChainSubdivisionIter, pow_add]

@[reassoc]
lemma affineChainSubdivisionIter_succ (R : C) (k : ℕ) :
    affineChainSubdivisionIter Y R (k + 1) =
      affineChainSubdivisionIter Y R k ≫
        affineChainSubdivision Y R := by
  simp [affineChainSubdivisionIter_add]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma iota_affineChainSubdivisionIter_eq_sum (R : C) {n : ℕ}
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) Y)
    (k : ℕ) :
    SSet.ιChainComplex _ s ≫ (affineChainSubdivisionIter Y R k).f n =
      ∑ (σ : Fin k → Equiv.Perm (Fin (n + 1))),
        (∏ i, (σ i).sign) •
          SSet.ιChainComplex _ (affineSubdivisionIter s σ) := by
  induction k with
  | zero => simp
  | succ k hk =>
    let e : (Fin (k + 1) → Equiv.Perm (Fin (n + 1))) ≃
        (Fin k → Equiv.Perm (Fin (n + 1))) ×
          Equiv.Perm (Fin (n + 1)) :=
      { toFun σ := ⟨σ ∘ Fin.succ, σ 0⟩
        invFun := fun ⟨σ, σ'⟩ ↦ Fin.cases σ' σ
        left_inv σ := by
          ext l : 1
          obtain rfl | ⟨l, rfl⟩ := l.eq_zero_or_eq_succ <;> rfl }
    simp only [affineChainSubdivisionIter_succ, HomologicalComplex.comp_f,
      reassoc_of% hk, Preadditive.sum_comp, Linear.units_smul_comp,
      iota_affineChainSubdivision_eq_sum, Finset.smul_sum, smul_smul]
    rw [Finset.sum_bijective
      (g := fun ⟨σ, σ₀⟩ ↦
        ((∏ i, Equiv.Perm.sign (σ i)) * Equiv.Perm.sign σ₀) •
          SSet.ιChainComplex (affineSimplexSSet Y)
            (affineSubdivision (affineSubdivisionIter s σ) σ₀))
      (t := .univ) _ e.bijective (by simp) ?_,
      Finset.sum_finset_product .univ .univ (fun _ ↦ .univ) (by simp)]
    simp only [Finset.mem_univ, forall_const]
    intro σ
    congr
    · rw [mul_comm]
      simp [e, Fin.prod_univ_succ]

end Hatcher.Excision
