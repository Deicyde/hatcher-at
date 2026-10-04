/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.StandardSimplexZeroFaceHomology
import Hatcher.Singular.StandardSimplexZeroHorn
import Hatcher.Singular.TripleConnectingFormula
import Hatcher.Singular.Reduced

/-!
# The relative fundamental class of a standard simplex

This file constructs the class of the identity singular simplex in
`H_n(Δ[n], ∂Δ[n]; R)` and proves that it is an isomorphism.  The induction
uses the triple `(Δ[n+1], ∂Δ[n+1], Λ⁰[n+1])`; omitting face zero makes the
surviving boundary coefficient `+1`.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Set Simplicial Topology
open scoped Simplicial

namespace Hatcher.Simplex

private noncomputable abbrev relativeSimplexSSetPair (n : ℕ) : SSetPair.{0} :=
  Hatcher.Relative.singularPairFunctor.obj (standardSimplexPair n)

private theorem standardSimplexBoundary_zero_false
    (x : standardSimplexBoundary 0) : False := by
  obtain ⟨i, hi⟩ := x.2
  fin_cases i
  have hsumZero : ∑ j : Fin 1, x.1.weights j = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    fin_cases j
    exact hi
  linarith [x.1.total_of_fintype, hsumZero]

/-- The `i`th face of the identity simplex, with codomain restricted to the
boundary. -/
def standardSimplexFaceToBoundary (n : ℕ) (i : Fin (n + 2)) :
    C(StandardSimplex n, standardSimplexBoundary (n + 1)) where
  toFun x := ⟨Convexity.StdSimplex.map i.succAbove x, ⟨i, by
    exact Finsupp.mapDomain_of_notMem_range x.weights i (by simp)⟩⟩
  continuous_toFun :=
    (Convexity.StdSimplex.continuous_map ℝ i.succAbove).subtype_mk _

/-- Every nonzero face of the identity simplex lies in the zero horn. -/
def standardSimplexFaceToZeroHorn (n : ℕ) (i : Fin (n + 2)) (hi : i ≠ 0) :
    C(StandardSimplex n, standardSimplexZeroHorn n) where
  toFun x := ⟨Convexity.StdSimplex.map i.succAbove x, ⟨i, hi, by
    exact Finsupp.mapDomain_of_notMem_range x.weights i (by simp)⟩⟩
  continuous_toFun :=
    (Convexity.StdSimplex.continuous_map ℝ i.succAbove).subtype_mk _

/-- The `i`th face of the identity singular simplex, regarded as a singular
simplex of the boundary. -/
def standardSimplexIdentityFaceInBoundary (n : ℕ) (i : Fin (n + 2)) :
    (relativeSimplexSSetPair (n + 1)).left _⦋n⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm (standardSimplexFaceToBoundary n i)

/-- A nonzero face of the identity singular simplex, regarded as a singular
simplex of the zero horn. -/
def standardSimplexIdentityFaceInZeroHorn (n : ℕ)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    (TopCat.toSSet.obj (TopCat.of (standardSimplexZeroHorn n))) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm
    (standardSimplexFaceToZeroHorn n i hi)

/-- The identity singular simplex, with its ambient type expressed through
the relative simplex pair. -/
def standardSimplexPairIdentitySingularSimplex (n : ℕ) :
    (relativeSimplexSSetPair n).right _⦋n⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.id _)

@[simp]
theorem standardSimplexIdentityFaceInBoundary_map (n : ℕ)
    (i : Fin (n + 2)) :
    (relativeSimplexSSetPair (n + 1)).hom.app _
      (standardSimplexIdentityFaceInBoundary n i) =
      (relativeSimplexSSetPair (n + 1)).right.δ i
        (standardSimplexPairIdentitySingularSimplex (n + 1)) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext x
  rfl

@[simp]
theorem standardSimplexIdentityFaceInZeroHorn_map (n : ℕ)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    (TopCat.toSSet.map
      (TopCat.ofHom (standardSimplexZeroHornInclusion n))).app _
        (standardSimplexIdentityFaceInZeroHorn n i hi) =
      (TopCat.toSSet.obj (TopCat.of (StandardSimplex (n + 1)))).δ i
        (standardSimplexIdentitySingularSimplex (n + 1)) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext x
  rfl

@[simp]
theorem standardSimplexIdentity_zeroFace (n : ℕ) :
    (TopCat.toSSet.map
      (TopPair.Hom.fst (standardSimplexZeroFacePairHom n))).app _
        (standardSimplexPairIdentitySingularSimplex n) =
      standardSimplexIdentityFaceInBoundary n 0 := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext x
  rfl

private noncomputable abbrev boundaryHornABPair (n : ℕ) : SSetPair.{0} :=
  Hatcher.Relative.singularPairFunctor.obj
    (Hatcher.Relative.TopTriple.pairAB.obj
      (standardSimplexBoundaryHornTriple n))

private noncomputable abbrev boundaryHornXBPair (n : ℕ) : SSetPair.{0} :=
  Hatcher.Relative.singularPairFunctor.obj
    (Hatcher.Relative.TopTriple.pairXB.obj
      (standardSimplexBoundaryHornTriple n))

private noncomputable abbrev boundaryHornXAPair (n : ℕ) : SSetPair.{0} :=
  Hatcher.Relative.singularPairFunctor.obj
    (Hatcher.Relative.TopTriple.pairXA.obj
      (standardSimplexBoundaryHornTriple n))

private noncomputable abbrev boundaryHornABToXBMap (n : ℕ) :
    boundaryHornABPair n ⟶ boundaryHornXBPair n :=
  Hatcher.Relative.singularPairFunctor.map
    (Hatcher.Relative.TopTriple.pairABToXB
      (standardSimplexBoundaryHornTriple n))

private noncomputable abbrev boundaryHornXBToXAMap (n : ℕ) :
    boundaryHornXBPair n ⟶ boundaryHornXAPair n :=
  Hatcher.Relative.singularPairFunctor.map
    (Hatcher.Relative.TopTriple.pairXBToXA
      (standardSimplexBoundaryHornTriple n))

private noncomputable abbrev simplexZeroFaceSSetPairMap (n : ℕ) :
    relativeSimplexSSetPair n ⟶ boundaryHornABPair n :=
  Hatcher.Relative.singularPairFunctor.map
    (standardSimplexZeroFacePairHom n)

private def zeroHornSelfPair (n : ℕ) : TopPair.{0} :=
  TopPair.diag.obj (TopCat.of (standardSimplexZeroHorn n))

private def zeroHornSelfPairToXB (n : ℕ) :
    zeroHornSelfPair n ⟶
      Hatcher.Relative.TopTriple.pairXB.obj
        (standardSimplexBoundaryHornTriple n) :=
  TopPair.ofHom
    (standardSimplexBoundaryHornTriple n).mapBX
    (𝟙 _)
    (by
      change 𝟙 _ ≫ (standardSimplexBoundaryHornTriple n).mapBX =
        𝟙 _ ≫ (standardSimplexBoundaryHornTriple n).mapBX
      rfl)

private def boundaryHornIdentityFaceInBoundary (n : ℕ)
    (i : Fin (n + 2)) :
    (boundaryHornABPair n).right _⦋n⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm (standardSimplexFaceToBoundary n i)

private def boundaryHornXAIdentityFaceInBoundary (n : ℕ)
    (i : Fin (n + 2)) :
    (boundaryHornXAPair n).left _⦋n⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm (standardSimplexFaceToBoundary n i)

private def boundaryHornIdentityFaceInZeroHorn (n : ℕ)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    (boundaryHornXBPair n).left _⦋n⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm
    (standardSimplexFaceToZeroHorn n i hi)

private def boundaryHornIdentitySingularSimplex (n : ℕ) :
    (boundaryHornXBPair n).right _⦋n + 1⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.id _)

private def boundaryHornXAIdentitySingularSimplex (n : ℕ) :
    (boundaryHornXAPair n).right _⦋n + 1⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.id _)

@[simp]
private theorem boundaryHornIdentityFaceInBoundary_map (n : ℕ)
    (i : Fin (n + 2)) :
    (TopCat.toSSet.map
      (standardSimplexBoundaryHornTriple n).mapAX).app _
        (boundaryHornIdentityFaceInBoundary n i) =
      (boundaryHornXBPair n).right.δ i
        (boundaryHornIdentitySingularSimplex n) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext x
  rfl

@[simp]
private theorem boundaryHornXAIdentityFaceInBoundary_map (n : ℕ)
    (i : Fin (n + 2)) :
    (boundaryHornXAPair n).hom.app _
        (boundaryHornXAIdentityFaceInBoundary n i) =
      (boundaryHornXAPair n).right.δ i
        (boundaryHornXAIdentitySingularSimplex n) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext x
  rfl

@[simp]
private theorem boundaryHornIdentityFaceInZeroHorn_map (n : ℕ)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    (boundaryHornXBPair n).hom.app _
        (boundaryHornIdentityFaceInZeroHorn n i hi) =
      (boundaryHornXBPair n).right.δ i
        (boundaryHornIdentitySingularSimplex n) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext x
  rfl

universe v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C]

private noncomputable def standardSimplexZeroChainIso (R : C) :
    R ≅ ((relativeSimplexSSetPair 0).right.chainComplex R).X 0 where
  hom := (relativeSimplexSSetPair 0).right.ιChainComplex
    (standardSimplexPairIdentitySingularSimplex 0)
  inv := Sigma.desc (fun _ ↦ 𝟙 R)
  hom_inv_id := by
    change Sigma.ι (fun _ : (relativeSimplexSSetPair 0).right _⦋0⦌ ↦ R)
        (standardSimplexPairIdentitySingularSimplex 0) ≫
      Sigma.desc (fun _ ↦ 𝟙 R) = 𝟙 R
    rw [Sigma.ι_comp_desc]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro x
    obtain rfl : x = standardSimplexPairIdentitySingularSimplex 0 := by
      apply (TopCat.toSSetObjEquiv _ _).injective
      ext y
      change (_ : StandardSimplex 0) = _
      exact Subsingleton.elim _ _
    simp [SSet.ιChainComplex]
    exact (Category.comp_id _).symm

private theorem standardSimplexZero_singularBoundary_eq_zero (R : C) :
    ((relativeSimplexSSetPair 0).right.chainComplex R).d 1 0 = 0 := by
  apply (relativeSimplexSSetPair 0).right.chainComplex_hom_ext
  intro x
  rw [SSet.ιChainComplex_d]
  have hface :
      (relativeSimplexSSetPair 0).right.δ (0 : Fin 2) x =
        (relativeSimplexSSetPair 0).right.δ (1 : Fin 2) x := by
    apply (TopCat.toSSetObjEquiv _ _).injective
    ext y
    change (_ : StandardSimplex 0) = _
    exact Subsingleton.elim _ _
  simp [Fin.sum_univ_two, hface]

private theorem relativeSimplexBoundary_zero_notNonempty :
    ¬ (relativeSimplexSSetPair 0).left.Nonempty := by
  rintro ⟨x⟩
  exact standardSimplexBoundary_zero_false
    ((TopCat.toSSetObjEquiv _ _) x default)

private theorem isZero_zeroHornSelfPair_homology
    (R : C) (n k : ℕ) :
    IsZero ((Hatcher.Relative.homologyFunctor R k).obj
      (zeroHornSelfPair n)) := by
  let P := Hatcher.Relative.singularPairFunctor.obj (zeroHornSelfPair n)
  haveI : IsIso (zeroHornSelfPair n).map := by
    change IsIso (𝟙 (TopCat.of (standardSimplexZeroHorn n)))
    infer_instance
  haveI : IsIso P.hom := by
    change IsIso (TopCat.toSSet.map (zeroHornSelfPair n).map)
    infer_instance
  have hK : IsZero (P.chainComplex R) := P.isZero_chainComplex R
  exact ((P.chainComplex R).acyclic_of_isZero hK k).isZero_homology

private theorem isZero_boundaryHornXB_homology
    (R : C) (n k : ℕ) :
    IsZero ((Hatcher.Relative.homologyFunctor R k).obj
      (Hatcher.Relative.TopTriple.pairXB.obj
        (standardSimplexBoundaryHornTriple n))) := by
  let f := zeroHornSelfPairToXB n
  have hf :
      IsIso ((Hatcher.Relative.homologyFunctor R k).map f) := by
    apply Hatcher.Relative.homologyMap_isIso_of_components
    · intro j
      change IsIso (((singularHomologyFunctor C j).obj R).map (𝟙 _))
      infer_instance
    · intro j
      let e := (zeroHornStrongDeformationRetract n).toHomotopyEquiv.symm
      change IsIso (((singularHomologyFunctor C j).obj R).map
        (TopCat.ofHom e.toFun))
      exact (Hatcher.Singular.homologyIsoOfHomotopyEquiv e R j).isIso_hom
  letI := hf
  exact (isZero_zeroHornSelfPair_homology R n k).of_iso
    (asIso ((Hatcher.Relative.homologyFunctor R k).map f)).symm

/-- The identity singular simplex as an absolute singular chain. -/
noncomputable def standardSimplexIdentityChain (R : C) (n : ℕ) :
    R ⟶ ((relativeSimplexSSetPair n).right.chainComplex R).X n :=
  (relativeSimplexSSetPair n).right.ιChainComplex
    (standardSimplexPairIdentitySingularSimplex n)

/-- The identity singular simplex, projected to relative chains. -/
noncomputable def relativeSimplexIdentityChain (R : C) (n : ℕ) :
    R ⟶ ((relativeSimplexSSetPair n).chainComplex R).X n :=
  standardSimplexIdentityChain R n ≫
    ((relativeSimplexSSetPair n).chainComplexπ R).f n

private noncomputable def boundaryHornXBIdentityChain (R : C) (n : ℕ) :
    R ⟶ ((boundaryHornXBPair n).chainComplex R).X (n + 1) :=
  (boundaryHornXBPair n).right.ιChainComplex
      (boundaryHornIdentitySingularSimplex n) ≫
    ((boundaryHornXBPair n).chainComplexπ R).f (n + 1)

private noncomputable def boundaryHornXAIdentityChain (R : C) (n : ℕ) :
    R ⟶ ((boundaryHornXAPair n).chainComplex R).X (n + 1) :=
  (boundaryHornXAPair n).right.ιChainComplex
      (boundaryHornXAIdentitySingularSimplex n) ≫
    ((boundaryHornXAPair n).chainComplexπ R).f (n + 1)

set_option backward.isDefEq.respectTransparency false in
private theorem boundaryHornXAIdentityChain_eq (R : C) (n : ℕ) :
    boundaryHornXAIdentityChain R n =
      relativeSimplexIdentityChain R (n + 1) := by
  rfl

private theorem boundaryHornXAFace_projection_eq_zero
    (R : C) (n : ℕ) (i : Fin (n + 2)) :
    (boundaryHornXAPair n).right.ιChainComplex
          ((boundaryHornXAPair n).right.δ i
            (boundaryHornXAIdentitySingularSimplex n)) ≫
        ((boundaryHornXAPair n).chainComplexπ R).f n =
      0 := by
  rw [← boundaryHornXAIdentityFaceInBoundary_map n i]
  let P := boundaryHornXAPair n
  let x := boundaryHornXAIdentityFaceInBoundary n i
  have hι := SSet.ι_chainComplexMap_f P.left P.right P.hom R x
  calc
    _ = (P.left.ιChainComplex x ≫
          (SSet.chainComplexMap P.hom R).f n) ≫
        (P.chainComplexπ R).f n := by
      rw [hι]
    _ = 0 := by
      rw [Category.assoc, P.chainComplex_condition_f, comp_zero]

private theorem boundaryHornXAIdentityChain_cycle (R : C) (n : ℕ) :
    boundaryHornXAIdentityChain R n ≫
        ((boundaryHornXAPair n).chainComplex R).d (n + 1) n =
      0 := by
  dsimp only [boundaryHornXAIdentityChain]
  rw [Category.assoc, ((boundaryHornXAPair n).chainComplexπ R).comm]
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp]
  apply Finset.sum_eq_zero
  intro i _
  rw [Preadditive.zsmul_comp]
  simp only [boundaryHornXAFace_projection_eq_zero, smul_zero]

private noncomputable def boundaryHornABZeroFaceChain (R : C) (n : ℕ) :
    R ⟶ ((boundaryHornABPair n).chainComplex R).X n :=
  (boundaryHornABPair n).right.ιChainComplex
      (boundaryHornIdentityFaceInBoundary n 0) ≫
    ((boundaryHornABPair n).chainComplexπ R).f n

private theorem boundaryHornPositiveFace_projection_eq_zero
    (R : C) (n : ℕ) (i : Fin (n + 2)) (hi : i ≠ 0) :
    (boundaryHornXBPair n).right.ιChainComplex
          ((boundaryHornXBPair n).right.δ i
            (boundaryHornIdentitySingularSimplex n)) ≫
        ((boundaryHornXBPair n).chainComplexπ R).f n =
      0 := by
  rw [← boundaryHornIdentityFaceInZeroHorn_map n i hi]
  let P := boundaryHornXBPair n
  let x := boundaryHornIdentityFaceInZeroHorn n i hi
  have hι := SSet.ι_chainComplexMap_f P.left P.right P.hom R x
  calc
    _ = (P.left.ιChainComplex x ≫
          (SSet.chainComplexMap P.hom R).f n) ≫
        (P.chainComplexπ R).f n := by
      rw [hι]
    _ = 0 := by
      rw [Category.assoc, P.chainComplex_condition_f, comp_zero]

private theorem boundaryHornZeroFace_map_eq
    (R : C) (n : ℕ) :
    boundaryHornABZeroFaceChain R n ≫
        (SSetPair.chainComplexMap (boundaryHornABToXBMap n) R).f n =
      (boundaryHornXBPair n).right.ιChainComplex
          ((boundaryHornXBPair n).right.δ 0
            (boundaryHornIdentitySingularSimplex n)) ≫
        ((boundaryHornXBPair n).chainComplexπ R).f n := by
  let P := boundaryHornABPair n
  let Q := boundaryHornXBPair n
  let f := boundaryHornABToXBMap n
  let x := boundaryHornIdentityFaceInBoundary n 0
  have hι := SSet.ι_chainComplexMap_f P.right Q.right f.right R x
  have hface :
      (ConcreteCategory.hom (f.right.app (Opposite.op ⦋n⦌))) x =
        Q.right.δ 0 (boundaryHornIdentitySingularSimplex n) := by
    exact boundaryHornIdentityFaceInBoundary_map n 0
  have hπ :
      (P.chainComplexπ R).f n ≫
          (SSetPair.chainComplexMap f R).f n =
        (SSet.chainComplexMap f.right R).f n ≫
          (Q.chainComplexπ R).f n := by
    change ((((SSetPair.chainComplexFunctorπ C).app R).app P ≫
      ((SSetPair.chainComplexFunctor C).obj R).map f).f n) =
      ((((SSetPair.chainComplexFunctorRight C).obj R).map f ≫
        ((SSetPair.chainComplexFunctorπ C).app R).app Q).f n)
    exact congrArg (fun φ ↦ φ.f n)
      (((SSetPair.chainComplexFunctorπ C).app R).naturality f).symm
  change (P.right.ιChainComplex x ≫ (P.chainComplexπ R).f n) ≫
      (SSetPair.chainComplexMap f R).f n = _
  rw [Category.assoc, hπ]
  rw [← Category.assoc, hι, hface]

private theorem boundaryHornXBIdentityChain_map_eq
    (R : C) (n : ℕ) :
    boundaryHornXBIdentityChain R n ≫
        (SSetPair.chainComplexMap (boundaryHornXBToXAMap n) R).f (n + 1) =
      boundaryHornXAIdentityChain R n := by
  let P := boundaryHornXBPair n
  let Q := boundaryHornXAPair n
  let f := boundaryHornXBToXAMap n
  let x := boundaryHornIdentitySingularSimplex n
  have hι := SSet.ι_chainComplexMap_f P.right Q.right f.right R x
  have hsimplex :
      (ConcreteCategory.hom (f.right.app (Opposite.op ⦋n + 1⦌))) x =
        boundaryHornXAIdentitySingularSimplex n := by
    apply (TopCat.toSSetObjEquiv _ _).injective
    ext y
    rfl
  have hπ :
      (P.chainComplexπ R).f (n + 1) ≫
          (SSetPair.chainComplexMap f R).f (n + 1) =
        (SSet.chainComplexMap f.right R).f (n + 1) ≫
          (Q.chainComplexπ R).f (n + 1) := by
    change ((((SSetPair.chainComplexFunctorπ C).app R).app P ≫
      ((SSetPair.chainComplexFunctor C).obj R).map f).f (n + 1)) =
      ((((SSetPair.chainComplexFunctorRight C).obj R).map f ≫
        ((SSetPair.chainComplexFunctorπ C).app R).app Q).f (n + 1))
    exact congrArg (fun φ ↦ φ.f (n + 1))
      (((SSetPair.chainComplexFunctorπ C).app R).naturality f).symm
  change (P.right.ιChainComplex x ≫ (P.chainComplexπ R).f (n + 1)) ≫
      (SSetPair.chainComplexMap f R).f (n + 1) = _
  rw [Category.assoc, hπ]
  rw [← Category.assoc, hι, hsimplex]
  rfl

private theorem boundaryHornXBIdentityChain_boundary
    (R : C) (n : ℕ) :
    boundaryHornABZeroFaceChain R n ≫
        (SSetPair.chainComplexMap (boundaryHornABToXBMap n) R).f n =
      boundaryHornXBIdentityChain R n ≫
        ((boundaryHornXBPair n).chainComplex R).d (n + 1) n := by
  rw [boundaryHornZeroFace_map_eq]
  dsimp only [boundaryHornXBIdentityChain]
  rw [Category.assoc, ((boundaryHornXBPair n).chainComplexπ R).comm]
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    rw [Preadditive.zsmul_comp,
      boundaryHornPositiveFace_projection_eq_zero R n i hi, smul_zero]
  · simp

private theorem relativeSimplexIdentityChain_zeroFace
    (R : C) (n : ℕ) :
    relativeSimplexIdentityChain R n ≫
        (SSetPair.chainComplexMap (simplexZeroFaceSSetPairMap n) R).f n =
      boundaryHornABZeroFaceChain R n := by
  let P := relativeSimplexSSetPair n
  let Q := boundaryHornABPair n
  let f := simplexZeroFaceSSetPairMap n
  let x := standardSimplexPairIdentitySingularSimplex n
  have hι := SSet.ι_chainComplexMap_f P.right Q.right f.right R x
  have hface :
      (ConcreteCategory.hom (f.right.app (Opposite.op ⦋n⦌))) x =
        boundaryHornIdentityFaceInBoundary n 0 := by
    apply (TopCat.toSSetObjEquiv _ _).injective
    ext y
    rfl
  have hπ :
      (P.chainComplexπ R).f n ≫
          (SSetPair.chainComplexMap f R).f n =
        (SSet.chainComplexMap f.right R).f n ≫
          (Q.chainComplexπ R).f n := by
    change ((((SSetPair.chainComplexFunctorπ C).app R).app P ≫
      ((SSetPair.chainComplexFunctor C).obj R).map f).f n) =
      ((((SSetPair.chainComplexFunctorRight C).obj R).map f ≫
        ((SSetPair.chainComplexFunctorπ C).app R).app Q).f n)
    exact congrArg (fun φ ↦ φ.f n)
      (((SSetPair.chainComplexFunctorπ C).app R).naturality f).symm
  change (P.right.ιChainComplex x ≫ (P.chainComplexπ R).f n) ≫
      (SSetPair.chainComplexMap f R).f n = _
  rw [Category.assoc, hπ]
  rw [← Category.assoc, hι, hface]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem identityFace_relativeProjection_eq_zero
    (R : C) (n : ℕ) (i : Fin (n + 2)) :
    (relativeSimplexSSetPair (n + 1)).right.ιChainComplex
          ((relativeSimplexSSetPair (n + 1)).right.δ i
            (standardSimplexPairIdentitySingularSimplex (n + 1))) ≫
        ((relativeSimplexSSetPair (n + 1)).chainComplexπ R).f n =
      0 := by
  rw [← standardSimplexIdentityFaceInBoundary_map n i]
  let P := relativeSimplexSSetPair (n + 1)
  let x := standardSimplexIdentityFaceInBoundary n i
  have hι := SSet.ι_chainComplexMap_f
    P.left P.right P.hom R x
  calc
    _ = (P.left.ιChainComplex x ≫
          (SSet.chainComplexMap P.hom R).f n) ≫
        (P.chainComplexπ R).f n := by
      rw [hι]
      rfl
    _ = 0 := by
      rw [Category.assoc, P.chainComplex_condition_f, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The projected identity simplex is a relative cycle. -/
theorem relativeSimplexIdentityChain_cycle (R : C) (n : ℕ) :
    relativeSimplexIdentityChain R n ≫
        ((relativeSimplexSSetPair n).chainComplex R).d n
            ((ComplexShape.down ℕ).next n) =
      0 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [show (ComplexShape.down ℕ).next (n + 1) = n by simp]
      change (standardSimplexIdentityChain R (n + 1) ≫
          ((relativeSimplexSSetPair (n + 1)).chainComplexπ R).f (n + 1)) ≫ _ = 0
      rw [Category.assoc,
        ((relativeSimplexSSetPair (n + 1)).chainComplexπ R).comm]
      dsimp only [standardSimplexIdentityChain]
      rw [← Category.assoc, SSet.ιChainComplex_d]
      simp only [Preadditive.sum_comp]
      apply Finset.sum_eq_zero
      intro i _
      rw [Preadditive.zsmul_comp]
      simp only [identityFace_relativeProjection_eq_zero, smul_zero]

private theorem boundaryHornABZeroFaceChain_cycle (R : C) (n : ℕ) :
    boundaryHornABZeroFaceChain R n ≫
        ((boundaryHornABPair n).chainComplex R).d n
          ((ComplexShape.down ℕ).next n) =
      0 := by
  rw [← relativeSimplexIdentityChain_zeroFace R n]
  rw [Category.assoc,
    (SSetPair.chainComplexMap (simplexZeroFaceSSetPairMap n) R).comm]
  rw [← Category.assoc, relativeSimplexIdentityChain_cycle, zero_comp]

/-- **Hatcher, Example 2.23 (page 125).** The class of the identity singular
`n`-simplex in `H_n(Δ[n], ∂Δ[n]; R)`. -/
noncomputable def relativeSimplexFundamentalClass (R : C) (n : ℕ) :
    R ⟶ (Hatcher.Relative.homologyFunctor R n).obj
      (standardSimplexPair n) :=
  let K := (Hatcher.Relative.chainComplexFunctor R).obj
    (standardSimplexPair n)
  K.liftCycles (relativeSimplexIdentityChain R n)
      ((ComplexShape.down ℕ).next n) rfl
      (relativeSimplexIdentityChain_cycle R n) ≫
    K.homologyπ n

set_option backward.isDefEq.respectTransparency false in
private theorem relativeSimplexFundamentalClass_zero_isIso (R : C) :
    IsIso (relativeSimplexFundamentalClass R 0) := by
  let P := relativeSimplexSSetPair 0
  let K := P.chainComplex R
  letI : P.left.HasDimensionLT 0 :=
    P.left.notNonempty_iff_hasDimensionLT_zero.mp
      relativeSimplexBoundary_zero_notNonempty
  have hπ : IsIso (P.chainComplexπ R) := inferInstance
  letI := hπ
  have hπ₀ : IsIso ((P.chainComplexπ R).f 0) := inferInstance
  letI := hπ₀
  have hid : IsIso (standardSimplexIdentityChain R 0) :=
    (standardSimplexZeroChainIso R).isIso_hom
  letI := hid
  have hrelative : IsIso (relativeSimplexIdentityChain R 0) := by
    change IsIso (standardSimplexIdentityChain R 0 ≫
      (P.chainComplexπ R).f 0)
    infer_instance
  letI := hrelative
  have hd : K.d 1 0 = 0 := by
    rw [← cancel_epi ((P.chainComplexπ R).f 1)]
    rw [(P.chainComplexπ R).comm]
    rw [standardSimplexZero_singularBoundary_eq_zero, zero_comp, comp_zero]
  have hhomologyπ : IsIso (K.homologyπ 0) :=
    K.isIso_homologyπ 1 0 (by simp) hd
  letI := hhomologyπ
  let ι := K.liftCycles (relativeSimplexIdentityChain R 0)
    ((ComplexShape.down ℕ).next 0) rfl
    (relativeSimplexIdentityChain_cycle R 0)
  have hι : IsIso ι := by
    have hiCycles : IsIso (K.iCycles 0) := inferInstance
    letI := hiCycles
    have hcomp : IsIso (ι ≫ K.iCycles 0) := by
      rw [K.liftCycles_i]
      exact hrelative
    letI := hcomp
    exact IsIso.of_isIso_comp_right ι (K.iCycles 0)
  letI := hι
  change IsIso (ι ≫ K.homologyπ 0)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem relativeSimplexFundamentalClass_zeroFace
    (R : C) (n : ℕ) :
    relativeSimplexFundamentalClass R n ≫
        (Hatcher.Relative.homologyFunctor R n).map
          (standardSimplexZeroFacePairHom n) =
      let K := (boundaryHornABPair n).chainComplex R
      K.liftCycles (boundaryHornABZeroFaceChain R n)
          ((ComplexShape.down ℕ).next n) rfl
          (boundaryHornABZeroFaceChain_cycle R n) ≫
        K.homologyπ n := by
  dsimp only [relativeSimplexFundamentalClass]
  dsimp only [Hatcher.Relative.homologyFunctor, Functor.comp_map,
    SSetPair.homologyFunctor_map]
  rw [Category.assoc]
  rw [HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  simpa only [relativeSimplexIdentityChain_zeroFace]

private noncomputable def boundaryHornXAIdentityClass (R : C) (n : ℕ) :
    R ⟶ (boundaryHornXAPair n).homology R (n + 1) :=
  let K := (boundaryHornXAPair n).chainComplex R
  K.liftCycles (boundaryHornXAIdentityChain R n) n (by simp)
      (boundaryHornXAIdentityChain_cycle R n) ≫
    K.homologyπ (n + 1)

private noncomputable def boundaryHornABZeroFaceClass (R : C) (n : ℕ) :
    R ⟶ (boundaryHornABPair n).homology R n :=
  let K := (boundaryHornABPair n).chainComplex R
  K.liftCycles (boundaryHornABZeroFaceChain R n)
      ((ComplexShape.down ℕ).next n) rfl
      (boundaryHornABZeroFaceChain_cycle R n) ≫
    K.homologyπ n

set_option backward.isDefEq.respectTransparency false in
private theorem boundaryHornXAIdentityClass_eq (R : C) (n : ℕ) :
    boundaryHornXAIdentityClass R n =
      relativeSimplexFundamentalClass R (n + 1) := by
  unfold boundaryHornXAIdentityClass relativeSimplexFundamentalClass
  simp only [show (ComplexShape.down ℕ).next (n + 1) = n by simp,
    boundaryHornXAIdentityChain_eq]
  change
    ((boundaryHornXAPair n).chainComplex R).liftCycles
          (relativeSimplexIdentityChain R (n + 1)) n _ _ ≫
        ((boundaryHornXAPair n).chainComplex R).homologyπ (n + 1) =
      ((boundaryHornXAPair n).chainComplex R).liftCycles
          (relativeSimplexIdentityChain R (n + 1)) n _ _ ≫
        ((boundaryHornXAPair n).chainComplex R).homologyπ (n + 1)
  rfl

private theorem boundaryHornClasses_tripleConnecting (R : C) (n : ℕ) :
    boundaryHornXAIdentityClass R n ≫
        Hatcher.Relative.tripleConnecting
          (standardSimplexBoundaryHornTriple n) R (n + 1) n rfl =
      boundaryHornABZeroFaceClass R n := by
  let T := standardSimplexBoundaryHornTriple n
  let x₃ := boundaryHornXAIdentityChain R n
  let x₂ := boundaryHornXBIdentityChain R n
  let x₁ := boundaryHornABZeroFaceChain R n
  have hx₃ :
      x₃ ≫ ((boundaryHornXAPair n).chainComplex R).d (n + 1) n = 0 :=
    boundaryHornXAIdentityChain_cycle R n
  have hx₂ :
      x₂ ≫ (Hatcher.Relative.tripleChainComplexMapXBToXA T R).f (n + 1) =
        x₃ :=
    boundaryHornXBIdentityChain_map_eq R n
  have hx₁ :
      x₁ ≫ (Hatcher.Relative.tripleChainComplexMapABToXB T R).f n =
        x₂ ≫ ((boundaryHornXBPair n).chainComplex R).d (n + 1) n :=
    boundaryHornXBIdentityChain_boundary R n
  have hx₁cycle :
      x₁ ≫ ((boundaryHornABPair n).chainComplex R).d n
          ((ComplexShape.down ℕ).next n) = 0 :=
    boundaryHornABZeroFaceChain_cycle R n
  have h := Hatcher.Relative.tripleConnecting_eq
    T R (n + 1) n rfl
    x₃ hx₃ x₂ hx₂ x₁ hx₁
    ((ComplexShape.down ℕ).next n) rfl hx₁cycle
  dsimp only [boundaryHornXAIdentityClass, boundaryHornABZeroFaceClass]
  exact (Category.assoc _ _ _).trans h

set_option backward.isDefEq.respectTransparency false in
private theorem relativeSimplexFundamentalClass_tripleConnecting
    (R : C) (n : ℕ) :
    relativeSimplexFundamentalClass R (n + 1) ≫
        Hatcher.Relative.tripleConnecting
          (standardSimplexBoundaryHornTriple n) R (n + 1) n rfl =
      relativeSimplexFundamentalClass R n ≫
        (Hatcher.Relative.homologyFunctor R n).map
          (standardSimplexZeroFacePairHom n) := by
  rw [relativeSimplexFundamentalClass_zeroFace]
  change relativeSimplexFundamentalClass R (n + 1) ≫
      Hatcher.Relative.tripleConnecting
        (standardSimplexBoundaryHornTriple n) R (n + 1) n rfl =
    boundaryHornABZeroFaceClass R n
  rw [← boundaryHornXAIdentityClass_eq]
  exact boundaryHornClasses_tripleConnecting R n

/-- **Hatcher, Example 2.23 (page 125).** The class represented by the
identity singular simplex generates the relative homology of the standard
simplex and its boundary.  The successor step uses face zero, whose
alternating-boundary coefficient is `+1`. -/
theorem relativeSimplexFundamentalClass_isIso (R : C) (n : ℕ) :
    IsIso (relativeSimplexFundamentalClass R n) := by
  induction n with
  | zero =>
      exact relativeSimplexFundamentalClass_zero_isIso R
  | succ n ih =>
      let δ := Hatcher.Relative.tripleConnecting
        (standardSimplexBoundaryHornTriple n) R (n + 1) n rfl
      have hδ : IsIso δ := Hatcher.Relative.tripleConnecting_isIso
        (standardSimplexBoundaryHornTriple n) R (n + 1) n rfl
        (isZero_boundaryHornXB_homology R n (n + 1))
        (isZero_boundaryHornXB_homology R n n)
      have hz : IsIso ((Hatcher.Relative.homologyFunctor R n).map
          (standardSimplexZeroFacePairHom n)) :=
        zeroFacePair_homologyMap_isIso R n n
      have hr : IsIso (relativeSimplexFundamentalClass R n ≫
          (Hatcher.Relative.homologyFunctor R n).map
            (standardSimplexZeroFacePairHom n)) :=
        IsIso.comp_isIso' ih hz
      exact @IsIso.of_isIso_fac_right C _ _ _ _ _ _ _
        hδ hr (relativeSimplexFundamentalClass_tripleConnecting R n)

end Hatcher.Simplex
