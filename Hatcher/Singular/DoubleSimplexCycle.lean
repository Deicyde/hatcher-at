/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.Reduced
import Hatcher.Singular.StandardSimplexBoundaryHorn

/-!
# The fundamental cycle of the ordered double simplex

This file constructs the topological pushout of two standard simplices along
their boundaries, with the same vertex ordering on both copies.  The
difference of the two canonical top-dimensional singular simplices is a cycle
in the augmented singular chain complex.  In dimension zero this is the
augmentation-zero difference of the two vertices.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Opposite Simplicial

namespace Hatcher.Simplex

/-- The boundary inclusion of the ordered topological standard simplex. -/
def standardSimplexBoundaryInclusion (n : ℕ) :
    TopCat.of (standardSimplexBoundary n) ⟶
      TopCat.of (StandardSimplex n) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The ordered double simplex: two copies of `Δ[n]` glued along their
boundaries by the identity, hence preserving the order of every boundary
vertex. -/
noncomputable abbrev doubleSimplex (n : ℕ) : TopCat.{0} :=
  pushout (standardSimplexBoundaryInclusion n)
    (standardSimplexBoundaryInclusion n)

/-- The inclusion of the first top-dimensional simplex into the ordered
double simplex. -/
noncomputable abbrev doubleSimplexFirstInclusion (n : ℕ) :
    TopCat.of (StandardSimplex n) ⟶ doubleSimplex n :=
  pushout.inl (standardSimplexBoundaryInclusion n)
    (standardSimplexBoundaryInclusion n)

/-- The inclusion of the second top-dimensional simplex into the ordered
double simplex. -/
noncomputable abbrev doubleSimplexSecondInclusion (n : ℕ) :
    TopCat.of (StandardSimplex n) ⟶ doubleSimplex n :=
  pushout.inr (standardSimplexBoundaryInclusion n)
    (standardSimplexBoundaryInclusion n)

/-- The first canonical singular `n`-simplex of the ordered double simplex. -/
noncomputable def doubleSimplexFirstSingularSimplex (n : ℕ) :
    (TopCat.toSSet.obj (doubleSimplex n)) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm (doubleSimplexFirstInclusion n).hom

/-- The second canonical singular `n`-simplex of the ordered double simplex. -/
noncomputable def doubleSimplexSecondSingularSimplex (n : ℕ) :
    (TopCat.toSSet.obj (doubleSimplex n)) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm (doubleSimplexSecondInclusion n).hom

/-- Corresponding faces of the two canonical simplices agree.  The equality
is the pushout relation evaluated on the ordered face whose missing
barycentric coordinate is `i`. -/
theorem doubleSimplex_face_eq (n : ℕ) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (doubleSimplex (n + 1))).δ i
        (doubleSimplexFirstSingularSimplex (n + 1)) =
      (TopCat.toSSet.obj (doubleSimplex (n + 1))).δ i
        (doubleSimplexSecondSingularSimplex (n + 1)) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext z
  let y : standardSimplexBoundary (n + 1) :=
    ⟨Convexity.StdSimplex.map i.succAbove z, ⟨i, by
      exact Finsupp.mapDomain_of_notMem_range z.weights i (by simp)⟩⟩
  exact ConcreteCategory.congr_hom
    (pushout.condition (f := standardSimplexBoundaryInclusion (n + 1))
      (g := standardSimplexBoundaryInclusion (n + 1))) y

universe v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C]
  [Preadditive C]

/-- **Hatcher, Example 2.23 (page 125).** The ordered difference of the two
top-dimensional singular simplices in the double-simplex model.  It is a
chain in degree `n + 1` of the augmented singular chain complex, representing
reduced degree `n`. -/
noncomputable def doubleSimplexFundamentalCycle (R : C) (n : ℕ) :
    R ⟶
      ((Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj
        (doubleSimplex n)).X (n + 1) := by
  change R ⟶ (TopCat.toSSet.obj (doubleSimplex n)).chainComplex R |>.X n
  exact
    (TopCat.toSSet.obj (doubleSimplex n)).ιChainComplex
        (doubleSimplexFirstSingularSimplex n) -
      (TopCat.toSSet.obj (doubleSimplex n)).ιChainComplex
        (doubleSimplexSecondSingularSimplex n)

/-- The ordered difference is a cycle in the augmented singular chain
complex.  In positive dimension, corresponding faces cancel term by term.
In dimension zero, both vertices have augmentation one, so their difference
has augmentation zero. -/
theorem doubleSimplexFundamentalCycle_d (R : C) (n : ℕ) :
    doubleSimplexFundamentalCycle R n ≫
        ((Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj
          (doubleSimplex n)).d (n + 1) n =
      0 := by
  cases n with
  | zero =>
      let first :
          R ⟶ (((singularChainComplexFunctor C).obj R).obj
            (doubleSimplex 0)).X 0 :=
        (TopCat.toSSet.obj (doubleSimplex 0)).ιChainComplex
          (doubleSimplexFirstSingularSimplex 0)
      let second :
          R ⟶ (((singularChainComplexFunctor C).obj R).obj
            (doubleSimplex 0)).X 0 :=
        (TopCat.toSSet.obj (doubleSimplex 0)).ιChainComplex
          (doubleSimplexSecondSingularSimplex 0)
      have hfirst :
          first ≫ Hatcher.Reduced.chainAugmentation R (doubleSimplex 0) =
            𝟙 R :=
        Hatcher.Reduced.ι_chainAugmentation R (doubleSimplex 0)
          (doubleSimplexFirstSingularSimplex 0)
      have hsecond :
          second ≫ Hatcher.Reduced.chainAugmentation R (doubleSimplex 0) =
            𝟙 R :=
        Hatcher.Reduced.ι_chainAugmentation R (doubleSimplex 0)
          (doubleSimplexSecondSingularSimplex 0)
      change
        (first - second) ≫
            Hatcher.Reduced.chainAugmentation R (doubleSimplex 0) = 0
      rw [Preadditive.sub_comp, hfirst, hsecond, sub_self]
  | succ n =>
      change
        ((TopCat.toSSet.obj (doubleSimplex (n + 1))).ιChainComplex
              (doubleSimplexFirstSingularSimplex (n + 1)) -
            (TopCat.toSSet.obj (doubleSimplex (n + 1))).ιChainComplex
              (doubleSimplexSecondSingularSimplex (n + 1))) ≫
            ((TopCat.toSSet.obj (doubleSimplex (n + 1))).chainComplex R).d
              (n + 1) n =
          0
      rw [Preadditive.sub_comp, SSet.ιChainComplex_d,
        SSet.ιChainComplex_d]
      simp_rw [doubleSimplex_face_eq n]
      exact sub_self _

end Hatcher.Simplex
