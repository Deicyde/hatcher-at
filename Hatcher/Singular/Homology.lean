/-
Hatcher, *Algebraic Topology*, Propositions 2.8 and Corollary 2.11.
-/
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Topology.Homotopy.Equiv

noncomputable section

open AlgebraicTopology CategoryTheory Limits

namespace Hatcher.Singular

universe w v u

section Point

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{0} C] [CategoryWithHomology C]

/-- The zeroth singular homology of a point is the coefficient object. -/
noncomputable def pointHomologyZeroIso (R : C) :
    ((singularHomologyFunctor C 0).obj R).obj (TopCat.of PUnit) ≅ R := by
  letI : PathConnectedSpace PUnit := {
    nonempty := inferInstance
    joined x y := by simpa only [Subsingleton.elim y x] using Joined.refl x }
  exact asIso ((TopCat.of PUnit).singularHomology₀ε R)

/-- **Hatcher, Proposition 2.8 (page 110).** The positive-degree singular
homology of a point vanishes. -/
lemma isZero_pointHomology (R : C) (n : ℕ) (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj (TopCat.of PUnit)) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R (TopCat.of PUnit) hn

/-- **Hatcher, Proposition 2.8 (page 110).** A point has zeroth singular
homology isomorphic to the coefficient object and zero homology in every
positive degree. -/
theorem point_homology (R : C) :
    Nonempty (((singularHomologyFunctor C 0).obj R).obj (TopCat.of PUnit) ≅ R) ∧
      ∀ n : ℕ, n ≠ 0 →
        IsZero (((singularHomologyFunctor C n).obj R).obj (TopCat.of PUnit)) :=
  ⟨⟨pointHomologyZeroIso R⟩, isZero_pointHomology R⟩

end Point

section HomotopyEquiv

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]
  {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Hatcher, Corollary 2.11 (page 111).** A homotopy equivalence induces an
isomorphism on singular homology in every degree. -/
noncomputable def homologyIsoOfHomotopyEquiv
    (e : ContinuousMap.HomotopyEquiv X Y) (R : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of X) ≅
      ((singularHomologyFunctor C n).obj R).obj (TopCat.of Y) where
  hom := ((singularHomologyFunctor C n).obj R).map (TopCat.ofHom e.toFun)
  inv := ((singularHomologyFunctor C n).obj R).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← Functor.map_comp]
    change HomologicalComplex.homologyMap
      (((singularChainComplexFunctor C).obj R).map
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun)) n = 𝟙 _
    calc
      _ = HomologicalComplex.homologyMap
          (((singularChainComplexFunctor C).obj R).map (𝟙 (TopCat.of X))) n :=
        TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
          (f := TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun)
          (g := 𝟙 (TopCat.of X)) e.left_inv.some R n
      _ = 𝟙 _ := by simp
  inv_hom_id := by
    rw [← Functor.map_comp]
    change HomologicalComplex.homologyMap
      (((singularChainComplexFunctor C).obj R).map
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun)) n = 𝟙 _
    calc
      _ = HomologicalComplex.homologyMap
          (((singularChainComplexFunctor C).obj R).map (𝟙 (TopCat.of Y))) n :=
        TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
          (f := TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun)
          (g := 𝟙 (TopCat.of Y)) e.right_inv.some R n
      _ = 𝟙 _ := by simp

/-- The forward morphism is the singular-homology map induced by the given
homotopy equivalence. -/
@[simp]
lemma homologyIsoOfHomotopyEquiv_hom
    (e : ContinuousMap.HomotopyEquiv X Y) (R : C) (n : ℕ) :
    (homologyIsoOfHomotopyEquiv e R n).hom =
      ((singularHomologyFunctor C n).obj R).map (TopCat.ofHom e.toFun) := rfl

end HomotopyEquiv

end Hatcher.Singular
