/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.MayerVietoris.ChainComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Exactness of the Mayer–Vietoris chain complex

The binary-cover Mayer–Vietoris chain complex is short exact for arbitrary
subsets of the ambient space.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Simplicial
open scoped Simplicial

namespace Hatcher.MayerVietoris

universe w v u v' u'

variable (C : Type u) [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C] (R : C)
variable {J : Type u'} [Category.{v'} J] [HasColimitsOfShape J (Type w)]

local instance chainComplexFunctor_preservesColimits :
    PreservesColimitsOfShape J ((SSet.chainComplexFunctor.{w} C).obj R) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n => by
    have : PreservesColimitsOfShape J
        ((evaluation SimplexCategoryᵒᵖ (Type w)).obj (Opposite.op ⦋n⦌) ⋙
          sigmaConst.obj R) :=
      comp_preservesColimitsOfShape _ _
    exact preservesColimitsOfShape_of_natIso
      (show (evaluation SimplexCategoryᵒᵖ (Type w)).obj (Opposite.op ⦋n⦌) ⋙
          sigmaConst.obj R ≅
        (SSet.chainComplexFunctor.{w} C).obj R ⋙
          HomologicalComplex.eval C _ n from Iso.refl _)

variable {Y Z : SSet.{w}} (f : Y ⟶ Z)

local instance mono_chainComplexMap [Mono f] : Mono (SSet.chainComplexMap f R) :=
  HomologicalComplex.mono_of_mono_f _ fun _ =>
    inferInstanceAs (Mono ((sigmaConst.obj R).map (f.app _)))

variable {X : TopCat.{w}}

local instance : HasFiniteCoproducts C := hasFiniteCoproducts_of_hasCoproducts C
local instance : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts

/-- **Hatcher, §2.2.** The binary-cover Mayer–Vietoris chain complex is
short exact. -/
theorem chainComplexShortComplex_shortExact (A B : Set X) (R : C) :
    (chainComplexShortComplex A B R).ShortExact := by
  let sq := (smallCoverBicartSq A B).isPushout
  change (sq.map ((SSet.chainComplexFunctor.{w} C).obj R)).shortComplex.ShortExact
  refine
    { exact := (sq.map ((SSet.chainComplexFunctor.{w} C).obj R)).exact_shortComplex
      mono_f := ?_
      epi_g := (sq.map ((SSet.chainComplexFunctor.{w} C).obj R)).epi_shortComplex_g }
  change Mono (biprod.lift (intersectionToLeftChainMap A B R)
    (-intersectionToRightChainMap A B R))
  letI : Mono (intersectionToLeftChainMap A B R) := by
    dsimp [intersectionToLeftChainMap]
    infer_instance
  exact mono_of_mono_fac
    (biprod.lift_fst (intersectionToLeftChainMap A B R)
      (-intersectionToRightChainMap A B R))

end Hatcher.MayerVietoris
