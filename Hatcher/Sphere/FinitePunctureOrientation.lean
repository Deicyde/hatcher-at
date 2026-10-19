/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.FinitePunctureExcision
import Hatcher.Sphere.FiniteFiberDegree

/-!
# The oriented class of a finite-puncture pair

The ordered sphere class projected to the pair with a finite fiber deleted is
the image of the sum of the transported oriented local classes. Its geometric
projections recover the ordered local class at each fiber point; after
normalization, these are the coordinates of the finite homology coproduct.
-/

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set Topology
open scoped BigOperators

namespace Hatcher.Sphere

variable {n : ℕ}
  {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
  {y : TopCat.sphere.{0} n}

/-- The finite sum of the transported ordered local classes in the canonical
source coproduct. The finite indexing instance is obtained internally from the
given finiteness witness. -/
noncomputable def finitePunctureLocalFundamentalClassSum
    (D : FiniteFiberNeighborhoods f y) (hfinite : (fiber f y).Finite)
    (hn : 0 < n) :
    AddCommGrpCat.of ℤ ⟶ ∐ fun i : fiber f y ↦
      (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
        (Hatcher.Relative.puncturedPair (TopCat.of (D.U i))
          ⟨i.1, D.center_mem i⟩) := by
  classical
  letI : Fintype (fiber f y) := finiteFiberFintype hfinite
  exact ∑ i : fiber f y,
    integralSphereNeighborhoodFundamentalClass
        n hn i.1 (D.U i) (D.center_mem i) (D.isOpen_U i) ≫
      Sigma.ι (fun j : fiber f y ↦
        (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
          (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
            ⟨j.1, D.center_mem j⟩)) i

/-- Every finite-biproduct coordinate of the source sum is exactly its
transported ordered local class. No indexing instance is a public hypothesis. -/
theorem finitePunctureLocalFundamentalClassSum_comp_biproduct_projection
    (D : FiniteFiberNeighborhoods f y) (hfinite : (fiber f y).Finite)
    (hn : 0 < n) (x : fiber f y) :
    letI : Fintype (fiber f y) := finiteFiberFintype hfinite
    finitePunctureLocalFundamentalClassSum D hfinite hn ≫
        (biproduct.isoCoproduct (fun j : fiber f y ↦
          (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
            (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
              ⟨j.1, D.center_mem j⟩))).inv ≫
        biproduct.π (fun j : fiber f y ↦
          (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
            (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
              ⟨j.1, D.center_mem j⟩)) x =
      integralSphereNeighborhoodFundamentalClass
        n hn x.1 (D.U x) (D.center_mem x) (D.isOpen_U x) := by
  classical
  let : Fintype (fiber f y) := finiteFiberFintype hfinite
  let H (i : fiber f y) :=
    (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
      (Hatcher.Relative.puncturedPair (TopCat.of (D.U i))
        ⟨i.1, D.center_mem i⟩)
  let c (i : fiber f y) : AddCommGrpCat.of ℤ ⟶ H i :=
    integralSphereNeighborhoodFundamentalClass
      n hn i.1 (D.U i) (D.center_mem i) (D.isOpen_U i)
  have hsum : finitePunctureLocalFundamentalClassSum D hfinite hn ≫
      (biproduct.isoCoproduct H).inv = biproduct.lift c := by
    change (∑ i : fiber f y, c i ≫ Sigma.ι H i) ≫
      (biproduct.isoCoproduct H).inv = biproduct.lift c
    rw [biproduct.isoCoproduct_inv, Preadditive.sum_comp, biproduct.lift_eq]
    simp only [Category.assoc, Sigma.ι_comp_desc]
  change finitePunctureLocalFundamentalClassSum D hfinite hn ≫
    (biproduct.isoCoproduct H).inv ≫ biproduct.π H x = c x
  rw [← Category.assoc, hsum, biproduct.lift_π]

/-- The actual inclusion of complements projects the finite-puncture class
to the ordered local class at the chosen fiber point. This uses no finiteness
or neighborhood witness. -/
@[reassoc]
theorem finitePunctureFundamentalClass_comp_projection
    (hn : 0 < n) (x : fiber f y) :
    finitePunctureFundamentalClass n f y ≫ finitePunctureProjectionMap x n =
      integralSphereLocalFundamentalClass n hn x.1 := by
  let j : AddCommGrpCat.of ℤ ⟶
      (Hatcher.Reduced.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
        (TopCat.sphere.{0} n) :=
    Hatcher.Simplex.doubleSimplexSphereFundamentalClass (AddCommGrpCat.of ℤ) n
  let rP :
      (Hatcher.Reduced.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
          (TopCat.sphere.{0} n) ⟶
        (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
          (Hatcher.Relative.deletedPair (TopCat.sphere.{0} n) (fiber f y)) :=
    Hatcher.Relative.reducedPairProjection
      (Hatcher.Relative.deletedPair (TopCat.sphere.{0} n) (fiber f y))
      (AddCommGrpCat.of ℤ) n
  let rQ :
      (Hatcher.Reduced.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
          (TopCat.sphere.{0} n) ⟶
        (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
          (Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) x.1) :=
    Hatcher.Relative.reducedPairProjection
      (Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) x.1)
      (AddCommGrpCat.of ℤ) n
  let s : End ((Hatcher.Reduced.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
      (TopCat.sphere.{0} n)) :=
    (Hatcher.Reduced.homologyFunctor (AddCommGrpCat.of ℤ) n).map
      (TopPair.Hom.fst (finitePunctureProjectionPairHom x))
  have hs : s = 𝟙 _ :=
    (congrArg (fun g : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n ↦
        (Hatcher.Reduced.homologyFunctor (AddCommGrpCat.of ℤ) n).map g)
      (finitePunctureProjectionPairHom_fst x)).trans
        ((Hatcher.Reduced.homologyFunctor (AddCommGrpCat.of ℤ) n).map_id _)
  have hnat : rP ≫
      (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).map
        (finitePunctureProjectionPairHom x) = s ≫ rQ :=
    Hatcher.Relative.reducedPairProjection_naturality
      (finitePunctureProjectionPairHom x) (AddCommGrpCat.of ℤ) n
  have hprojection : rP ≫
      (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).map
        (finitePunctureProjectionPairHom x) = rQ :=
    hnat.trans ((congrArg (fun m ↦ m ≫ rQ) hs).trans (Category.id_comp rQ))
  change (j ≫ rP) ≫
    (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).map
      (finitePunctureProjectionPairHom x) = j ≫ rQ
  exact (Category.assoc j rP _).trans (congrArg (fun m ↦ j ≫ m) hprojection)

/-- Normalizing the geometric projection transports the finite-puncture
class to the oriented class in the chosen local neighborhood. -/
@[reassoc]
theorem finitePunctureFundamentalClass_comp_normalizedProjection
    (D : FiniteFiberNeighborhoods f y) (hn : 0 < n) (x : fiber f y) :
    finitePunctureFundamentalClass n f y ≫
        finitePunctureNormalizedProjection D n x =
      integralSphereNeighborhoodFundamentalClass
        n hn x.1 (D.U x) (D.center_mem x) (D.isOpen_U x) := by
  let : T2Space (TopCat.sphere.{0} n) :=
    (sphereULiftHomeomorph n).symm.t2Space
  let : IsIso (Hatcher.Relative.localHomologyOpenNeighborhoodMap
      x.1 (D.U x) (D.center_mem x) (AddCommGrpCat.of ℤ) n) :=
    Hatcher.Relative.localHomologyOpenNeighborhoodMap_isIso_of_t1
      x.1 (D.U x) (D.center_mem x) (D.isOpen_U x) (AddCommGrpCat.of ℤ) n
  dsimp only [finitePunctureNormalizedProjection,
    integralSphereNeighborhoodFundamentalClass]
  exact finitePunctureFundamentalClass_comp_projection_assoc hn x _

/-- The diagonal local summand carries its transported orientation to the
ordered ambient local class. -/
@[reassoc]
theorem finitePunctureLocalFundamentalClass_comp_projection_self
    (D : FiniteFiberNeighborhoods f y) (hfinite : (fiber f y).Finite)
    (hn : 0 < n) (x : fiber f y) :
    integralSphereNeighborhoodFundamentalClass
        n hn x.1 (D.U x) (D.center_mem x) (D.isOpen_U x) ≫
        Sigma.ι (fun j : fiber f y ↦
          (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
            (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
              ⟨j.1, D.center_mem j⟩)) x ≫
        (finitePunctureHomologyIso D hfinite n).hom ≫
        finitePunctureProjectionMap x n =
      integralSphereLocalFundamentalClass n hn x.1 := by
  rw [finitePunctureProjection_comp_summand_self D hfinite n x]
  exact integralSphereNeighborhoodFundamentalClass_map
    n hn x.1 (D.U x) (D.center_mem x) (D.isOpen_U x)

/-- Every off-diagonal local class vanishes under the geometric projection. -/
@[reassoc]
theorem finitePunctureLocalFundamentalClass_comp_projection_of_ne
    (D : FiniteFiberNeighborhoods f y) (hfinite : (fiber f y).Finite)
    (hn : 0 < n) (x z : fiber f y) (hzx : z ≠ x) :
    integralSphereNeighborhoodFundamentalClass
        n hn z.1 (D.U z) (D.center_mem z) (D.isOpen_U z) ≫
        Sigma.ι (fun j : fiber f y ↦
          (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
            (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
              ⟨j.1, D.center_mem j⟩)) z ≫
        (finitePunctureHomologyIso D hfinite n).hom ≫
        finitePunctureProjectionMap x n = 0 := by
  rw [finitePunctureProjection_comp_summand_of_ne D hfinite n x z hzx, comp_zero]

/-- **Hatcher, Proposition 2.30 (printed page 136), orientation step.** The
projected ordered sphere class is the image of the finite sum of the ordered
local classes under the canonical finite-puncture homology isomorphism. The
same coordinate argument includes the empty fiber without a separate case. -/
@[reassoc]
theorem finitePunctureFundamentalClass_eq_sum
    (D : FiniteFiberNeighborhoods f y) (hfinite : (fiber f y).Finite)
    (hn : 0 < n) :
    finitePunctureFundamentalClass n f y =
      finitePunctureLocalFundamentalClassSum D hfinite hn ≫
        (finitePunctureHomologyIso D hfinite n).hom := by
  classical
  let : Fintype (fiber f y) := finiteFiberFintype hfinite
  apply finitePunctureHomology_hom_ext D hfinite n
  intro x
  calc
    finitePunctureFundamentalClass n f y ≫
        finitePunctureHomologyProjection D hfinite n x =
        integralSphereNeighborhoodFundamentalClass
          n hn x.1 (D.U x) (D.center_mem x) (D.isOpen_U x) := by
      rw [← finitePunctureNormalizedProjection_eq_homologyProjection D hfinite n x]
      exact finitePunctureFundamentalClass_comp_normalizedProjection D hn x
    _ = (finitePunctureLocalFundamentalClassSum D hfinite hn ≫
        (finitePunctureHomologyIso D hfinite n).hom) ≫
        finitePunctureHomologyProjection D hfinite n x := by
      symm
      rw [finitePunctureHomologyProjection]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact finitePunctureLocalFundamentalClassSum_comp_biproduct_projection
        D hfinite hn x

end Hatcher.Sphere
