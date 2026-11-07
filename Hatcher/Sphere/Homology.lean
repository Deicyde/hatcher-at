/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.HomologyRecurrence
import Hatcher.Sphere.ZeroSphereHomology
import Mathlib.Algebra.Category.Grp.Abelian
import Hatcher.VanKampen.ConeAttachmentDisk
import Hatcher.Singular.ContractibleAmbientRelative
import Hatcher.Singular.GoodPairPointQuotientSequenceNaturality

/-!
# Reduced homology of spheres

The direct calculation for the zero-sphere and the suspension recurrence
compute reduced singular homology in every sphere dimension.
-/

noncomputable section

open CategoryTheory Limits

namespace Hatcher.Sphere

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]

/-- **Hatcher, Corollary 2.14 (page 114).** Reduced homology of the
`n`-sphere is the coefficient object in degree `n` and vanishes in every
other degree.  The diagonal isomorphism is returned under `Nonempty` rather
than choosing an orientation. -/
theorem reducedHomology_sphere (R : C) (n : ℕ) :
    Nonempty
        ((Hatcher.Reduced.homologyFunctor.{w} R n).obj
          (TopCat.sphere.{w} n) ≅ R) ∧
      ∀ i, i ≠ n →
        IsZero ((Hatcher.Reduced.homologyFunctor.{w} R i).obj
          (TopCat.sphere.{w} n)) := by
  induction n with
  | zero =>
      exact reducedHomology_sphere_zero R
  | succ n ih =>
      have hSucc := reducedHomology_sphereSucc R n
      constructor
      · obtain ⟨eSucc⟩ := hSucc.1 n
        obtain ⟨eDiag⟩ := ih.1
        exact ⟨eSucc ≪≫ eDiag⟩
      · intro i hi
        cases i with
        | zero =>
            exact hSucc.2
        | succ i =>
            have hi' : i ≠ n := by
              intro h
              apply hi
              rw [h]
            obtain ⟨eSucc⟩ := hSucc.1 i
            exact (ih.2 i hi').of_iso eSucc

/-- The integral specialization of the reduced homology calculation for
spheres, as displayed in Hatcher's Corollary 2.14. -/
theorem reducedHomology_sphere_int (n : ℕ) :
    Nonempty
        ((Hatcher.Reduced.homologyFunctor.{0}
            (AddCommGrpCat.of ℤ) n).obj
          (TopCat.sphere.{0} n) ≅ AddCommGrpCat.of ℤ) ∧
      ∀ i, i ≠ n →
        IsZero ((Hatcher.Reduced.homologyFunctor.{0}
          (AddCommGrpCat.of ℤ) i).obj (TopCat.sphere.{0} n)) :=
  reducedHomology_sphere (C := AddCommGrpCat.{0})
    (AddCommGrpCat.of ℤ) n

end Hatcher.Sphere

namespace Hatcher.Sphere

open CategoryTheory
open Hatcher.Relative

/-- The actual retained sphere cone-base pair, with its proved good-pair property. -/
def sphereConeGoodPair (n : ℕ) : Hatcher.Relative.GoodPair.{u} :=
  ⟨sphereConePair.{u} n, (sphere_cone_geometry n).1⟩

/-- The canonical integral suspension boundary isomorphism is reduced homology
of the actual inverse quotient-sphere homeomorphism, followed by the
quotient-to-relative comparison and the actual cone-pair connecting map.
It includes the reduced degree-zero target when `n = 0`. -/
def sphereSuspensionBoundaryIso (n : ℕ) :
    (Hatcher.Reduced.homologyFunctor.{0}
      (AddCommGrpCat.of ℤ) (n + 1)).obj (TopCat.sphere.{0} (n + 1)) ≅
    (Hatcher.Reduced.homologyFunctor.{0}
      (AddCommGrpCat.of ℤ) n).obj (TopCat.sphere.{0} n) := by
  let : ContractibleSpace (sphereConePair.{0} n).fst :=
    (sphere_cone_geometry n).2.2.1
  exact (Hatcher.Reduced.homologyFunctor.{0}
    (AddCommGrpCat.of ℤ) (n + 1)).mapIso
      (TopCat.isoOfHomeo (sphereConeQuotientHomeomorph.{0} n)).symm ≪≫
    ((goodPairPointQuotientRelativeHomologyNatIso
      (AddCommGrpCat.of ℤ) (n + 1)).app (sphereConeGoodPair.{0} n)).symm ≪≫
    contractibleAmbientRelativeHomologyIso
      (sphereConePair.{0} n) (AddCommGrpCat.of ℤ) (n + 1) n rfl

/-- The forward suspension boundary map is the specified canonical composite. -/
theorem sphere_suspension_boundary_iso_hom (n : ℕ) :
    (sphereSuspensionBoundaryIso n).hom =
      (Hatcher.Reduced.homologyFunctor.{0}
        (AddCommGrpCat.of ℤ) (n + 1)).map
          (TopCat.isoOfHomeo (sphereConeQuotientHomeomorph.{0} n)).inv ≫
        (goodPairPointQuotientRelativeHomologyNatIso
          (AddCommGrpCat.of ℤ) (n + 1)).inv.app (sphereConeGoodPair.{0} n) ≫
        reducedPairConnecting
          (sphereConePair.{0} n) (AddCommGrpCat.of ℤ) (n + 1) n rfl := by
  simp only [sphereSuspensionBoundaryIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv, contractibleAmbientRelativeHomologyIso_hom,
    Category.assoc]

private theorem sphere_suspension_inverse_quotient_square (n : ℕ)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    sphereSuspensionMap n f ≫
        (TopCat.isoOfHomeo (sphereConeQuotientHomeomorph.{0} n)).inv =
      (TopCat.isoOfHomeo (sphereConeQuotientHomeomorph.{0} n)).inv ≫
        pointQuotientMap (sphereConePairMap n f) := by
  ext y
  change (sphereConeQuotientHomeomorph.{0} n).symm
      (sphereConeQuotientHomeomorph.{0} n
        (pointQuotientMap (sphereConePairMap n f)
          ((sphereConeQuotientHomeomorph.{0} n).symm y))) =
    pointQuotientMap (sphereConePairMap n f)
      ((sphereConeQuotientHomeomorph.{0} n).symm y)
  exact (sphereConeQuotientHomeomorph.{0} n).symm_apply_apply _

/-- **Hatcher, Proposition 2.33 (printed page 137).** The actual integral
suspension boundary isomorphism intertwines the induced suspension and sphere
maps, in every dimension including zero and for arbitrary continuous maps. -/
theorem sphere_suspension_boundary_naturality (n : ℕ)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    (Hatcher.Reduced.homologyFunctor.{0}
      (AddCommGrpCat.of ℤ) (n + 1)).map (sphereSuspensionMap n f) ≫
        (sphereSuspensionBoundaryIso n).hom =
      (sphereSuspensionBoundaryIso n).hom ≫
        (Hatcher.Reduced.homologyFunctor.{0}
          (AddCommGrpCat.of ℤ) n).map f := by
  let H := Hatcher.Reduced.homologyFunctor.{0} (AddCommGrpCat.of ℤ) (n + 1)
  let L := Hatcher.Reduced.homologyFunctor.{0} (AddCommGrpCat.of ℤ) n
  let e := TopCat.isoOfHomeo (sphereConeQuotientHomeomorph.{0} n)
  let δ : H.obj (pointQuotient (sphereConePair.{0} n)) ⟶
      L.obj (TopCat.sphere.{0} n) :=
    goodPairPointQuotientConnecting
      (sphereConeGoodPair.{0} n) (AddCommGrpCat.of ℤ) (n + 1) n rfl
  have hΔ : (sphereSuspensionBoundaryIso n).hom = H.map e.inv ≫ δ := by
    exact sphere_suspension_boundary_iso_hom n
  have hTop : H.map (sphereSuspensionMap n f) ≫ H.map e.inv =
      H.map e.inv ≫ H.map (pointQuotientMap (sphereConePairMap n f)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg H.map (sphere_suspension_inverse_quotient_square n f)
  let g : sphereConeGoodPair.{0} n ⟶ sphereConeGoodPair.{0} n :=
    ObjectProperty.homMk (sphereConePairMap n f)
  have hδ : δ ≫ L.map f =
      H.map (pointQuotientMap (sphereConePairMap n f)) ≫ δ := by
    exact goodPairPointQuotientConnecting_naturality
      g (AddCommGrpCat.of ℤ) (n + 1) n rfl
  rw [hΔ]
  change H.map (sphereSuspensionMap n f) ≫ (H.map e.inv ≫ δ) =
    (H.map e.inv ≫ δ) ≫ L.map f
  exact (Category.assoc (H.map (sphereSuspensionMap n f)) (H.map e.inv) δ).symm.trans
    ((congrArg (fun t => t ≫ δ) hTop).trans
      ((Category.assoc (H.map e.inv)
          (H.map (pointQuotientMap (sphereConePairMap n f))) δ).trans
        ((congrArg (fun t => H.map e.inv ≫ t) hδ.symm).trans
          (Category.assoc (H.map e.inv) δ (L.map f)).symm)))

end Hatcher.Sphere
