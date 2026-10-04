/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.Homology
import Hatcher.Singular.MappingCone
import Hatcher.Singular.RelativeIsomorphism
import Hatcher.VanKampen.ConeAttachmentDeformation
import Hatcher.VanKampen.ConeAttachmentIntersection

/-!
# Relative homology of the base-side mapping-cone cover

The base-side member of the standard mapping-cone cover retracts to the
ambient space of the original pair, while the cover intersection projects to
its subspace.  These maps commute strictly with the pair embeddings and induce
an isomorphism on relative homology.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Set Topology
open scoped unitInterval ContinuousMap

namespace Hatcher.Relative

universe w v u

private abbrev mappingConeCoverIntersection (P : TopPair.{w}) :=
  ↥(Hatcher.VanKampen.ConeAttachment.upperCover P.map ∩
    Hatcher.VanKampen.ConeAttachment.lowerCover P.map)

private noncomputable def mappingConeCoverIntersectionSwap
    (P : TopPair.{w}) :
    mappingConeCoverIntersection P ≃ₜ
      ↥(Hatcher.VanKampen.ConeAttachment.lowerCover P.map ∩
        Hatcher.VanKampen.ConeAttachment.upperCover P.map) :=
  Homeomorph.setCongr (Set.inter_comm _ _)

/-- The cover intersection, in the order used by the mapping-cone pair, is
the explicit open interior cylinder on the subspace of the original pair. -/
noncomputable def mappingConeCoverIntersectionCylinderHomeomorph
    (P : TopPair.{w}) :
    mappingConeCoverIntersection P ≃ₜ
      P.snd × Set.Ioo (0 : I) 1 :=
  (mappingConeCoverIntersectionSwap P).trans
    (Hatcher.VanKampen.ConeAttachment.interiorCylinderHomeomorphCoverIntersection
      P.map).symm

@[simp]
lemma mappingConeCoverIntersectionCylinderHomeomorph_symm_coe
    (P : TopPair.{w}) (p : P.snd × Set.Ioo (0 : I) 1) :
    (((mappingConeCoverIntersectionCylinderHomeomorph P).symm p :
        mappingConeCoverIntersection P) :
      Hatcher.VanKampen.ConeAttachment P.map) =
      Hatcher.VanKampen.ConeAttachment.cylinder P.map p.1 p.2 := by
  rfl

/-- Projection of the mapping-cone cover intersection to the subspace of the
original pair.  In the interior-cylinder coordinates it is first projection. -/
noncomputable def mappingConeCoverIntersectionProjection
    (P : TopPair.{w}) :
    C(mappingConeCoverIntersection P, P.snd) where
  toFun z := (mappingConeCoverIntersectionCylinderHomeomorph P z).1
  continuous_toFun := continuous_fst.comp
    (mappingConeCoverIntersectionCylinderHomeomorph P).continuous

@[simp]
lemma mappingConeCoverIntersectionProjection_symm_apply
    (P : TopPair.{w}) (p : P.snd × Set.Ioo (0 : I) 1) :
    mappingConeCoverIntersectionProjection P
        ((mappingConeCoverIntersectionCylinderHomeomorph P).symm p) =
      p.1 := by
  simp [mappingConeCoverIntersectionProjection]

private def interiorMidpoint : I := ⟨(1 : ℝ) / 2, by norm_num⟩

private theorem interiorMidpoint_pos : 0 < interiorMidpoint := by
  change (0 : ℝ) < 1 / 2
  norm_num

private theorem interiorMidpoint_lt_one : interiorMidpoint < 1 := by
  change (1 : ℝ) / 2 < 1
  norm_num

private def interiorMidpoint' : Set.Ioo (0 : I) 1 :=
  ⟨interiorMidpoint, interiorMidpoint_pos, interiorMidpoint_lt_one⟩

private theorem convexComb_pos {a b : I} (ha : 0 < a) (hb : 0 < b)
    (t : I) : 0 < Set.Icc.convexComb a b t := by
  rcases le_total a b with hab | hba
  · exact lt_of_lt_of_le ha (Set.Icc.le_convexComb hab t)
  · have h := Set.Icc.le_convexComb hba (unitInterval.symm t)
    rw [Set.Icc.convexComb_symm] at h
    exact lt_of_lt_of_le hb h

private theorem convexComb_lt_one {a b : I} (ha : a < 1) (hb : b < 1)
    (t : I) : Set.Icc.convexComb a b t < 1 := by
  rcases le_total a b with hab | hba
  · exact lt_of_le_of_lt (Set.Icc.convexComb_le hab t) hb
  · have h := Set.Icc.convexComb_le hba (unitInterval.symm t)
    rw [Set.Icc.convexComb_symm] at h
    exact lt_of_le_of_lt h ha

private def contractInteriorInterval
    (t : I) (x : Set.Ioo (0 : I) 1) : Set.Ioo (0 : I) 1 :=
  ⟨Set.Icc.convexComb interiorMidpoint x.1 t,
    convexComb_pos interiorMidpoint_pos x.2.1 t,
    convexComb_lt_one interiorMidpoint_lt_one x.2.2 t⟩

private theorem continuous_contractInteriorInterval :
    Continuous fun p : I × Set.Ioo (0 : I) 1 ↦
      contractInteriorInterval p.1 p.2 := by
  apply Continuous.subtype_mk
  exact Set.Icc.continuous_convexComb_prod.comp
    (continuous_const.prodMk
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst))

private def interiorCylinderProjection
    (T : Type*) [TopologicalSpace T] :
    C(T × Set.Ioo (0 : I) 1, T) :=
  ⟨Prod.fst, continuous_fst⟩

private def interiorCylinderMidpointInclusion
    (T : Type*) [TopologicalSpace T] :
    C(T, T × Set.Ioo (0 : I) 1) :=
  ⟨fun x ↦ (x, interiorMidpoint'),
    continuous_id.prodMk continuous_const⟩

private def interiorCylinderContraction
    (T : Type*) [TopologicalSpace T] :
    ((interiorCylinderMidpointInclusion T).comp
        (interiorCylinderProjection T)).Homotopy
      (ContinuousMap.id (T × Set.Ioo (0 : I) 1)) where
  toFun p := (p.2.1, contractInteriorInterval p.1 p.2.2)
  continuous_toFun :=
    (continuous_fst.comp continuous_snd).prodMk
      (continuous_contractInteriorInterval.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  map_zero_left p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [contractInteriorInterval, interiorCylinderMidpointInclusion,
        interiorCylinderProjection, interiorMidpoint', interiorMidpoint]
  map_one_left p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [contractInteriorInterval]

private def interiorCylinderHomotopyEquivBase
    (T : Type*) [TopologicalSpace T] :
    T × Set.Ioo (0 : I) 1 ≃ₕ T where
  toFun := interiorCylinderProjection T
  invFun := interiorCylinderMidpointInclusion T
  left_inv := ⟨interiorCylinderContraction T⟩
  right_inv := by
    have h : (interiorCylinderProjection T).comp
        (interiorCylinderMidpointInclusion T) = ContinuousMap.id T := by
      ext x
      rfl
    rw [h]

/-- The mapping-cone cover intersection is homotopy equivalent to the
original subspace, with forward map exactly the explicit cylinder
projection. -/
noncomputable def mappingConeCoverIntersectionHomotopyEquiv
    (P : TopPair.{w}) :
    mappingConeCoverIntersection P ≃ₕ P.snd :=
  (mappingConeCoverIntersectionCylinderHomeomorph P).toHomotopyEquiv.trans
    (interiorCylinderHomotopyEquivBase P.snd)

@[simp]
lemma mappingConeCoverIntersectionHomotopyEquiv_toFun
    (P : TopPair.{w}) :
    (mappingConeCoverIntersectionHomotopyEquiv P).toFun =
      mappingConeCoverIntersectionProjection P :=
  rfl

private theorem mappingConeCoverRetraction_comm (P : TopPair.{w}) :
    TopCat.ofHom (mappingConeCoverIntersectionProjection P) ≫ P.map =
      (mappingConeCoverPair P).map ≫
        TopCat.ofHom
          (Hatcher.VanKampen.ConeAttachment.lowerRetraction P.map.hom) := by
  ext z
  let e := mappingConeCoverIntersectionCylinderHomeomorph P
  let p := e z
  have hz : z = e.symm p := (e.symm_apply_apply z).symm
  rw [hz]
  change P.map (mappingConeCoverIntersectionProjection P (e.symm p)) =
    Hatcher.VanKampen.ConeAttachment.lowerRetraction P.map.hom
      ⟨((e.symm p : mappingConeCoverIntersection P) :
          Hatcher.VanKampen.ConeAttachment P.map),
        (e.symm p).property.2⟩
  rw [mappingConeCoverIntersectionProjection_symm_apply]
  have harg :
      (⟨((e.symm p : mappingConeCoverIntersection P) :
          Hatcher.VanKampen.ConeAttachment P.map),
        (e.symm p).property.2⟩ :
        Hatcher.VanKampen.ConeAttachment.lowerCover P.map) =
      ⟨Hatcher.VanKampen.ConeAttachment.cylinder P.map p.1 p.2,
        by
          change Sum.inr (Sum.inr (p.1, (p.2 : I))) ∈
            Hatcher.VanKampen.ConeAttachment.quotientMk P.map ⁻¹'
              Hatcher.VanKampen.ConeAttachment.lowerCover P.map
          rw [Hatcher.VanKampen.ConeAttachment.quotientMk_preimage_lowerCover]
          exact p.2.2.1⟩ := by
    apply Subtype.ext
    exact mappingConeCoverIntersectionCylinderHomeomorph_symm_coe P p
  rw [harg]
  exact (Hatcher.VanKampen.ConeAttachment.lowerRetraction_apply_cylinder
    P.map.hom p.1 p.2 p.2.2.1).symm

/-- Retraction of the base-side mapping-cone cover pair to the original
topological pair. -/
noncomputable def mappingConeCoverRetraction (P : TopPair.{w}) :
    mappingConeCoverPair P ⟶ P :=
  TopPair.ofHom
    (TopCat.ofHom
      (Hatcher.VanKampen.ConeAttachment.lowerRetraction P.map.hom))
    (TopCat.ofHom (mappingConeCoverIntersectionProjection P))
    (mappingConeCoverRetraction_comm P)

@[simp]
lemma mappingConeCoverRetraction_fst (P : TopPair.{w}) :
    TopPair.Hom.fst (mappingConeCoverRetraction P) =
      TopCat.ofHom
        (Hatcher.VanKampen.ConeAttachment.lowerRetraction P.map.hom) :=
  rfl

@[simp]
lemma mappingConeCoverRetraction_snd (P : TopPair.{w}) :
    TopPair.Hom.snd (mappingConeCoverRetraction P) =
      TopCat.ofHom (mappingConeCoverIntersectionProjection P) :=
  rfl

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- The canonical mapping-cone cover retraction induces an isomorphism on
relative homology in every degree, including degree zero. -/
instance mappingConeCoverRetraction_homologyMap_isIso
    (P : TopPair.{w}) (R : C) (n : ℕ) :
    IsIso ((homologyFunctor R n).map (mappingConeCoverRetraction P)) := by
  apply homologyMap_isIso_of_components
  · intro k
    change IsIso (((singularHomologyFunctor C k).obj R).map
      (TopCat.ofHom (mappingConeCoverIntersectionProjection P)))
    rw [← mappingConeCoverIntersectionHomotopyEquiv_toFun]
    exact (Hatcher.Singular.homologyIsoOfHomotopyEquiv
      (mappingConeCoverIntersectionHomotopyEquiv P) R k).isIso_hom
  · intro k
    change IsIso (((singularHomologyFunctor C k).obj R).map
      (TopCat.ofHom
        (Hatcher.VanKampen.ConeAttachment.lowerRetraction P.map.hom)))
    exact (Hatcher.Singular.homologyIsoOfHomotopyEquiv
      (Hatcher.VanKampen.ConeAttachment.lowerStrongDeformationRetract
        P.map.hom).toHomotopyEquiv R k).isIso_hom

end Hatcher.Relative
