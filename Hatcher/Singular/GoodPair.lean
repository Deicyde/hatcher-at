/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Topology.StrongDeformationRetract
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Category.TopPair

/-!
# Good pairs

This file packages Hatcher's definition of a good topological pair.  A good
pair consists of a nonempty closed subspace which is a strong deformation
retract of a neighborhood in the ambient space.
-/

noncomputable section

open CategoryTheory Set Topology

namespace Hatcher.Relative

universe u

/-- The map from the subspace of a topological pair into a set containing its
image. -/
def goodPairNeighborhoodInclusion (P : TopPair.{u}) (V : Set P.fst)
    (hV : Set.range P.map ⊆ V) : C(P.snd, V) where
  toFun a := ⟨P.map a, hV ⟨a, rfl⟩⟩
  continuous_toFun := P.map.hom.continuous.subtype_mk _

/-- The induced inclusion into a neighborhood is a topological embedding. -/
theorem goodPairNeighborhoodInclusion_isEmbedding (P : TopPair.{u})
    (V : Set P.fst) (hV : Set.range P.map ⊆ V) :
    IsEmbedding (goodPairNeighborhoodInclusion P V hV) :=
  P.isEmbedding_map.codRestrict V (fun a ↦ hV ⟨a, rfl⟩)

/-- Chosen witness data that a topological pair is good in Hatcher's sense. -/
structure GoodPairData (P : TopPair.{u}) where
  /-- The subspace is nonempty. -/
  nonempty : Nonempty P.snd
  /-- The image of the subspace is closed in the ambient space. -/
  isClosed_range : IsClosed (Set.range P.map)
  /-- A neighborhood of the embedded subspace. It need not itself be open. -/
  V : Set P.fst
  /-- The chosen set contains the embedded subspace in its interior. -/
  range_subset_interior : Set.range P.map ⊆ interior V
  /-- The chosen neighborhood strongly deformation retracts onto the embedded
  subspace. -/
  strongDeformationRetract :
    Hatcher.StrongDeformationRetract
      (goodPairNeighborhoodInclusion P V
        (range_subset_interior.trans interior_subset))

/-- A topological pair is good when it admits Hatcher's witness data. -/
def IsGoodPair (P : TopPair.{u}) : Prop :=
  Nonempty (GoodPairData P)

/-- The object property of being a good topological pair. -/
def goodPairProperty : ObjectProperty TopPair.{u} :=
  IsGoodPair

/-- The full subcategory of good topological pairs. Its morphisms are ordinary
morphisms of topological pairs and do not preserve chosen witness data. -/
abbrev GoodPair : Type (u + 1) :=
  goodPairProperty.FullSubcategory

/-- The inclusion of good pairs into all topological pairs. -/
abbrev goodPairForget : GoodPair.{u} ⥤ TopPair.{u} :=
  goodPairProperty.ι

end Hatcher.Relative
