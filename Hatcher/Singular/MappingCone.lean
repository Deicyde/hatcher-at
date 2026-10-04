/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Excision.BinaryCover
import Hatcher.VanKampen.ConeAttachmentPushout

/-!
# The mapping cone of a topological pair

This file packages the existing explicit single-cone attachment as the
mapping cone of a topological pair.  Its standard two-set open cover gives
the canonical pair map used by binary-cover excision.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Topology

namespace Hatcher.Relative

universe w

/-- The mapping cone of a topological pair, retaining an explicit cone apex
even when the subspace is empty. -/
def mappingCone (P : TopPair.{w}) : TopCat.{w} :=
  TopCat.of (Hatcher.VanKampen.ConeAttachment P.map)

/-- The explicit mapping-cone model is the pushout of the pair embedding and
the retained boundary inclusion into the explicit cone. -/
theorem mappingCone_isPushout (P : TopPair.{w}) :
    IsPushout
      (Hatcher.VanKampen.ConeAttachment.attachingHom
        P.map P.map.hom.continuous)
      (Hatcher.VanKampen.ConeAttachment.coneBoundaryHom P.snd)
      (Hatcher.VanKampen.ConeAttachment.baseHom P.map)
      (Hatcher.VanKampen.ConeAttachment.coneHom
        P.map P.map.hom.continuous) :=
  Hatcher.VanKampen.ConeAttachment.isPushout_coneAttachment
    P.map P.map.hom.continuous

/-- The mapping cone paired with the cone-side member of its standard open
cover. -/
def mappingConeUpperPair (P : TopPair.{w}) : TopPair.{w} :=
  TopPair.ofSubset
    (X := TopCat.of (Hatcher.VanKampen.ConeAttachment P.map))
    (Hatcher.VanKampen.ConeAttachment.upperCover P.map)

/-- The base-side member of the standard mapping-cone cover, paired with its
intersection with the cone-side member. -/
def mappingConeCoverPair (P : TopPair.{w}) : TopPair.{w} :=
  TopPair.of
    (TopCat.ofHom
      (ContinuousMap.inclusion
        (Set.inter_subset_right :
          Hatcher.VanKampen.ConeAttachment.upperCover P.map ∩
              Hatcher.VanKampen.ConeAttachment.lowerCover P.map ⊆
            Hatcher.VanKampen.ConeAttachment.lowerCover P.map)))
    (IsEmbedding.inclusion
      (Set.inter_subset_right :
        Hatcher.VanKampen.ConeAttachment.upperCover P.map ∩
            Hatcher.VanKampen.ConeAttachment.lowerCover P.map ⊆
          Hatcher.VanKampen.ConeAttachment.lowerCover P.map))

/-- The upper and lower members form an interior cover of the mapping cone,
in the orientation used by binary-cover excision. -/
theorem mappingConeCoverCondition (P : TopPair.{w}) :
    Hatcher.Excision.CoverCondition
      (X := TopCat.of (Hatcher.VanKampen.ConeAttachment P.map))
      (Hatcher.VanKampen.ConeAttachment.upperCover P.map)
      (Hatcher.VanKampen.ConeAttachment.lowerCover P.map) where
  union_interior := by
    rw [(Hatcher.VanKampen.ConeAttachment.isOpen_upperCover P.map).interior_eq,
      (Hatcher.VanKampen.ConeAttachment.isOpen_lowerCover P.map).interior_eq]
    simpa [Set.union_comm] using
      Hatcher.VanKampen.ConeAttachment.lowerCover_union_upperCover P.map

/-- The canonical excision inclusion from the base-side cover pair to the
mapping cone relative to its cone-side cover member. -/
def mappingConeExcision (P : TopPair.{w}) :
    mappingConeCoverPair P ⟶ mappingConeUpperPair P :=
  Hatcher.Excision.coverPairHom (mappingConeCoverCondition P)

end Hatcher.Relative
