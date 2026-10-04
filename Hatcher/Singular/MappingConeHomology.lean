/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.ContractibleSubspaceRelative
import Hatcher.Singular.MappingConeCoverHomology

/-!
# Relative homology as reduced homology of the mapping cone

Hatcher's arbitrary-pair mapping-cone comparison is the composite of the
base-side cover retraction, binary-cover excision, and the reduced-to-relative
comparison for the contractible cone-side cover member.
-/

noncomputable section

open CategoryTheory Limits

namespace Hatcher.Relative

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- The canonical binary-cover excision map for the mapping cone induces an
isomorphism on relative homology. -/
instance mappingConeExcision_homologyMap_isIso
    (P : TopPair.{w}) (R : C) (n : ℕ) :
    IsIso ((homologyFunctor R n).map (mappingConeExcision P)) := by
  change IsIso ((homologyFunctor R n).map
    (Hatcher.Excision.coverPairHom (mappingConeCoverCondition P)))
  exact Hatcher.Excision.coverHomologyMap_isIso
    (mappingConeCoverCondition P) R n

/-- **Hatcher, §2.1 (page 125).** Relative homology of an arbitrary
topological pair is canonically isomorphic to reduced homology of its mapping
cone. -/
noncomputable def mappingConeHomologyIso
    (P : TopPair.{w}) (R : C) (n : ℕ) :
    (homologyFunctor R n).obj P ≅
      (Hatcher.Reduced.homologyFunctor R n).obj (mappingCone P) := by
  let _ : ContractibleSpace (mappingConeUpperPair P).snd :=
    Hatcher.VanKampen.ConeAttachment.contractibleSpace_upperCover P.map.hom
  exact
    (asIso ((homologyFunctor R n).map
      (mappingConeCoverRetraction P))).symm ≪≫
    asIso ((homologyFunctor R n).map (mappingConeExcision P)) ≪≫
    (contractibleSubspaceHomologyIso (mappingConeUpperPair P) R n).symm

@[simp]
theorem mappingConeHomologyIso_inv
    (P : TopPair.{w}) (R : C) (n : ℕ) :
    (mappingConeHomologyIso P R n).inv =
      reducedPairProjection (mappingConeUpperPair P) R n ≫
        inv ((homologyFunctor R n).map (mappingConeExcision P)) ≫
        (homologyFunctor R n).map (mappingConeCoverRetraction P) := by
  let _ : ContractibleSpace (mappingConeUpperPair P).snd :=
    Hatcher.VanKampen.ConeAttachment.contractibleSpace_upperCover P.map.hom
  change (((asIso ((homologyFunctor R n).map
      (mappingConeCoverRetraction P))).symm ≪≫
    asIso ((homologyFunctor R n).map (mappingConeExcision P)) ≪≫
    (contractibleSubspaceHomologyIso (mappingConeUpperPair P) R n).symm).inv) = _
  rw [Iso.trans_inv, Iso.trans_inv]
  simp only [Iso.symm_inv, asIso_hom, asIso_inv]
  rw [contractibleSubspaceHomologyIso_hom]
  simp only [Category.assoc]

end Hatcher.Relative
