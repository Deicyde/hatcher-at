/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Jack McCarthy
-/
import Hatcher.Singular.PointedRelativeNaturality

/-!
# Relative homology with a contractible subspace

The reduced long exact sequence of a pair identifies reduced homology of the
ambient space with relative homology when the subspace is contractible.  The
comparison is the canonical reduced-pair projection, including in degree zero.
-/

noncomputable section

open CategoryTheory Limits ZeroObject

namespace Hatcher.Relative

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- If the subspace of a topological pair is contractible, the canonical map
from reduced ambient homology to relative homology is an isomorphism in every
degree. -/
lemma reducedPairProjection_isIso_of_contractibleSubspace
    (P : TopPair.{w}) [ContractibleSpace P.snd] (R : C) (n : ℕ) :
    IsIso (reducedPairProjection P R n) := by
  cases n with
  | zero =>
      let S := reducedPairZeroSequence P R
      have hS : S.Exact :=
        reducedPairZeroSequence_exact P R (inferInstance : Nonempty P.snd).some
      have hsubspace :
          IsZero ((Hatcher.Reduced.homologyFunctor R 0).obj P.snd) :=
        Hatcher.Reduced.isZero_homology_of_contractible R 0
      have _ : Mono (S.map' 1 2) :=
        (hS.exact 0).mono_g (hsubspace.eq_of_src _ _)
      have _ : Epi (S.map' 1 2) :=
        (hS.exact 1).epi_f ((isZero_zero C).eq_of_tgt _ _)
      change IsIso (S.map' 1 2)
      apply isIso_of_mono_of_epi
  | succ k =>
      let S := reducedPairSequence P R (k + 1) k rfl
      have hS : S.Exact := reducedPairSequence_exact P R (k + 1) k rfl
      have hsubspaceHigh :
          IsZero ((Hatcher.Reduced.homologyFunctor R (k + 1)).obj P.snd) :=
        Hatcher.Reduced.isZero_homology_of_contractible R (k + 1)
      have hsubspaceLow :
          IsZero ((Hatcher.Reduced.homologyFunctor R k).obj P.snd) :=
        Hatcher.Reduced.isZero_homology_of_contractible R k
      have _ : Mono (S.map' 1 2) :=
        (hS.exact 0).mono_g (hsubspaceHigh.eq_of_src _ _)
      have _ : Epi (S.map' 1 2) :=
        (hS.exact 1).epi_f (hsubspaceLow.eq_of_tgt _ _)
      change IsIso (S.map' 1 2)
      apply isIso_of_mono_of_epi

/-- **Hatcher, §2.1 (page 125).** If the subspace of a topological pair is
contractible, reduced homology of the ambient space is canonically isomorphic
to relative homology.  The forward map is the reduced-pair projection from the
long exact sequence. -/
noncomputable def contractibleSubspaceHomologyIso
    (P : TopPair.{w}) [ContractibleSpace P.snd] (R : C) (n : ℕ) :
    (Hatcher.Reduced.homologyFunctor R n).obj P.fst ≅
      (homologyFunctor R n).obj P := by
  let _ : IsIso (reducedPairProjection P R n) :=
    reducedPairProjection_isIso_of_contractibleSubspace P R n
  exact asIso (reducedPairProjection P R n)

@[simp]
lemma contractibleSubspaceHomologyIso_hom
    (P : TopPair.{w}) [ContractibleSpace P.snd] (R : C) (n : ℕ) :
    (contractibleSubspaceHomologyIso P R n).hom =
      reducedPairProjection P R n := by
  rfl

end Hatcher.Relative
