/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.PointedRelative
import Hatcher.Singular.ReducedRelative

/-!
# Relative homology in a contractible ambient space

The reduced long exact sequence identifies relative homology of `(X,A)` with
the shifted reduced homology of `A` when `X` is contractible.
-/

noncomputable section

open CategoryTheory Limits ZeroObject

namespace Hatcher.Relative

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- If the ambient space of a pair is contractible, the connecting morphism
from relative homology to shifted reduced subspace homology is an isomorphism. -/
lemma reducedPairConnecting_isIso_of_contractibleAmbient
    (P : TopPair.{w}) [ContractibleSpace P.fst] (R : C)
    (n m : ℕ) (h : m + 1 = n) :
    IsIso (reducedPairConnecting P R n m h) := by
  let S := reducedPairSequence P R n m h
  have hS : S.Exact := reducedPairSequence_exact P R n m h
  have hAmbientHigh :
      IsZero ((Hatcher.Reduced.homologyFunctor R n).obj P.fst) :=
    Hatcher.Reduced.isZero_homology_of_contractible R n
  have hAmbientLow :
      IsZero ((Hatcher.Reduced.homologyFunctor R m).obj P.fst) :=
    Hatcher.Reduced.isZero_homology_of_contractible R m
  have _ : Mono (S.map' 2 3) :=
    (hS.exact 1).mono_g (hAmbientHigh.eq_of_src _ _)
  have _ : Epi (S.map' 2 3) :=
    (hS.exact 2).epi_f (hAmbientLow.eq_of_tgt _ _)
  change IsIso (S.map' 2 3)
  apply isIso_of_mono_of_epi

/-- **Hatcher, §2.1 (page 126).** In a contractible ambient space, relative
homology is canonically the shifted reduced homology of the subspace. The
forward map is the connecting morphism in the reduced pair sequence. -/
noncomputable def contractibleAmbientRelativeHomologyIso
    (P : TopPair.{w}) [ContractibleSpace P.fst] (R : C)
    (n m : ℕ) (h : m + 1 = n) :
    (homologyFunctor R n).obj P ≅
      (Hatcher.Reduced.homologyFunctor R m).obj P.snd := by
  let _ : IsIso (reducedPairConnecting P R n m h) :=
    reducedPairConnecting_isIso_of_contractibleAmbient P R n m h
  exact asIso (reducedPairConnecting P R n m h)

@[simp]
theorem contractibleAmbientRelativeHomologyIso_hom
    (P : TopPair.{w}) [ContractibleSpace P.fst] (R : C)
    (n m : ℕ) (h : m + 1 = n) :
    (contractibleAmbientRelativeHomologyIso P R n m h).hom =
      reducedPairConnecting P R n m h := by
  rfl

/-- For a nonempty subspace of a contractible ambient space, relative
homology in degree zero vanishes. -/
theorem isZero_relativeHomology_zero_of_contractibleAmbient
    (P : TopPair.{w}) [ContractibleSpace P.fst] (R : C) (x : P.snd) :
    IsZero ((homologyFunctor R 0).obj P) := by
  let S := reducedPairZeroSequence P R
  have hS : S.Exact := reducedPairZeroSequence_exact P R x
  have hAmbient :
      IsZero ((Hatcher.Reduced.homologyFunctor R 0).obj P.fst) :=
    Hatcher.Reduced.isZero_homology_of_contractible R 0
  let f := S.map' 1 2
  exact @IsZero.of_epi _ _ _ _ _ f
    ((hS.exact 1).epi_f ((isZero_zero C).eq_of_tgt _ _)) hAmbient

end Hatcher.Relative
