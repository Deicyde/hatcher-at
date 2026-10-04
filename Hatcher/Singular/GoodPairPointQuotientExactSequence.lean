/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.GoodPairPointQuotientNaturality

/-!
# The reduced exact sequence of a good-pair point quotient

For a good pair `(X, A)`, the canonical comparison from relative homology to
reduced homology of `X/A` transports the reduced long exact sequence of the
pair to Hatcher's quotient sequence.  The maps from `X` to `X/A` are written
literally as the maps induced by the canonical point-quotient projection.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits ZeroObject

namespace Hatcher.Relative

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- The connecting morphism in Hatcher's good-pair quotient sequence.  It is
the reduced-pair connecting morphism transported backwards through the
canonical Proposition 2.22 comparison. -/
noncomputable def goodPairPointQuotientConnecting
    (P : GoodPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    (Hatcher.Reduced.homologyFunctor R n).obj (pointQuotient P.obj) ⟶
      (Hatcher.Reduced.homologyFunctor R m).obj P.obj.snd :=
  (goodPairPointQuotientRelativeHomologyNatIso R n).inv.app P ≫
    reducedPairConnecting P.obj R n m h

/-- Six consecutive terms in Hatcher's reduced exact sequence
`H̃_n(A) ⟶ H̃_n(X) ⟶ H̃_n(X/A) ⟶ H̃_m(A) ⟶
H̃_m(X) ⟶ H̃_m(X/A)` for a good pair and `m + 1 = n`.

Both arrows into quotient homology are, definitionally, induced by the
canonical point-quotient projection. -/
noncomputable def goodPairPointQuotientSequence
    (P : GoodPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    ComposableArrows C 5 :=
  ComposableArrows.mk₅
    ((Hatcher.Reduced.homologyFunctor R n).map P.obj.map)
    ((Hatcher.Reduced.homologyFunctor R n).map
      (pointQuotientProjection P.obj))
    (goodPairPointQuotientConnecting P R n m h)
    ((Hatcher.Reduced.homologyFunctor R m).map P.obj.map)
    ((Hatcher.Reduced.homologyFunctor R m).map
      (pointQuotientProjection P.obj))

/-- The upper ambient-to-quotient arrow is literally induced by the canonical
projection `X ⟶ X/A`. -/
@[simp]
lemma goodPairPointQuotientSequence_map_one_two
    (P : GoodPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    (goodPairPointQuotientSequence P R n m h).map' 1 2 =
      (Hatcher.Reduced.homologyFunctor R n).map
        (pointQuotientProjection P.obj) := by
  rfl

/-- The middle arrow is the transported reduced-pair connecting morphism. -/
@[simp]
lemma goodPairPointQuotientSequence_map_two_three
    (P : GoodPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    (goodPairPointQuotientSequence P R n m h).map' 2 3 =
      goodPairPointQuotientConnecting P R n m h := by
  rfl

/-- The lower ambient-to-quotient arrow is literally induced by the canonical
projection `X ⟶ X/A`. -/
@[simp]
lemma goodPairPointQuotientSequence_map_four_five
    (P : GoodPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    (goodPairPointQuotientSequence P R n m h).map' 4 5 =
      (Hatcher.Reduced.homologyFunctor R m).map
        (pointQuotientProjection P.obj) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The reduced-pair sequence and the good-pair point-quotient sequence differ
only by the canonical Proposition 2.22 comparisons at the relative terms. -/
noncomputable def reducedPairSequenceIsoGoodPairPointQuotientSequence
    (P : GoodPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    reducedPairSequence P.obj R n m h ≅
      goodPairPointQuotientSequence P R n m h :=
  ComposableArrows.isoMk₅
    (Iso.refl _) (Iso.refl _)
    ((goodPairPointQuotientRelativeHomologyNatIso R n).app P)
    (Iso.refl _) (Iso.refl _)
    ((goodPairPointQuotientRelativeHomologyNatIso R m).app P)
    (by
      change
        (Hatcher.Reduced.homologyFunctor R n).map P.obj.map ≫ 𝟙 _ =
          𝟙 _ ≫ (Hatcher.Reduced.homologyFunctor R n).map P.obj.map
      simp)
    (by
      change
        reducedPairProjection P.obj R n ≫
            (goodPairPointQuotientRelativeHomologyNatIso R n).hom.app P =
          𝟙 _ ≫ (Hatcher.Reduced.homologyFunctor R n).map
            (pointQuotientProjection P.obj)
      simpa only [Category.id_comp] using
        reducedPairProjection_comp_goodPairPointQuotientRelativeHomologyNatIso_hom_app
          P R n)
    (by
      rw [reducedPairSequence_map_two_three]
      change
        reducedPairConnecting P.obj R n m h ≫ 𝟙 _ =
          ((goodPairPointQuotientRelativeHomologyNatIso R n).app P).hom ≫
            ((goodPairPointQuotientRelativeHomologyNatIso R n).app P).inv ≫
              reducedPairConnecting P.obj R n m h
      rw [Category.comp_id]
      exact (Iso.hom_inv_id_assoc
        ((goodPairPointQuotientRelativeHomologyNatIso R n).app P)
        (reducedPairConnecting P.obj R n m h)).symm)
    (by
      change
        (Hatcher.Reduced.homologyFunctor R m).map P.obj.map ≫ 𝟙 _ =
          𝟙 _ ≫ (Hatcher.Reduced.homologyFunctor R m).map P.obj.map
      simp)
    (by
      change
        reducedPairProjection P.obj R m ≫
            (goodPairPointQuotientRelativeHomologyNatIso R m).hom.app P =
          𝟙 _ ≫ (Hatcher.Reduced.homologyFunctor R m).map
            (pointQuotientProjection P.obj)
      simpa only [Category.id_comp] using
        reducedPairProjection_comp_goodPairPointQuotientRelativeHomologyNatIso_hom_app
          P R m)

/-- **Hatcher, Theorem 2.13 (printed page 114).** Every adjacent-degree
six-term window in the reduced good-pair quotient sequence is exact. -/
theorem goodPairPointQuotientSequence_exact
    (P : GoodPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    (goodPairPointQuotientSequence P R n m h).Exact := by
  apply ComposableArrows.exact_of_iso
    (reducedPairSequenceIsoGoodPairPointQuotientSequence P R n m h)
  exact reducedPairSequence_exact P.obj R n m h

/-- Consecutive six-term windows of the good-pair quotient sequence agree on
their three common terms. -/
lemma goodPairPointQuotientSequence_overlap
    (P : GoodPair.{w}) (R : C) (n m k : ℕ)
    (h : m + 1 = n) (h' : k + 1 = m) :
    (goodPairPointQuotientSequence P R n m h).δ₀.δ₀.δ₀ =
      (goodPairPointQuotientSequence P R m k h').δlast.δlast.δlast := by
  apply ComposableArrows.ext₂_of_arrow
  · rfl
  · rfl

/-- The terminal degree-zero sequence
`H̃₀(A) ⟶ H̃₀(X) ⟶ H̃₀(X/A) ⟶ 0` for a good pair. -/
noncomputable def goodPairPointQuotientZeroSequence
    (P : GoodPair.{w}) (R : C) : ComposableArrows C 3 :=
  ComposableArrows.mk₃
    ((Hatcher.Reduced.homologyFunctor R 0).map P.obj.map)
    ((Hatcher.Reduced.homologyFunctor R 0).map
      (pointQuotientProjection P.obj))
    (0 : (Hatcher.Reduced.homologyFunctor R 0).obj
      (pointQuotient P.obj) ⟶ (0 : C))

/-- The quotient arrow at the degree-zero endpoint is literally induced by
the canonical projection `X ⟶ X/A`. -/
@[simp]
lemma goodPairPointQuotientZeroSequence_map_one_two
    (P : GoodPair.{w}) (R : C) :
    (goodPairPointQuotientZeroSequence P R).map' 1 2 =
      (Hatcher.Reduced.homologyFunctor R 0).map
        (pointQuotientProjection P.obj) := by
  rfl

/-- The degree-zero endpoint is the terminal part of the adjacent-degree
window from degree one to degree zero. -/
lemma goodPairPointQuotientZeroSequence_δlast
    (P : GoodPair.{w}) (R : C) :
    (goodPairPointQuotientZeroSequence P R).δlast =
      (goodPairPointQuotientSequence P R 1 0 rfl).δ₀.δ₀.δ₀ := by
  apply ComposableArrows.ext₂_of_arrow
  · rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- The terminal reduced-pair sequence and the terminal quotient sequence
differ only by the degree-zero Proposition 2.22 comparison. -/
noncomputable def reducedPairZeroSequenceIsoGoodPairPointQuotientZeroSequence
    (P : GoodPair.{w}) (R : C) :
    reducedPairZeroSequence P.obj R ≅
      goodPairPointQuotientZeroSequence P R :=
  ComposableArrows.isoMk₃
    (Iso.refl _) (Iso.refl _)
    ((goodPairPointQuotientRelativeHomologyNatIso R 0).app P)
    (Iso.refl _)
    (by
      change
        (Hatcher.Reduced.homologyFunctor R 0).map P.obj.map ≫ 𝟙 _ =
          𝟙 _ ≫ (Hatcher.Reduced.homologyFunctor R 0).map P.obj.map
      simp)
    (by
      change
        reducedPairProjection P.obj R 0 ≫
            (goodPairPointQuotientRelativeHomologyNatIso R 0).hom.app P =
          𝟙 _ ≫ (Hatcher.Reduced.homologyFunctor R 0).map
            (pointQuotientProjection P.obj)
      simpa only [Category.id_comp] using
        reducedPairProjection_comp_goodPairPointQuotientRelativeHomologyNatIso_hom_app
          P R 0)
    (by
      change
        (0 : (homologyFunctor R 0).obj P.obj ⟶ (0 : C)) ≫ 𝟙 _ =
          ((goodPairPointQuotientRelativeHomologyNatIso R 0).app P).hom ≫ 0
      simp)

/-- **Hatcher, Theorem 2.13 (printed page 114), degree-zero endpoint.**
The terminal sequence `H̃₀(A) ⟶ H̃₀(X) ⟶ H̃₀(X/A) ⟶ 0`
is exact for every good pair. -/
theorem goodPairPointQuotientZeroSequence_exact
    (P : GoodPair.{w}) (R : C) :
    (goodPairPointQuotientZeroSequence P R).Exact := by
  apply ComposableArrows.exact_of_iso
    (reducedPairZeroSequenceIsoGoodPairPointQuotientZeroSequence P R)
  exact reducedPairZeroSequence_exact P.obj R
    (isGoodPair_of_goodPair P).some.nonempty.some

/-- The good-pair quotient sequence is exact in every adjacent-degree window
and at its terminal degree-zero endpoint. -/
theorem goodPairPointQuotientLongExact
    (P : GoodPair.{w}) (R : C) :
    (∀ (n m : ℕ) (h : m + 1 = n),
      (goodPairPointQuotientSequence P R n m h).Exact) ∧
      (goodPairPointQuotientZeroSequence P R).Exact := by
  exact ⟨fun n m h ↦ goodPairPointQuotientSequence_exact P R n m h,
    goodPairPointQuotientZeroSequence_exact P R⟩

end Hatcher.Relative
