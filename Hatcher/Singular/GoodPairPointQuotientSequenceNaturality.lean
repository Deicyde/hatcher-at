/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.GoodPairPointQuotientExactSequence

/-!
# Naturality of the good-pair point-quotient exact sequence

Every morphism of good pairs induces the canonical morphisms between Hatcher's
six-term point-quotient sequences and their terminal degree-zero sequences.
The connecting square follows by transporting reduced-pair naturality through
the Proposition 2.22 natural isomorphism.  The quotient components are the
maps induced by the functorial point-quotient maps.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits ZeroObject

namespace Hatcher.Relative

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- **Hatcher, §2.1 (printed page 128).** The connecting morphism in the
good-pair point-quotient sequence is natural for every map of good pairs. -/
@[reassoc]
theorem goodPairPointQuotientConnecting_naturality
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C)
    (n m : ℕ) (h : m + 1 = n) :
    goodPairPointQuotientConnecting P R n m h ≫
        (Hatcher.Reduced.homologyFunctor R m).map
          (TopPair.Hom.snd f.hom) =
      (Hatcher.Reduced.homologyFunctor R n).map
          (pointQuotientMap f.hom) ≫
        goodPairPointQuotientConnecting Q R n m h := by
  dsimp only [goodPairPointQuotientConnecting]
  rw [Category.assoc, reducedPairConnecting_naturality]
  have hnaturality :=
    (goodPairPointQuotientRelativeHomologyNatIso R n).inv.naturality_assoc f
      (reducedPairConnecting Q.obj R n m h)
  dsimp [goodPairRelativeHomologyFunctor,
    goodPairReducedPointQuotientHomologyFunctor] at hnaturality
  exact hnaturality.symm

/-- A map of good pairs induces the canonical morphism between the
corresponding six-term windows in Hatcher's point-quotient exact sequence. -/
noncomputable def goodPairPointQuotientSequenceMap
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C)
    (n m : ℕ) (h : m + 1 = n) :
    goodPairPointQuotientSequence P R n m h ⟶
      goodPairPointQuotientSequence Q R n m h :=
  ComposableArrows.homMk₅
    ((Hatcher.Reduced.homologyFunctor R n).map (TopPair.Hom.snd f.hom))
    ((Hatcher.Reduced.homologyFunctor R n).map (TopPair.Hom.fst f.hom))
    ((Hatcher.Reduced.homologyFunctor R n).map (pointQuotientMap f.hom))
    ((Hatcher.Reduced.homologyFunctor R m).map (TopPair.Hom.snd f.hom))
    ((Hatcher.Reduced.homologyFunctor R m).map (TopPair.Hom.fst f.hom))
    ((Hatcher.Reduced.homologyFunctor R m).map (pointQuotientMap f.hom))
    (by
      change
        (Hatcher.Reduced.homologyFunctor R n).map P.obj.map ≫
            (Hatcher.Reduced.homologyFunctor R n).map
              (TopPair.Hom.fst f.hom) =
          (Hatcher.Reduced.homologyFunctor R n).map
              (TopPair.Hom.snd f.hom) ≫
            (Hatcher.Reduced.homologyFunctor R n).map Q.obj.map
      simpa only [Functor.map_comp] using congrArg
        (fun g ↦ (Hatcher.Reduced.homologyFunctor R n).map g)
        (TopPair.Hom.w f.hom).symm)
    (by
      change
        (Hatcher.Reduced.homologyFunctor R n).map
              (pointQuotientProjection P.obj) ≫
            (Hatcher.Reduced.homologyFunctor R n).map
              (pointQuotientMap f.hom) =
          (Hatcher.Reduced.homologyFunctor R n).map
              (TopPair.Hom.fst f.hom) ≫
            (Hatcher.Reduced.homologyFunctor R n).map
              (pointQuotientProjection Q.obj)
      rw [← Functor.map_comp, pointQuotientProjection_naturality,
        Functor.map_comp])
    (goodPairPointQuotientConnecting_naturality f R n m h)
    (by
      change
        (Hatcher.Reduced.homologyFunctor R m).map P.obj.map ≫
            (Hatcher.Reduced.homologyFunctor R m).map
              (TopPair.Hom.fst f.hom) =
          (Hatcher.Reduced.homologyFunctor R m).map
              (TopPair.Hom.snd f.hom) ≫
            (Hatcher.Reduced.homologyFunctor R m).map Q.obj.map
      simpa only [Functor.map_comp] using congrArg
        (fun g ↦ (Hatcher.Reduced.homologyFunctor R m).map g)
        (TopPair.Hom.w f.hom).symm)
    (by
      change
        (Hatcher.Reduced.homologyFunctor R m).map
              (pointQuotientProjection P.obj) ≫
            (Hatcher.Reduced.homologyFunctor R m).map
              (pointQuotientMap f.hom) =
          (Hatcher.Reduced.homologyFunctor R m).map
              (TopPair.Hom.fst f.hom) ≫
            (Hatcher.Reduced.homologyFunctor R m).map
              (pointQuotientProjection Q.obj)
      rw [← Functor.map_comp, pointQuotientProjection_naturality,
        Functor.map_comp])

@[simp] lemma goodPairPointQuotientSequenceMap_app_zero
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C)
    (n m : ℕ) (h : m + 1 = n) :
    ComposableArrows.app' (goodPairPointQuotientSequenceMap f R n m h) 0 =
      (Hatcher.Reduced.homologyFunctor R n).map
        (TopPair.Hom.snd f.hom) := rfl

@[simp] lemma goodPairPointQuotientSequenceMap_app_one
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C)
    (n m : ℕ) (h : m + 1 = n) :
    ComposableArrows.app' (goodPairPointQuotientSequenceMap f R n m h) 1 =
      (Hatcher.Reduced.homologyFunctor R n).map
        (TopPair.Hom.fst f.hom) := rfl

@[simp] lemma goodPairPointQuotientSequenceMap_app_two
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C)
    (n m : ℕ) (h : m + 1 = n) :
    ComposableArrows.app' (goodPairPointQuotientSequenceMap f R n m h) 2 =
      (Hatcher.Reduced.homologyFunctor R n).map
        (pointQuotientMap f.hom) := rfl

@[simp] lemma goodPairPointQuotientSequenceMap_app_three
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C)
    (n m : ℕ) (h : m + 1 = n) :
    ComposableArrows.app' (goodPairPointQuotientSequenceMap f R n m h) 3 =
      (Hatcher.Reduced.homologyFunctor R m).map
        (TopPair.Hom.snd f.hom) := rfl

@[simp] lemma goodPairPointQuotientSequenceMap_app_four
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C)
    (n m : ℕ) (h : m + 1 = n) :
    ComposableArrows.app' (goodPairPointQuotientSequenceMap f R n m h) 4 =
      (Hatcher.Reduced.homologyFunctor R m).map
        (TopPair.Hom.fst f.hom) := rfl

@[simp] lemma goodPairPointQuotientSequenceMap_app_five
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C)
    (n m : ℕ) (h : m + 1 = n) :
    ComposableArrows.app' (goodPairPointQuotientSequenceMap f R n m h) 5 =
      (Hatcher.Reduced.homologyFunctor R m).map
        (pointQuotientMap f.hom) := rfl

/-- The upper ambient-to-quotient square is the square induced by the
functorial point-quotient projection. -/
@[reassoc]
lemma goodPairPointQuotientSequence_upper_projection_naturality
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C)
    (n m : ℕ) (h : m + 1 = n) :
    (goodPairPointQuotientSequence P R n m h).map' 1 2 ≫
        (Hatcher.Reduced.homologyFunctor R n).map
          (pointQuotientMap f.hom) =
      (Hatcher.Reduced.homologyFunctor R n).map
          (TopPair.Hom.fst f.hom) ≫
        (goodPairPointQuotientSequence Q R n m h).map' 1 2 := by
  exact ComposableArrows.naturality'
    (goodPairPointQuotientSequenceMap f R n m h) 1 2

/-- The lower ambient-to-quotient square is the corresponding square one
degree lower. -/
@[reassoc]
lemma goodPairPointQuotientSequence_lower_projection_naturality
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C)
    (n m : ℕ) (h : m + 1 = n) :
    (goodPairPointQuotientSequence P R n m h).map' 4 5 ≫
        (Hatcher.Reduced.homologyFunctor R m).map
          (pointQuotientMap f.hom) =
      (Hatcher.Reduced.homologyFunctor R m).map
          (TopPair.Hom.fst f.hom) ≫
        (goodPairPointQuotientSequence Q R n m h).map' 4 5 := by
  exact ComposableArrows.naturality'
    (goodPairPointQuotientSequenceMap f R n m h) 4 5

/-- The maps of two consecutive six-term windows agree on their three common
terms. -/
lemma goodPairPointQuotientSequenceMap_overlap
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C)
    (n m k : ℕ) (h : m + 1 = n) (h' : k + 1 = m) :
    ComposableArrows.app'
        (ComposableArrows.δ₀Functor.map
          (ComposableArrows.δ₀Functor.map
            (ComposableArrows.δ₀Functor.map
              (goodPairPointQuotientSequenceMap f R n m h)))) 0 =
      ComposableArrows.app'
        (ComposableArrows.δlastFunctor.map
          (ComposableArrows.δlastFunctor.map
            (ComposableArrows.δlastFunctor.map
              (goodPairPointQuotientSequenceMap f R m k h')))) 0 ∧
    ComposableArrows.app'
        (ComposableArrows.δ₀Functor.map
          (ComposableArrows.δ₀Functor.map
            (ComposableArrows.δ₀Functor.map
              (goodPairPointQuotientSequenceMap f R n m h)))) 1 =
      ComposableArrows.app'
        (ComposableArrows.δlastFunctor.map
          (ComposableArrows.δlastFunctor.map
            (ComposableArrows.δlastFunctor.map
              (goodPairPointQuotientSequenceMap f R m k h')))) 1 ∧
    ComposableArrows.app'
        (ComposableArrows.δ₀Functor.map
          (ComposableArrows.δ₀Functor.map
            (ComposableArrows.δ₀Functor.map
              (goodPairPointQuotientSequenceMap f R n m h)))) 2 =
      ComposableArrows.app'
        (ComposableArrows.δlastFunctor.map
          (ComposableArrows.δlastFunctor.map
            (ComposableArrows.δlastFunctor.map
              (goodPairPointQuotientSequenceMap f R m k h')))) 2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- A map of good pairs induces the canonical map between the terminal
degree-zero quotient sequences, including the terminal zero object. -/
noncomputable def goodPairPointQuotientZeroSequenceMap
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C) :
    goodPairPointQuotientZeroSequence P R ⟶
      goodPairPointQuotientZeroSequence Q R :=
  ComposableArrows.homMk₃
    ((Hatcher.Reduced.homologyFunctor R 0).map (TopPair.Hom.snd f.hom))
    ((Hatcher.Reduced.homologyFunctor R 0).map (TopPair.Hom.fst f.hom))
    ((Hatcher.Reduced.homologyFunctor R 0).map (pointQuotientMap f.hom))
    (𝟙 (0 : C))
    (by
      change
        (Hatcher.Reduced.homologyFunctor R 0).map P.obj.map ≫
            (Hatcher.Reduced.homologyFunctor R 0).map
              (TopPair.Hom.fst f.hom) =
          (Hatcher.Reduced.homologyFunctor R 0).map
              (TopPair.Hom.snd f.hom) ≫
            (Hatcher.Reduced.homologyFunctor R 0).map Q.obj.map
      simpa only [Functor.map_comp] using congrArg
        (fun g ↦ (Hatcher.Reduced.homologyFunctor R 0).map g)
        (TopPair.Hom.w f.hom).symm)
    (by
      change
        (Hatcher.Reduced.homologyFunctor R 0).map
              (pointQuotientProjection P.obj) ≫
            (Hatcher.Reduced.homologyFunctor R 0).map
              (pointQuotientMap f.hom) =
          (Hatcher.Reduced.homologyFunctor R 0).map
              (TopPair.Hom.fst f.hom) ≫
            (Hatcher.Reduced.homologyFunctor R 0).map
              (pointQuotientProjection Q.obj)
      rw [← Functor.map_comp, pointQuotientProjection_naturality,
        Functor.map_comp])
    (by
      change
        (0 : (Hatcher.Reduced.homologyFunctor R 0).obj
            (pointQuotient P.obj) ⟶ (0 : C)) ≫ 𝟙 (0 : C) =
          (Hatcher.Reduced.homologyFunctor R 0).map
              (pointQuotientMap f.hom) ≫ 0
      simp)

@[simp] lemma goodPairPointQuotientZeroSequenceMap_app_zero
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C) :
    ComposableArrows.app' (goodPairPointQuotientZeroSequenceMap f R) 0 =
      (Hatcher.Reduced.homologyFunctor R 0).map
        (TopPair.Hom.snd f.hom) := rfl

@[simp] lemma goodPairPointQuotientZeroSequenceMap_app_one
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C) :
    ComposableArrows.app' (goodPairPointQuotientZeroSequenceMap f R) 1 =
      (Hatcher.Reduced.homologyFunctor R 0).map
        (TopPair.Hom.fst f.hom) := rfl

@[simp] lemma goodPairPointQuotientZeroSequenceMap_app_two
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C) :
    ComposableArrows.app' (goodPairPointQuotientZeroSequenceMap f R) 2 =
      (Hatcher.Reduced.homologyFunctor R 0).map
        (pointQuotientMap f.hom) := rfl

@[simp] lemma goodPairPointQuotientZeroSequenceMap_app_three
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C) :
    ComposableArrows.app' (goodPairPointQuotientZeroSequenceMap f R) 3 =
      𝟙 (0 : C) := rfl

/-- Naturality includes the final square from reduced quotient homology to the
zero object. -/
@[reassoc]
lemma goodPairPointQuotientZeroEndpoint_naturality
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C) :
    (goodPairPointQuotientZeroSequence P R).map' 2 3 ≫ 𝟙 (0 : C) =
      (Hatcher.Reduced.homologyFunctor R 0).map
          (pointQuotientMap f.hom) ≫
        (goodPairPointQuotientZeroSequence Q R).map' 2 3 := by
  exact ComposableArrows.naturality'
    (goodPairPointQuotientZeroSequenceMap f R) 2 3

/-- The terminal degree-zero sequence map is the last three components of the
degree-one/degree-zero six-term sequence map. -/
lemma goodPairPointQuotientZeroSequenceMap_δlast
    {P Q : GoodPair.{w}} (f : P ⟶ Q) (R : C) :
    ComposableArrows.app'
        (ComposableArrows.δlastFunctor.map
          (goodPairPointQuotientZeroSequenceMap f R)) 0 =
      ComposableArrows.app'
        (ComposableArrows.δ₀Functor.map
          (ComposableArrows.δ₀Functor.map
            (ComposableArrows.δ₀Functor.map
              (goodPairPointQuotientSequenceMap f R 1 0 rfl)))) 0 ∧
    ComposableArrows.app'
        (ComposableArrows.δlastFunctor.map
          (goodPairPointQuotientZeroSequenceMap f R)) 1 =
      ComposableArrows.app'
        (ComposableArrows.δ₀Functor.map
          (ComposableArrows.δ₀Functor.map
            (ComposableArrows.δ₀Functor.map
              (goodPairPointQuotientSequenceMap f R 1 0 rfl)))) 1 ∧
    ComposableArrows.app'
        (ComposableArrows.δlastFunctor.map
          (goodPairPointQuotientZeroSequenceMap f R)) 2 =
      ComposableArrows.app'
        (ComposableArrows.δ₀Functor.map
          (ComposableArrows.δ₀Functor.map
            (ComposableArrows.δ₀Functor.map
              (goodPairPointQuotientSequenceMap f R 1 0 rfl)))) 2 := by
  exact ⟨rfl, rfl, rfl⟩

end Hatcher.Relative
