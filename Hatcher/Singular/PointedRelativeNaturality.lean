/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Jack McCarthy
-/
import Hatcher.Singular.PointedRelative

/-!
# Naturality of relative homology at a basepoint

The canonical isomorphism between the homology of a pointed pair and reduced
homology is natural for based maps.  The supporting reduced-pair projection is
natural for every map of pairs, including at degree zero, and the degree-zero
endpoint is packaged as an explicit map of four-term sequences.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits ZeroObject

namespace Hatcher.Relative

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- The projection from reduced ambient homology to relative homology in the
reduced long exact sequence of a pair. -/
noncomputable def reducedPairProjection
    (P : TopPair.{w}) (R : C) (n : ℕ) :
    (Hatcher.Reduced.homologyFunctor R n).obj P.fst ⟶
      (homologyFunctor R n).obj P :=
  HomologicalComplex.homologyMap (augmentedPairProjection P R) (n + 1) ≫
    (augmentedRelativeHomologyIso P R n).hom

set_option backward.isDefEq.respectTransparency false in
/-- The reduced-pair projection is natural for every map of topological pairs
in every degree, including degree zero. -/
@[reassoc]
lemma reducedPairProjection_naturality {P Q : TopPair.{w}} (f : P ⟶ Q)
    (R : C) (n : ℕ) :
    reducedPairProjection P R n ≫ (homologyFunctor R n).map f =
      (Hatcher.Reduced.homologyFunctor R n).map (TopPair.Hom.fst f) ≫
        reducedPairProjection Q R n := by
  have hchain :
      Hatcher.Reduced.augmentedMap R (TopPair.Hom.fst f) ≫
          augmentedPairProjection Q R =
        augmentedPairProjection P R ≫ augmentedRelativeMap f R := by
    exact (augmentedPairChainComplexMap f R).comm₂₃
  dsimp only [reducedPairProjection]
  rw [Category.assoc, ← augmentedRelativeHomologyIso_naturality]
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp]
  have hmap :
      (Hatcher.Reduced.homologyFunctor R n).map (TopPair.Hom.fst f) =
        HomologicalComplex.homologyMap
          (Hatcher.Reduced.augmentedMap R (TopPair.Hom.fst f)) (n + 1) := by
    rfl
  rw [hmap, ← Category.assoc, ← HomologicalComplex.homologyMap_comp, hchain]

set_option backward.isDefEq.respectTransparency false in
/-- A map of pairs induces a map of the degree-zero endpoint of the reduced
pair long exact sequence, including the terminal zero object. -/
noncomputable def reducedPairZeroSequenceMap {P Q : TopPair.{w}} (f : P ⟶ Q)
    (R : C) :
    reducedPairZeroSequence P R ⟶ reducedPairZeroSequence Q R :=
  ComposableArrows.homMk₃
    ((Hatcher.Reduced.homologyFunctor R 0).map (TopPair.Hom.snd f))
    ((Hatcher.Reduced.homologyFunctor R 0).map (TopPair.Hom.fst f))
    ((homologyFunctor R 0).map f)
    (𝟙 (0 : C))
    (by
      symm
      change (Hatcher.Reduced.homologyFunctor R 0).map (TopPair.Hom.snd f) ≫
          (Hatcher.Reduced.homologyFunctor R 0).map Q.map =
        (Hatcher.Reduced.homologyFunctor R 0).map P.map ≫
          (Hatcher.Reduced.homologyFunctor R 0).map (TopPair.Hom.fst f)
      rw [← Functor.map_comp, TopPair.Hom.w, Functor.map_comp])
    (reducedPairProjection_naturality f R 0)
    (by
      change (0 : (homologyFunctor R 0).obj P ⟶ (0 : C)) ≫ 𝟙 (0 : C) =
        (homologyFunctor R 0).map f ≫
          (0 : (homologyFunctor R 0).obj Q ⟶ (0 : C))
      simp)

@[simp]
lemma reducedPairZeroSequenceMap_app_zero {P Q : TopPair.{w}} (f : P ⟶ Q)
    (R : C) :
    ComposableArrows.app' (reducedPairZeroSequenceMap f R) 0 =
      (Hatcher.Reduced.homologyFunctor R 0).map (TopPair.Hom.snd f) := by
  rfl

@[simp]
lemma reducedPairZeroSequenceMap_app_one {P Q : TopPair.{w}} (f : P ⟶ Q)
    (R : C) :
    ComposableArrows.app' (reducedPairZeroSequenceMap f R) 1 =
      (Hatcher.Reduced.homologyFunctor R 0).map (TopPair.Hom.fst f) := by
  rfl

@[simp]
lemma reducedPairZeroSequenceMap_app_two {P Q : TopPair.{w}} (f : P ⟶ Q)
    (R : C) :
    ComposableArrows.app' (reducedPairZeroSequenceMap f R) 2 =
      (homologyFunctor R 0).map f := by
  rfl

@[simp]
lemma reducedPairZeroSequenceMap_app_three {P Q : TopPair.{w}} (f : P ⟶ Q)
    (R : C) :
    ComposableArrows.app' (reducedPairZeroSequenceMap f R) 3 = 𝟙 (0 : C) := by
  rfl

/-- The final square of the degree-zero reduced-pair sequence commutes.  This
records explicitly that naturality includes the terminal map to zero. -/
@[reassoc]
lemma reducedPairZeroEndpoint_naturality {P Q : TopPair.{w}} (f : P ⟶ Q)
    (R : C) :
    (reducedPairZeroSequence P R).map' 2 3 ≫ 𝟙 (0 : C) =
      (homologyFunctor R 0).map f ≫
        (reducedPairZeroSequence Q R).map' 2 3 := by
  exact ComposableArrows.naturality' (reducedPairZeroSequenceMap f R) 2 3

/-- A based map induces a map between the associated pointed pairs. -/
noncomputable def pointedPairMap {X Y : TopCat.{w}} {x : X} {y : Y}
    (f : X ⟶ Y) (hf : f x = y) :
    pointedPair X x ⟶ pointedPair Y y :=
  TopPair.ofHom f (𝟙 _) (by
    ext z
    exact hf.symm)

@[simp]
lemma pointedPairMap_fst {X Y : TopCat.{w}} {x : X} {y : Y}
    (f : X ⟶ Y) (hf : f x = y) :
    TopPair.Hom.fst (pointedPairMap f hf) = f := by
  rfl

@[simp]
lemma pointedPairMap_snd {X Y : TopCat.{w}} {x : X} {y : Y}
    (f : X ⟶ Y) (hf : f x = y) :
    TopPair.Hom.snd (pointedPairMap f hf) = 𝟙 _ := by
  rfl

@[simp]
lemma pointedPairProjection_eq_reducedPairProjection
    (X : TopCat.{w}) (x : X) (R : C) (n : ℕ) :
    pointedPairProjection X x R n =
      reducedPairProjection (pointedPair X x) R n := by
  rfl

@[simp]
lemma pointedPairHomologyIso_inv
    (X : TopCat.{w}) (x : X) (R : C) (n : ℕ) :
    (pointedPairHomologyIso X x R n).inv =
      pointedPairProjection X x R n := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Hatcher, §2.1 (pages 127–128).** The canonical comparison from
relative homology at a chosen basepoint to reduced homology is natural for
based maps in every degree, including degree zero. -/
@[reassoc]
theorem pointedPairHomologyIso_naturality
    {X Y : TopCat.{w}} {x : X} {y : Y}
    (f : X ⟶ Y) (hf : f x = y) (R : C) (n : ℕ) :
    (homologyFunctor R n).map (pointedPairMap f hf) ≫
        (pointedPairHomologyIso Y y R n).hom =
      (pointedPairHomologyIso X x R n).hom ≫
        (Hatcher.Reduced.homologyFunctor R n).map f := by
  rw [← cancel_mono (pointedPairHomologyIso Y y R n).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← cancel_epi (pointedPairHomologyIso X x R n).inv]
  simp only [Iso.inv_hom_id_assoc]
  simpa only [pointedPairHomologyIso_inv,
    pointedPairProjection_eq_reducedPairProjection, pointedPairMap_fst] using
    reducedPairProjection_naturality (pointedPairMap f hf) R n

end Hatcher.Relative
