import Mathlib.AlgebraicTopology.SimplicialSet.SSetPair
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.Topology.Category.TopPair

/-!
# Singular simplicial sets of topological pairs

This file lifts the singular-set functor from topological spaces to
topological pairs. An embedding of spaces induces a monomorphism of singular
simplicial sets, so the result is naturally a simplicial-set pair.
-/

noncomputable section

open CategoryTheory

namespace Hatcher.Relative

universe u

/-- The singular simplicial-set pair associated to a topological pair. -/
noncomputable def singularPairFunctor : TopPair.{u} ⥤ SSetPair.{u} where
  obj P := by
    letI : Mono P.map :=
      (TopCat.mono_iff_injective P.map).2 P.isEmbedding_map.injective
    exact SSetPair.of (TopCat.toSSet.map P.map)
  map {P Q} f :=
    SSetPair.homMk
      (TopCat.toSSet.map (TopPair.Hom.snd f))
      (TopCat.toSSet.map (TopPair.Hom.fst f))
      (by
        change TopCat.toSSet.map (TopPair.Hom.snd f) ≫ TopCat.toSSet.map Q.map =
          TopCat.toSSet.map P.map ≫ TopCat.toSSet.map (TopPair.Hom.fst f)
        rw [← TopCat.toSSet.map_comp, TopPair.Hom.w, TopCat.toSSet.map_comp])
  map_id P := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map (𝟙 P.snd) = 𝟙 _
      exact TopCat.toSSet.map_id _
    · change TopCat.toSSet.map (𝟙 P.fst) = 𝟙 _
      exact TopCat.toSSet.map_id _
  map_comp f g := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map
        (TopPair.Hom.snd f ≫ TopPair.Hom.snd g) = _
      exact TopCat.toSSet.map_comp _ _
    · change TopCat.toSSet.map
        (TopPair.Hom.fst f ≫ TopPair.Hom.fst g) = _
      exact TopCat.toSSet.map_comp _ _

end Hatcher.Relative
