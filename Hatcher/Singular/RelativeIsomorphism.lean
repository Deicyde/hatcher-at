import Hatcher.Singular.Relative

/-!
# Isomorphisms in relative homology

This file derives an isomorphism criterion for relative homology from the long
exact sequence of a pair.  In particular, it handles degree zero through the
endpoint case built into Mathlib's generic homology-sequence criterion.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits

namespace Hatcher.Relative

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- A map of topological pairs that induces ordinary homology isomorphisms on
both the subspace and ambient-space components also induces an isomorphism in
relative homology, in every degree (including degree zero). -/
theorem homologyMap_isIso_of_components
    {P Q : TopPair.{w}} (f : P ⟶ Q) (R : C) (n : ℕ)
    (hsubspace : ∀ k : ℕ,
      IsIso (((singularHomologyFunctor C k).obj R).map (TopPair.Hom.snd f)))
    (hambient : ∀ k : ℕ,
      IsIso (((singularHomologyFunctor C k).obj R).map (TopPair.Hom.fst f))) :
    IsIso ((homologyFunctor R n).map f) := by
  change IsIso (HomologicalComplex.homologyMap
    ((pairChainComplexShortComplexFunctor R).map f).τ₃ n)
  apply HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    ((pairChainComplexShortComplexFunctor R).map f)
    ((singularPairFunctor.obj P).shortExact_chainComplexShortComplex R)
    ((singularPairFunctor.obj Q).shortExact_chainComplexShortComplex R)
  · change Epi (((singularHomologyFunctor C n).obj R).map (TopPair.Hom.snd f))
    have := hsubspace n
    infer_instance
  · change IsIso (((singularHomologyFunctor C n).obj R).map (TopPair.Hom.fst f))
    exact hambient n
  · intro k _
    change IsIso (((singularHomologyFunctor C k).obj R).map (TopPair.Hom.snd f))
    exact hsubspace k
  · intro k _
    change Mono (((singularHomologyFunctor C k).obj R).map (TopPair.Hom.fst f))
    have := hambient k
    infer_instance

end Hatcher.Relative
