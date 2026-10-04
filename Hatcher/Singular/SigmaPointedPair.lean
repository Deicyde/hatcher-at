import Hatcher.Singular.PointedRelativeNaturality
import Mathlib.Topology.Category.TopCat.Limits.Products

/-!
# The sigma pair of a family of pointed spaces

This file packages the topological coproduct of a family of pointed spaces as
a topological pair.  It also records the canonical morphism from each pointed
summand into that pair.
-/

noncomputable section

open CategoryTheory

namespace Hatcher.Relative

universe u v

variable {ι : Type u} {X : ι → TopCat.{max u v}}

private def sigmaBasepointMap (x₀ : ∀ i, X i) :
    (Σ _ : ι, PUnit.{max u v + 1}) → (Σ i, X i) :=
  Sigma.map (fun i : ι ↦ i) fun i (_ : PUnit.{max u v + 1}) ↦ x₀ i

private lemma continuous_sigmaBasepointMap (x₀ : ∀ i, X i) :
    Continuous (sigmaBasepointMap x₀) := by
  unfold sigmaBasepointMap
  exact Continuous.sigma_map fun _ ↦ continuous_const

private lemma isEmbedding_sigmaBasepointMap (x₀ : ∀ i, X i) :
    Topology.IsEmbedding (sigmaBasepointMap x₀) := by
  unfold sigmaBasepointMap
  exact (Topology.isEmbedding_sigmaMap Function.injective_id).2 fun _ ↦
    Topology.IsEmbedding.of_subsingleton _

/-- The pair whose ambient space is the topological coproduct `Σ i, X i` and
whose subspace contains the chosen basepoint in every summand. -/
noncomputable def sigmaPointedPair (x₀ : ∀ i, X i) : TopPair.{max u v} :=
  TopPair.of
    (TopCat.ofHom
      { toFun := sigmaBasepointMap x₀
        continuous_toFun := continuous_sigmaBasepointMap x₀ })
    (isEmbedding_sigmaBasepointMap x₀)

/-- The structure map of the sigma pointed pair sends the singleton in each
summand to that summand's chosen basepoint. -/
@[simp]
lemma sigmaPointedPair_map_apply (x₀ : ∀ i, X i)
    (z : Σ _ : ι, PUnit.{max u v + 1}) :
    (sigmaPointedPair x₀).map z = ⟨z.1, x₀ z.1⟩ := by
  rfl

/-- The canonical morphism from a pointed summand into the sigma pointed
pair. -/
noncomputable def sigmaPointedPairι (x₀ : ∀ i, X i) (i : ι) :
    pointedPair (X i) (x₀ i) ⟶ sigmaPointedPair x₀ :=
  TopPair.ofHom
    (TopCat.sigmaι X i)
    (TopCat.sigmaι (fun _ : ι ↦ TopCat.of PUnit.{max u v + 1}) i)
    (by
      ext z
      rcases z with ⟨⟩
      rfl)

/-- The ambient component of the canonical inclusion of a pointed summand is
the standard sigma inclusion. -/
@[simp]
lemma sigmaPointedPairι_fst (x₀ : ∀ i, X i) (i : ι) :
    TopPair.Hom.fst (sigmaPointedPairι x₀ i) = TopCat.sigmaι X i := by
  rfl

@[simp]
lemma sigmaPointedPairι_fst_apply (x₀ : ∀ i, X i) (i : ι) (x : X i) :
    TopPair.Hom.fst (sigmaPointedPairι x₀ i) x = ⟨i, x⟩ := by
  rfl

/-- The subspace component of the canonical inclusion of a pointed summand is
the standard sigma inclusion. -/
@[simp]
lemma sigmaPointedPairι_snd (x₀ : ∀ i, X i) (i : ι) :
    TopPair.Hom.snd (sigmaPointedPairι x₀ i) =
      TopCat.sigmaι (fun _ : ι ↦ TopCat.of PUnit.{max u v + 1}) i := by
  rfl

@[simp]
lemma sigmaPointedPairι_snd_apply (x₀ : ∀ i, X i) (i : ι)
    (z : PUnit.{max u v + 1}) :
    TopPair.Hom.snd (sigmaPointedPairι x₀ i) z = ⟨i, z⟩ := by
  rfl

end Hatcher.Relative
