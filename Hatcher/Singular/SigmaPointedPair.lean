import Hatcher.Singular.PointedRelative
import Hatcher.Singular.SigmaPair

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

/-- The pair whose ambient space is the topological coproduct `Σ i, X i` and
whose subspace contains the chosen basepoint in every summand. -/
noncomputable def sigmaPointedPair (x₀ : ∀ i, X i) : TopPair.{max u v} :=
  sigmaPair fun i ↦ pointedPair (X i) (x₀ i)

/-- The pointed sigma pair is definitionally the generic sigma pair of the
corresponding pointed pairs. -/
theorem sigmaPointedPair_eq_sigmaPair (x₀ : ∀ i, X i) :
    sigmaPointedPair x₀ =
      sigmaPair (fun i ↦ pointedPair (X i) (x₀ i)) :=
  rfl

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
  sigmaPairι (fun j ↦ pointedPair (X j) (x₀ j)) i

/-- The inclusion of a pointed summand is definitionally the corresponding
generic sigma-pair inclusion. -/
theorem sigmaPointedPairι_eq_sigmaPairι (x₀ : ∀ i, X i) (i : ι) :
    sigmaPointedPairι x₀ i =
      sigmaPairι (fun j ↦ pointedPair (X j) (x₀ j)) i :=
  rfl

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
