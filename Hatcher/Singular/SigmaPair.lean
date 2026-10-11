/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.Category.TopPair

/-!
# The sigma pair of a family of topological pairs

The topological sigma types of the ambient spaces and subspaces of a family of
topological pairs form a new pair.  Each member of the family has a canonical
morphism into this sigma pair.
-/

open CategoryTheory

namespace Hatcher.Relative

universe u v

variable {ι : Type u} (P : ι → TopPair.{max u v})

private def sigmaPairMap :
    (Σ i, (P i).snd) → (Σ i, (P i).fst) :=
  Sigma.map (fun i : ι ↦ i) fun i ↦ (P i).map

private lemma continuous_sigmaPairMap :
    Continuous (sigmaPairMap P) := by
  unfold sigmaPairMap
  exact Continuous.sigma_map fun i ↦ (P i).map.hom.continuous

private lemma isEmbedding_sigmaPairMap :
    Topology.IsEmbedding (sigmaPairMap P) := by
  unfold sigmaPairMap
  exact (Topology.isEmbedding_sigmaMap Function.injective_id).2 fun i ↦
    TopPair.isEmbedding_map (P i)

/-- The topological pair whose ambient space and subspace are the respective
topological sigma types of a family of pairs. -/
def sigmaPair : TopPair.{max u v} :=
  TopPair.of
    (TopCat.ofHom
      { toFun := sigmaPairMap P
        continuous_toFun := continuous_sigmaPairMap P })
    (isEmbedding_sigmaPairMap P)

/-- The structure map of the sigma pair applies the structure map of the
corresponding summand without changing its index. -/
@[simp]
lemma sigmaPair_map_apply (z : Σ i, (P i).snd) :
    (sigmaPair P).map z = ⟨z.1, (P z.1).map z.2⟩ := by
  rfl

/-- The canonical morphism from one member of a family into its sigma pair. -/
def sigmaPairι (i : ι) : P i ⟶ sigmaPair P :=
  TopPair.ofHom
    (TopCat.sigmaι (fun j ↦ (P j).fst) i)
    (TopCat.sigmaι (fun j ↦ (P j).snd) i)
    (by ext z; rfl)

/-- The ambient component of a summand inclusion is the standard sigma
inclusion. -/
@[simp]
lemma sigmaPairι_fst (i : ι) :
    TopPair.Hom.fst (sigmaPairι P i) =
      TopCat.sigmaι (fun j ↦ (P j).fst) i := by
  rfl

@[simp]
lemma sigmaPairι_fst_apply (i : ι) (x : (P i).fst) :
    TopPair.Hom.fst (sigmaPairι P i) x = ⟨i, x⟩ := by
  rfl

/-- The subspace component of a summand inclusion is the standard sigma
inclusion. -/
@[simp]
lemma sigmaPairι_snd (i : ι) :
    TopPair.Hom.snd (sigmaPairι P i) =
      TopCat.sigmaι (fun j ↦ (P j).snd) i := by
  rfl

@[simp]
lemma sigmaPairι_snd_apply (i : ι) (x : (P i).snd) :
    TopPair.Hom.snd (sigmaPairι P i) x = ⟨i, x⟩ := by
  rfl

end Hatcher.Relative
