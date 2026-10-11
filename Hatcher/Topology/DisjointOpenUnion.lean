/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Mathlib.Data.Set.Lattice.Disjoint
import Mathlib.Topology.Constructions

/-!
# Disjoint open unions

A pairwise disjoint family of open subsets is canonically homeomorphic to the
topological sigma type of its members.  The underlying map simply forgets the
summand tag.
-/

open Function Set

namespace Hatcher.Topology

universe u v

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/-- The canonical homeomorphism from the sigma type of a pairwise-disjoint
family of open subspaces to its union. -/
noncomputable def sigmaSubtypeHomeomorphUnion (U : ι → Set X)
    (hU : Pairwise (Disjoint on U)) (hUopen : ∀ i, IsOpen (U i)) :
    (Σ i, U i) ≃ₜ ⋃ i, U i :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (Set.sigmaToiUnion U) (Set.sigmaToiUnion_bijective U hU))
    (by
      rw [continuous_sigma_iff]
      intro i
      exact continuous_inclusion (Set.subset_iUnion U i))
    (by
      rw [isOpenMap_sigma]
      intro i
      exact (hUopen i).isOpenMap_inclusion (Set.subset_iUnion U i))

@[simp]
theorem sigmaSubtypeHomeomorphUnion_apply (U : ι → Set X)
    (hU : Pairwise (Disjoint on U)) (hUopen : ∀ i, IsOpen (U i))
    (x : Σ i, U i) :
    sigmaSubtypeHomeomorphUnion U hU hUopen x = Set.sigmaToiUnion U x :=
  rfl

@[simp]
theorem sigmaSubtypeHomeomorphUnion_apply_mk (U : ι → Set X)
    (hU : Pairwise (Disjoint on U)) (hUopen : ∀ i, IsOpen (U i))
    (i : ι) (x : U i) :
    sigmaSubtypeHomeomorphUnion U hU hUopen ⟨i, x⟩ =
      ⟨x, Set.mem_iUnion.2 ⟨i, x.2⟩⟩ :=
  rfl

@[simp]
theorem sigmaSubtypeHomeomorphUnion_symm_apply_mk (U : ι → Set X)
    (hU : Pairwise (Disjoint on U)) (hUopen : ∀ i, IsOpen (U i))
    (i : ι) (x : U i) :
    (sigmaSubtypeHomeomorphUnion U hU hUopen).symm
        ⟨x, Set.mem_iUnion.2 ⟨i, x.2⟩⟩ = ⟨i, x⟩ := by
  apply (sigmaSubtypeHomeomorphUnion U hU hUopen).injective
  rw [Homeomorph.apply_symm_apply]
  rfl

end Hatcher.Topology
