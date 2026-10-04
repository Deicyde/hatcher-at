/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.TripleChains
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-!
# Boundaries and zero horns of topological simplices

This file packages the topological simplex triple used in Hatcher's induction
for the explicit relative fundamental class.
-/

noncomputable section

open CategoryTheory Set Topology
open Simplicial Opposite

namespace Hatcher.Simplex

/-- The ordered topological standard `n`-simplex. -/
abbrev StandardSimplex (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n + 1))

/-- The boundary of the ordered standard simplex: some barycentric coordinate
vanishes. -/
def standardSimplexBoundary (n : ℕ) : Set (StandardSimplex n) :=
  {x | ∃ i, x.weights i = 0}

/-- The zero horn in the standard `(n+1)`-simplex: a coordinate other than
coordinate zero vanishes. -/
def standardSimplexZeroHorn (n : ℕ) : Set (StandardSimplex (n + 1)) :=
  {x | ∃ i, i ≠ 0 ∧ x.weights i = 0}

theorem standardSimplexZeroHorn_subset_boundary (n : ℕ) :
    standardSimplexZeroHorn n ⊆ standardSimplexBoundary (n + 1) := by
  rintro x ⟨i, _, hi⟩
  exact ⟨i, hi⟩

/-- The topological pair `(Δ[n], ∂Δ[n])`. -/
def standardSimplexPair (n : ℕ) : TopPair.{0} :=
  TopPair.ofSubset (X := TopCat.of (StandardSimplex n))
    (standardSimplexBoundary n)

/-- The nested triple `Λ⁰[n+1] ⊆ ∂Δ[n+1] ⊆ Δ[n+1]`. -/
def standardSimplexBoundaryHornTriple (n : ℕ) :
    Hatcher.Relative.TopTriple.{0} where
  X := TopCat.of (StandardSimplex (n + 1))
  A := TopCat.of (standardSimplexBoundary (n + 1))
  B := TopCat.of (standardSimplexZeroHorn n)
  mapBA := TopCat.ofHom (ContinuousMap.inclusion
    (standardSimplexZeroHorn_subset_boundary n))
  mapAX := TopCat.ofHom
    ⟨Subtype.val, continuous_subtype_val⟩
  isEmbedding_mapBA := Topology.IsEmbedding.inclusion
    (standardSimplexZeroHorn_subset_boundary n)
  isEmbedding_mapAX := Topology.IsEmbedding.subtypeVal

/-- Inserting a zero barycentric coordinate gives the zero face of the
successor simplex. -/
def standardSimplexZeroFace (n : ℕ) :
    C(StandardSimplex n, StandardSimplex (n + 1)) :=
  ⟨Convexity.StdSimplex.map Fin.succ,
    Convexity.StdSimplex.continuous_map ℝ Fin.succ⟩

@[simp]
theorem standardSimplexZeroFace_weights_succ (n : ℕ)
    (x : StandardSimplex n) (i : Fin (n + 1)) :
    (standardSimplexZeroFace n x).weights i.succ = x.weights i := by
  exact Finsupp.mapDomain_apply_of_injective
    (Fin.succ_injective (n + 1)) x.weights i

@[simp]
theorem standardSimplexZeroFace_weights_zero (n : ℕ)
    (x : StandardSimplex n) :
    (standardSimplexZeroFace n x).weights 0 = 0 := by
  exact Finsupp.mapDomain_of_notMem_range x.weights 0 (by simp)

/-- The zero face, with codomain restricted to the boundary. -/
def standardSimplexZeroFaceToBoundary (n : ℕ) :
    C(StandardSimplex n, standardSimplexBoundary (n + 1)) where
  toFun x := ⟨standardSimplexZeroFace n x,
    ⟨0, standardSimplexZeroFace_weights_zero n x⟩⟩
  continuous_toFun := (standardSimplexZeroFace n).continuous.subtype_mk _

/-- The zero face sends the boundary of `Δ[n]` into the zero horn of
`Δ[n+1]`. -/
def standardSimplexBoundaryZeroFaceToHorn (n : ℕ) :
    C(standardSimplexBoundary n, standardSimplexZeroHorn n) where
  toFun x := ⟨standardSimplexZeroFace n x, by
    obtain ⟨i, hi⟩ := x.2
    exact ⟨i.succ, by simp, by simpa using hi⟩⟩
  continuous_toFun :=
    ((standardSimplexZeroFace n).continuous.comp continuous_subtype_val).subtype_mk _

/-- The zero face as a canonical map of pairs
`(Δ[n],∂Δ[n]) → (∂Δ[n+1],Λ⁰[n+1])`. -/
def standardSimplexZeroFacePairHom (n : ℕ) :
    standardSimplexPair n ⟶
      Hatcher.Relative.TopTriple.pairAB.obj
        (standardSimplexBoundaryHornTriple n) :=
  TopPair.ofHom
    (by
      change TopCat.of (StandardSimplex n) ⟶
        TopCat.of (standardSimplexBoundary (n + 1))
      exact TopCat.ofHom (standardSimplexZeroFaceToBoundary n))
    (by
      change TopCat.of (standardSimplexBoundary n) ⟶
        TopCat.of (standardSimplexZeroHorn n)
      exact TopCat.ofHom (standardSimplexBoundaryZeroFaceToHorn n))
    (by ext x; rfl)

/-- The identity singular `n`-simplex of the topological standard simplex. -/
def standardSimplexIdentitySingularSimplex (n : ℕ) :
    (TopCat.toSSet.obj (TopCat.of (StandardSimplex n))) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.id _)

end Hatcher.Simplex
