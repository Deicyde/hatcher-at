/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Mathlib.Topology.CWComplex.Classical.Subcomplex

/-!
# Intersections of classical CW subcomplexes

The cells common to two classical CW subcomplexes form the subcomplex whose
carrier is their set-theoretic intersection.
-/

noncomputable section

open Set Topology

namespace Hatcher.ClassicalCW.Subcomplex

universe u

variable {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]

/-- The intersection of two classical CW subcomplexes. -/
def inter (A B : CWComplex.Subcomplex C) : CWComplex.Subcomplex C where
  carrier := (A : Set X) ∩ (B : Set X)
  I n := A.I n ∩ B.I n
  closed' := A.closed.inter B.closed
  union' := by
    rw [empty_union]
    ext x
    constructor
    · intro hx
      obtain ⟨n, j, hxj⟩ := Set.mem_iUnion₂.mp hx
      constructor
      · rw [← Topology.CWComplex.Subcomplex.union (E := A)]
        exact Set.mem_iUnion₂.mpr ⟨n, ⟨j.1, j.2.1⟩, hxj⟩
      · rw [← Topology.CWComplex.Subcomplex.union (E := B)]
        exact Set.mem_iUnion₂.mpr ⟨n, ⟨j.1, j.2.2⟩, hxj⟩
    · rintro ⟨hxA, hxB⟩
      have hxA' := hxA
      have hxB' := hxB
      rw [← Topology.CWComplex.Subcomplex.union (E := A)] at hxA'
      rw [← Topology.CWComplex.Subcomplex.union (E := B)] at hxB'
      obtain ⟨n, j, hxj⟩ := Set.mem_iUnion₂.mp hxA'
      obtain ⟨m, k, hxk⟩ := Set.mem_iUnion₂.mp hxB'
      have hnot : ¬ Disjoint (Topology.CWComplex.openCell (C := C) n j.1)
          (Topology.CWComplex.openCell (C := C) m k.1) :=
        not_disjoint_iff.mpr ⟨x, hxj, hxk⟩
      have heq : (⟨n, j.1⟩ : Σ q, Topology.CWComplex.cell C q) = ⟨m, k.1⟩ :=
        CWComplex.eq_of_not_disjoint_openCell hnot
      have hnm : n = m := (Sigma.mk.inj_iff.mp heq).1
      subst m
      have hjk : j.1 = k.1 := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
      have hjB : j.1 ∈ B.I n := by
        rw [hjk]
        exact k.2
      exact Set.mem_iUnion₂.mpr ⟨n, ⟨j.1, j.2, hjB⟩, hxj⟩

@[simp]
theorem coe_inter (A B : CWComplex.Subcomplex C) :
    ((inter A B : CWComplex.Subcomplex C) : Set X) =
      (A : Set X) ∩ (B : Set X) :=
  rfl

@[simp]
theorem inter_I (A B : CWComplex.Subcomplex C) (n : ℕ) :
    (inter A B).I n = A.I n ∩ B.I n :=
  rfl

@[simp]
theorem mem_inter_I (A B : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) :
    i ∈ (inter A B).I n ↔ i ∈ A.I n ∧ i ∈ B.I n :=
  Iff.rfl

end Hatcher.ClassicalCW.Subcomplex
