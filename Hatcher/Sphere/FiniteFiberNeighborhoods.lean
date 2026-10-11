/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.HemisphereCharts
import Hatcher.Sphere.LocalDegreeNeighborhood

/-!
# Neighborhoods of a finite sphere-map fiber

A finite fiber of a sphere map admits pairwise disjoint open neighborhoods of
its points.  These neighborhoods are isolated-preimage neighborhoods and their
union is an open neighborhood of the full fiber.  The map also induces a
canonical morphism from the pair obtained by deleting the fiber to the sphere
punctured at the target.
-/

noncomputable section

open CategoryTheory Function Set Topology

namespace Hatcher.Sphere

/-- The set-theoretic fiber of a sphere map over a point. -/
def fiber {n : ℕ} (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (y : TopCat.sphere.{0} n) : Set (TopCat.sphere.{0} n) :=
  f ⁻¹' {y}

@[simp]
theorem mem_fiber {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y z : TopCat.sphere.{0} n} :
    z ∈ fiber f y ↔ f z = y := by
  simp [fiber]

/-- A caller-supplied finiteness proof gives the fiber subtype a finite
indexing structure without installing a global instance. -/
@[instance_reducible]
noncomputable def finiteFiberFintype {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (hfinite : (fiber f y).Finite) :
    Fintype (fiber f y) := by
  let _ : Finite (fiber f y) := hfinite.to_subtype
  exact Fintype.ofFinite _

/-- Pairwise-disjoint chosen local-degree neighborhoods of every point in a
sphere-map fiber. -/
structure FiniteFiberNeighborhoods {n : ℕ}
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (y : TopCat.sphere.{0} n) where
  /-- The chosen isolated-preimage neighborhood at each fiber point. -/
  neighborhood : ∀ i : fiber f y, LocalDegreeNeighborhood f i.1 y
  /-- The chosen underlying open sets are pairwise disjoint. -/
  pairwiseDisjoint :
    Pairwise (Disjoint on fun i ↦ (neighborhood i).U)

namespace FiniteFiberNeighborhoods

variable {n : ℕ}
  {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
  {y : TopCat.sphere.{0} n}

/-- The chosen open set around a fiber point. -/
abbrev U (D : FiniteFiberNeighborhoods f y) (i : fiber f y) :
    Set (TopCat.sphere.{0} n) :=
  (D.neighborhood i).U

/-- Every chosen fiber neighborhood is open. -/
theorem isOpen_U (D : FiniteFiberNeighborhoods f y) (i : fiber f y) :
    IsOpen (D.U i) :=
  (D.neighborhood i).isOpen_U

/-- Every fiber point belongs to its chosen neighborhood. -/
theorem center_mem (D : FiniteFiberNeighborhoods f y) (i : fiber f y) :
    i.1 ∈ D.U i :=
  (D.neighborhood i).x_mem

/-- The named family of chosen open sets is pairwise disjoint. -/
theorem pairwiseDisjoint_U (D : FiniteFiberNeighborhoods f y) :
    Pairwise (Disjoint on D.U) :=
  D.pairwiseDisjoint

/-- The union of the chosen neighborhoods of all fiber points. -/
def union (D : FiniteFiberNeighborhoods f y) :
    Set (TopCat.sphere.{0} n) :=
  ⋃ i, D.U i

/-- The union of the chosen fiber neighborhoods is open. -/
theorem isOpen_union (D : FiniteFiberNeighborhoods f y) :
    IsOpen D.union :=
  isOpen_iUnion D.isOpen_U

/-- The union of the chosen neighborhoods contains the full fiber. -/
theorem fiber_subset_union (D : FiniteFiberNeighborhoods f y) :
    fiber f y ⊆ D.union := by
  intro z hz
  exact Set.mem_iUnion.2 ⟨⟨z, hz⟩, D.center_mem ⟨z, hz⟩⟩

/-- When the fiber is empty, its family of neighborhoods has empty union. -/
theorem union_eq_empty_of_fiber_eq_empty
    (D : FiniteFiberNeighborhoods f y) (h : fiber f y = ∅) :
    D.union = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro z hz
  obtain ⟨i, _⟩ := Set.mem_iUnion.1 hz
  have hi : i.1 ∈ (∅ : Set (TopCat.sphere.{0} n)) :=
    (Set.ext_iff.mp h i.1).mp i.2
  exact hi

end FiniteFiberNeighborhoods

private theorem sphereT2Space (n : ℕ) :
    T2Space (TopCat.sphere.{0} n) :=
  (sphereULiftHomeomorph n).symm.t2Space

/-- Pairwise-disjoint open isolated-preimage neighborhoods of a finite fiber.
The construction also applies to the empty fiber. -/
noncomputable def finiteFiberNeighborhoods {n : ℕ}
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (y : TopCat.sphere.{0} n) (hfinite : (fiber f y).Finite) :
    FiniteFiberNeighborhoods f y := by
  let _ : T2Space (TopCat.sphere.{0} n) := sphereT2Space n
  let V := Classical.choose hfinite.t2_separation
  have hV : ∀ z, z ∈ V z ∧ IsOpen (V z) :=
    (Classical.choose_spec hfinite.t2_separation).1
  have hdisjoint : (fiber f y).PairwiseDisjoint V :=
    (Classical.choose_spec hfinite.t2_separation).2
  refine
    { neighborhood := fun i ↦
        { U := V i.1
          isOpen_U := (hV i.1).2
          x_mem := (hV i.1).1
          map_eq := mem_fiber.mp i.2
          eq_of_mem_of_map_eq := ?_ }
      pairwiseDisjoint := ?_ }
  · intro z hz hzy
    let j : fiber f y := ⟨z, mem_fiber.mpr hzy⟩
    by_contra hzi
    have hij : i ≠ j := by
      intro hij
      exact hzi (congrArg Subtype.val hij).symm
    have hval : (i.1 : TopCat.sphere.{0} n) ≠ j.1 := by
      intro h
      exact hij (Subtype.ext h)
    have hd : Disjoint (V i.1) (V j.1) :=
      hdisjoint i.2 j.2 hval
    exact (Set.disjoint_left.1 hd hz) (hV j.1).1
  · intro i j hij
    apply hdisjoint i.2 j.2
    intro h
    exact hij (Subtype.ext h)

private noncomputable def finiteFiberSubspaceMap {n : ℕ}
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (y : TopCat.sphere.{0} n) :
    C(((fiber f y)ᶜ : Set (TopCat.sphere.{0} n)),
      ({y}ᶜ : Set (TopCat.sphere.{0} n))) where
  toFun z := ⟨f z.1, by
    simpa only [Set.mem_compl_iff, mem_fiber,
      Set.mem_singleton_iff] using z.2⟩
  continuous_toFun :=
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _

/-- The canonical map from the sphere with a fiber deleted to the sphere
punctured at the target.  It is independent of finiteness and neighborhood
choices. -/
noncomputable def finiteFiberPairMap {n : ℕ}
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (y : TopCat.sphere.{0} n) :
    TopPair.ofSubset ((fiber f y)ᶜ : Set (TopCat.sphere.{0} n)) ⟶
      Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) y :=
  TopPair.ofHom f (TopCat.ofHom (finiteFiberSubspaceMap f y))
    (by ext z; rfl)

/-- The ambient component of the finite-fiber pair map is `f`. -/
@[simp]
theorem finiteFiberPairMap_fst {n : ℕ}
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (y : TopCat.sphere.{0} n) :
    TopPair.Hom.fst (finiteFiberPairMap f y) = f :=
  rfl

@[simp]
theorem finiteFiberPairMap_fst_apply {n : ℕ}
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (y z : TopCat.sphere.{0} n) :
    TopPair.Hom.fst (finiteFiberPairMap f y) z = f z :=
  rfl

/-- The subspace component is the restriction of `f`, with no exposed
membership proof. -/
@[simp]
theorem finiteFiberPairMap_snd_apply_coe {n : ℕ}
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (y : TopCat.sphere.{0} n)
    (z : (TopPair.ofSubset
      ((fiber f y)ᶜ : Set (TopCat.sphere.{0} n))).snd) :
    (TopPair.Hom.snd (finiteFiberPairMap f y) z).1 = f z.1 :=
  by
    change f z.1 = f z.1
    rfl

end Hatcher.Sphere
