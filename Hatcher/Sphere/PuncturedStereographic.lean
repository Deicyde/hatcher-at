import Hatcher.Sphere.HemisphereCharts
import Mathlib.Analysis.Convex.Contractible

/-!
# Stereographic projection from a punctured sphere

This file exposes the full opposite-point chart used implicitly in the sphere
calculations.  The public source remains `TopCat.sphere`; the only passage to
Mathlib's metric-sphere model is the existing `sphereULiftHomeomorph`.
-/

open Metric Set
open scoped EuclideanSpace

namespace Hatcher.Sphere

private noncomputable def rawPuncturedSphereHomeomorphEuclidean
    (n : ℕ) (p : RawSphere n) :
    ({p}ᶜ : Set (RawSphere n)) ≃ₜ EuclideanSpace ℝ (Fin n) := by
  let e := stereographic' n p
  exact
    (Homeomorph.setCongr (stereographic'_source p).symm).trans
      (e.toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr (stereographic'_target p)).trans
          (Homeomorph.Set.univ _)))

private noncomputable def puncturedSphereRawHomeomorph
    (n : ℕ) (p : TopCat.sphere.{0} n) :
    ({p}ᶜ : Set (TopCat.sphere.{0} n)) ≃ₜ
      ({sphereULiftHomeomorph n p}ᶜ : Set (RawSphere n)) :=
  (sphereULiftHomeomorph n).subtype fun x => by simp

/-- Stereographic projection from `p` identifies the complement of `p` in the
standard `n`-sphere with Euclidean `n`-space. -/
noncomputable def puncturedSphereHomeomorphEuclidean
    (n : ℕ) (p : TopCat.sphere.{0} n) :
    ({p}ᶜ : Set (TopCat.sphere.{0} n)) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (puncturedSphereRawHomeomorph n p).trans
    (rawPuncturedSphereHomeomorphEuclidean n (sphereULiftHomeomorph n p))

/-- The complement of a point in the standard sphere is contractible. -/
noncomputable instance puncturedSphereContractibleSpace
    (n : ℕ) (p : TopCat.sphere.{0} n) :
    ContractibleSpace ({p}ᶜ : Set (TopCat.sphere.{0} n)) :=
  Homeomorph.contractibleSpace (puncturedSphereHomeomorphEuclidean n p)

/-- In every positive-dimensional standard sphere, inverse stereographic
projection embeds the closed unit balls centered at `4 i e₀` as pairwise
disjoint closed balls. Their literal interiors are open and have Euclidean
ball charts. The common omitted point is the last coordinate vector, fixed by
orthogonal reflection in the zeroth coordinate hyperplane. The index `Fin k`
also includes the empty family when `k = 0`. -/
theorem finite_disjoint_sphere_balls (n : ℕ) (hn : 0 < n) (k : ℕ) :
    ∃ b : TopCat.sphere.{0} n,
      let e := puncturedSphereHomeomorphEuclidean n b
      let f : EuclideanSpace ℝ (Fin n) → TopCat.sphere.{0} n :=
        fun y ↦ (e.symm y).1
      let c : Fin k → EuclideanSpace ℝ (Fin n) :=
        fun i ↦ EuclideanSpace.single ⟨0, hn⟩ (4 * (i.1 : ℝ))
      (sphereULiftHomeomorph.{0} n b).1 =
          EuclideanSpace.single (Fin.last n) (1 : ℝ) ∧
      ((ℝ ∙ EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))ᗮ).reflection
          (sphereULiftHomeomorph.{0} n b).1 =
        (sphereULiftHomeomorph.{0} n b).1 ∧
      Topology.IsOpenEmbedding f ∧
      Pairwise (fun i j ↦
        Disjoint (f '' closedBall (c i) 1) (f '' closedBall (c j) 1)) ∧
      ∀ i : Fin k,
        Topology.IsClosedEmbedding
            (f ∘ (Subtype.val : closedBall (c i) 1 → EuclideanSpace ℝ (Fin n))) ∧
        IsClosed (f '' closedBall (c i) 1) ∧
        b ∉ f '' closedBall (c i) 1 ∧
        interior (f '' closedBall (c i) 1) = f '' ball (c i) 1 ∧
        IsOpen (f '' ball (c i) 1) ∧
        Nonempty (closedBall (c i) 1 ≃ₜ (f '' closedBall (c i) 1)) ∧
        Nonempty ((f '' ball (c i) 1) ≃ₜ ball (c i) 1) := by
  classical
  let : T2Space (TopCat.sphere.{0} n) :=
    (sphereULiftHomeomorph.{0} n).isEmbedding.t2Space
  let p : RawSphere n :=
    ⟨EuclideanSpace.single (Fin.last n) (1 : ℝ), by simp⟩
  let b : TopCat.sphere.{0} n := (sphereULiftHomeomorph.{0} n).symm p
  let e := puncturedSphereHomeomorphEuclidean n b
  let f : EuclideanSpace ℝ (Fin n) → TopCat.sphere.{0} n :=
    fun y ↦ (e.symm y).1
  let c : Fin k → EuclideanSpace ℝ (Fin n) :=
    fun i ↦ EuclideanSpace.single ⟨0, hn⟩ (4 * (i.1 : ℝ))
  have haxis : (sphereULiftHomeomorph.{0} n b).1 =
      EuclideanSpace.single (Fin.last n) (1 : ℝ) :=
    congrArg Subtype.val ((sphereULiftHomeomorph.{0} n).apply_symm_apply p)
  have hfirst_last : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hval
    exact (ne_of_gt hn) hval.symm
  have hreflection :
      ((ℝ ∙ EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))ᗮ).reflection
          (sphereULiftHomeomorph.{0} n b).1 =
        (sphereULiftHomeomorph.{0} n b).1 := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, haxis]
    simp [EuclideanSpace.inner_single_left, hfirst_last]
  have hopen : IsOpen ({b}ᶜ : Set (TopCat.sphere.{0} n)) :=
    isClosed_singleton.isOpen_compl
  have hf : Topology.IsOpenEmbedding f :=
    hopen.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
  have hc : Pairwise (fun i j : Fin k ↦
      Disjoint (closedBall (c i) 1) (closedBall (c j) 1)) := by
    intro i j hij
    apply closedBall_disjoint_closedBall
    have hij' : i.1 ≠ j.1 := fun h ↦ hij (Fin.ext h)
    have hdist : (2 : ℝ) < |4 * (i.1 : ℝ) - 4 * (j.1 : ℝ)| := by
      rcases lt_or_gt_of_ne hij' with hijlt | hjilt
      · have hgap : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hijlt)
        rw [abs_of_nonpos (by linarith :
          4 * (i.1 : ℝ) - 4 * (j.1 : ℝ) ≤ 0)]
        linarith
      · have hgap : (j.1 : ℝ) + 1 ≤ (i.1 : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hjilt)
        rw [abs_of_nonneg (by linarith :
          0 ≤ 4 * (i.1 : ℝ) - 4 * (j.1 : ℝ))]
        linarith
    simpa [c, EuclideanSpace.single, Real.dist_eq,
      (one_add_one_eq_two : (1 : ℝ) + 1 = 2)] using hdist
  refine ⟨b, haxis, hreflection, hf, ?_, ?_⟩
  · intro i j hij
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
    have hvu' := hf.injective hvu
    subst v
    exact Set.disjoint_left.mp (hc hij) hu hv
  · intro i
    have hcompact : IsCompact (f '' closedBall (c i) 1) :=
      (isCompact_closedBall (c i) 1).image hf.continuous
    have hclosed : IsClosed (f '' closedBall (c i) 1) := hcompact.isClosed
    have hclosedEmbedding : Topology.IsClosedEmbedding
        (f ∘ (Subtype.val : closedBall (c i) 1 → EuclideanSpace ℝ (Fin n))) := by
      refine ⟨hf.isEmbedding.comp Topology.IsEmbedding.subtypeVal, ?_⟩
      simpa only [Set.range_comp, Subtype.range_coe] using hclosed
    have hb : b ∉ f '' closedBall (c i) 1 := by
      rintro ⟨y, _, hy⟩
      have hy' : f y ≠ b := by
        simpa only [f, mem_compl_iff, mem_singleton_iff] using (e.symm y).property
      exact hy' hy
    have hinterior :
        interior (f '' closedBall (c i) 1) = f '' ball (c i) 1 := by
      have hsubset : interior (f '' closedBall (c i) 1) ⊆ Set.range f := by
        intro x hx
        rcases interior_subset hx with ⟨y, _, hy⟩
        exact ⟨y, hy⟩
      calc
        interior (f '' closedBall (c i) 1) =
            f '' (f ⁻¹' interior (f '' closedBall (c i) 1)) :=
          (Set.image_preimage_eq_of_subset hsubset).symm
        _ = f '' interior (closedBall (c i) 1) := by
          rw [hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous,
            hf.injective.preimage_image]
        _ = f '' ball (c i) 1 := by
          rw [interior_closedBall (c i) (one_ne_zero : (1 : ℝ) ≠ 0)]
    exact ⟨hclosedEmbedding, hclosed, hb, hinterior,
      hf.isOpenMap _ isOpen_ball,
      ⟨hf.isEmbedding.homeomorphImage (closedBall (c i) 1)⟩,
      ⟨(hf.isEmbedding.homeomorphImage (ball (c i) 1)).symm⟩⟩

end Hatcher.Sphere
