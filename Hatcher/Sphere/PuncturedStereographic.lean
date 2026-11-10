import Hatcher.Sphere.HemisphereCharts
import Hatcher.Singular.GoodPair
import Hatcher.Sphere.ZeroSphere
import Mathlib.Analysis.Convex.Contractible
import Hatcher.Singular.PointedWedgePointQuotient
import Hatcher.Topology.DisjointOpenUnion

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

namespace Hatcher.Sphere

open scoped OnePoint

/-- The prescribed Euclidean center of the ith sphere ball. -/
noncomputable def sphereBallCenter {n k : ℕ} (hn : 0 < n) (i : Fin k) :
    EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single ⟨0, hn⟩ (4 * (i.1 : ℝ))

/-- Inverse stereographic projection, followed by the actual subtype inclusion. -/
noncomputable def sphereBallEmbedding (n : ℕ) (b : TopCat.sphere.{0} n) :
    EuclideanSpace ℝ (Fin n) → TopCat.sphere.{0} n :=
  fun y ↦ ((puncturedSphereHomeomorphEuclidean n b).symm y).1

/-- The actual closed sphere ball transported from the prescribed Euclidean ball. -/
noncomputable def sphereBallClosed {n k : ℕ} (hn : 0 < n)
    (b : TopCat.sphere.{0} n) (i : Fin k) : Set (TopCat.sphere.{0} n) :=
  sphereBallEmbedding n b '' closedBall (sphereBallCenter hn i) 1

/-- The actual open sphere ball transported from the prescribed Euclidean ball. -/
noncomputable def sphereBallOpen {n k : ℕ} (hn : 0 < n)
    (b : TopCat.sphere.{0} n) (i : Fin k) : Set (TopCat.sphere.{0} n) :=
  sphereBallEmbedding n b '' ball (sphereBallCenter hn i) 1

/-- The union of the constructed open balls, with the empty union retained. -/
noncomputable def sphereBallUnion (n : ℕ) (hn : 0 < n) (k : ℕ)
    (b : TopCat.sphere.{0} n) : Set (TopCat.sphere.{0} n) :=
  ⋃ i : Fin k, sphereBallOpen hn b i

set_option maxHeartbeats 800000 in
/-- The actual geometry, punctured charts, and complement-collapse quotient
comparison used in the sphere pinch construction. All ball sets are fixed by
their prescribed stereographic formulas. -/
structure SphereBallPinchData (n : ℕ) (hn : 0 < n) (k : ℕ) where
  b : TopCat.sphere.{0} n
  last_axis :
    (sphereULiftHomeomorph.{0} n b).1 =
      EuclideanSpace.single (Fin.last n) (1 : ℝ)
  zeroth_reflection :
    ((ℝ ∙ EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))ᗮ).reflection
        (sphereULiftHomeomorph.{0} n b).1 =
      (sphereULiftHomeomorph.{0} n b).1
  embedding_open : Topology.IsOpenEmbedding (sphereBallEmbedding n b)
  closed_disjoint :
    Pairwise (fun i j : Fin k ↦
      Disjoint (sphereBallClosed hn b i) (sphereBallClosed hn b j))
  closed_properties :
    ∀ i : Fin k,
      Topology.IsClosedEmbedding
          (sphereBallEmbedding n b ∘
            (Subtype.val :
              closedBall (sphereBallCenter hn i) 1 → EuclideanSpace ℝ (Fin n))) ∧
      IsClosed (sphereBallClosed hn b i) ∧
      b ∉ sphereBallClosed hn b i ∧
      interior (sphereBallClosed hn b i) = sphereBallOpen hn b i ∧
      IsOpen (sphereBallOpen hn b i) ∧
      Nonempty (closedBall (sphereBallCenter hn i) 1 ≃ₜ sphereBallClosed hn b i) ∧
      Nonempty (sphereBallOpen hn b i ≃ₜ ball (sphereBallCenter hn i) 1)
  ballChart :
    ∀ i : Fin k, sphereBallOpen hn b i ≃ₜ ({b}ᶜ : Set (TopCat.sphere.{0} n))
  quotientHomeomorph :
    Hatcher.Relative.pointQuotient (TopPair.ofSubset (sphereBallUnion n hn k b)ᶜ) ≃ₜ
      Hatcher.PointedWedge (fun _ : Fin k ↦ TopCat.sphere.{0} n) (fun _ ↦ b)
  quotient_point :
    quotientHomeomorph
        (Hatcher.Relative.pointQuotientPoint
          (TopPair.ofSubset (sphereBallUnion n hn k b)ᶜ)) =
      Hatcher.PointedWedge.basepoint (fun _ : Fin k ↦ b)
  quotient_ball :
    ∀ (i : Fin k) (x : sphereBallOpen hn b i),
      quotientHomeomorph
          (Hatcher.Relative.pointQuotientProjection
            (TopPair.ofSubset (sphereBallUnion n hn k b)ᶜ) x.1) =
        Hatcher.PointedWedge.inclusion (fun _ : Fin k ↦ b) i (ballChart i x).1

private theorem sphere_ball_pinch_data_nonempty (n : ℕ) (hn : 0 < n) (k : ℕ) :
    Nonempty (SphereBallPinchData n hn k) := by
  classical
  let : T2Space (TopCat.sphere.{0} n) :=
    (sphereULiftHomeomorph.{0} n).isEmbedding.t2Space
  let : CompactSpace (TopCat.sphere.{0} n) :=
    Function.Surjective.compactSpace
      (sphereULiftHomeomorph.{0} n).symm.continuous
      (sphereULiftHomeomorph.{0} n).symm.surjective
  obtain ⟨b, haxis, hreflection, hj, hclosed, hballs⟩ :=
    finite_disjoint_sphere_balls n hn k
  change Topology.IsOpenEmbedding (sphereBallEmbedding n b) at hj
  change Pairwise (fun i j : Fin k ↦
    Disjoint (sphereBallClosed hn b i) (sphereBallClosed hn b j)) at hclosed
  let E := EuclideanSpace ℝ (Fin n)
  let e := puncturedSphereHomeomorphEuclidean n b
  let B : Fin k → Set (TopCat.sphere.{0} n) := fun i ↦ sphereBallOpen hn b i
  let C : Fin k → Set (TopCat.sphere.{0} n) := fun i ↦ sphereBallClosed hn b i
  let V : Set (TopCat.sphere.{0} n) := sphereBallUnion n hn k b
  have hOpen : ∀ i : Fin k, IsOpen (B i) := by
    intro i
    exact (hballs i).2.2.2.2.1
  have hBC : ∀ i : Fin k, B i ⊆ C i := by
    intro i
    exact Set.image_mono ball_subset_closedBall
  have hDisjoint : Pairwise (fun i j : Fin k ↦ Disjoint (B i) (B j)) := by
    intro i j hij
    exact (hclosed hij).mono (hBC i) (hBC j)
  have hV : IsOpen V := isOpen_iUnion hOpen
  have hbV : b ∉ V := by
    intro hb
    rcases Set.mem_iUnion.mp hb with ⟨i, hi⟩
    exact (hballs i).2.2.1 (hBC i hi)
  have hVc : (Vᶜ).Nonempty := ⟨b, hbV⟩
  let : ∀ i : Fin k, LocallyCompactSpace (B i) :=
    fun i ↦ (hOpen i).locallyCompactSpace
  let : ∀ i : Fin k, T2Space (B i) := fun i ↦ inferInstance
  let eta : ∀ i : Fin k, B i ≃ₜ E := fun i ↦
    (hj.isEmbedding.homeomorphImage (ball (sphereBallCenter hn i) 1)).symm.trans
      (((Homeomorph.unitBall : E ≃ₜ ball (0 : E) 1).trans
        (OpenPartialHomeomorph.unitBallBall (sphereBallCenter hn i) (1 : ℝ)
          zero_lt_one).toHomeomorphSourceTarget).symm)
  let H : ∀ i : Fin k, B i ≃ₜ ({b}ᶜ : Set (TopCat.sphere.{0} n)) :=
    fun i ↦ (eta i).trans e.symm
  have hjRange :
      Set.range (sphereBallEmbedding n b) = ({b}ᶜ : Set (TopCat.sphere.{0} n)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).property
    · intro hx
      let x' : ({b}ᶜ : Set (TopCat.sphere.{0} n)) := ⟨x, hx⟩
      refine ⟨e x', ?_⟩
      exact congrArg Subtype.val (e.symm_apply_apply x')
  let theta : OnePoint E ≃ₜ TopCat.sphere.{0} n :=
    OnePoint.equivOfIsEmbeddingOfRangeEq b (sphereBallEmbedding n b)
      hj.isEmbedding hjRange
  let phi : ∀ i : Fin k, OnePoint (B i) ≃ₜ TopCat.sphere.{0} n :=
    fun i ↦ (eta i).onePointCongr.trans theta
  have hPhiInfinity : ∀ i : Fin k, phi i (∞ : OnePoint (B i)) = b := by
    intro i
    change theta (∞ : OnePoint E) = b
    exact OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty b
      (sphereBallEmbedding n b) hj.isEmbedding hjRange
  have hPhiCoe :
      ∀ (i : Fin k) (x : B i), phi i (x : OnePoint (B i)) = (H i x).1 := by
    intro i x
    change theta ((eta i x : E) : OnePoint E) =
      sphereBallEmbedding n b (eta i x)
    exact OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe b
      (sphereBallEmbedding n b) hj.isEmbedding hjRange (eta i x)
  let P : TopPair.{0} := TopPair.ofSubset Vᶜ
  let A : Hatcher.Relative.pointQuotient P ≃ₜ OnePoint V :=
    Hatcher.Relative.compactComplementQuotientOnePointHomeomorph
      (TopCat.sphere.{0} n) V hV hVc
  let U : (Σ i : Fin k, B i) ≃ₜ V :=
    Hatcher.Topology.sigmaSubtypeHomeomorphUnion B hDisjoint hOpen
  let F :
      OnePoint (Σ i : Fin k, B i) ≃ₜ
        Hatcher.PointedWedge (fun i : Fin k ↦ OnePoint (B i))
          (fun i ↦ (∞ : OnePoint (B i))) :=
    Hatcher.Relative.finiteOnePointSigmaWedgeHomeomorph
      (fun i : Fin k ↦ TopCat.of (B i))
  let G :
      Hatcher.PointedWedge (fun i : Fin k ↦ OnePoint (B i))
          (fun i ↦ (∞ : OnePoint (B i))) ≃ₜ
        Hatcher.PointedWedge (fun _ : Fin k ↦ TopCat.sphere.{0} n) (fun _ ↦ b) :=
    Hatcher.PointedWedge.homeomorphCongr
      (fun i : Fin k ↦ (∞ : OnePoint (B i))) (fun _ ↦ b) phi hPhiInfinity
  let Q :
      Hatcher.Relative.pointQuotient P ≃ₜ
        Hatcher.PointedWedge (fun _ : Fin k ↦ TopCat.sphere.{0} n) (fun _ ↦ b) :=
    A.trans (U.symm.onePointCongr.trans (F.trans G))
  have hGPoint :
      G (Hatcher.PointedWedge.basepoint (fun i : Fin k ↦ (∞ : OnePoint (B i)))) =
        Hatcher.PointedWedge.basepoint (fun _ : Fin k ↦ b) := by
    rfl
  have hGInclusion :
      ∀ (i : Fin k) (x : OnePoint (B i)),
        G (Hatcher.PointedWedge.inclusion (fun j : Fin k ↦ (∞ : OnePoint (B j))) i x) =
          Hatcher.PointedWedge.inclusion (fun _ : Fin k ↦ b) i (phi i x) := by
    intro i x
    rfl
  have hAPoint :
      A (Hatcher.Relative.pointQuotientPoint P) = (∞ : OnePoint V) :=
    Hatcher.Relative.compactComplementQuotientOnePointHomeomorph_apply_point
      (TopCat.sphere.{0} n) V hV hVc
  have hFPoint :
      F (∞ : OnePoint (Σ i : Fin k, B i)) =
        Hatcher.PointedWedge.basepoint (fun i : Fin k ↦ (∞ : OnePoint (B i))) :=
    Hatcher.Relative.finite_one_point_sigma_wedge_homeomorph_apply_infty
      (fun i : Fin k ↦ TopCat.of (B i))
  have hQPoint :
      Q (Hatcher.Relative.pointQuotientPoint P) =
        Hatcher.PointedWedge.basepoint (fun _ : Fin k ↦ b) := by
    change G (F (U.symm.onePointCongr (A (Hatcher.Relative.pointQuotientPoint P)))) = _
    rw [hAPoint]
    change G (F (∞ : OnePoint (Σ i : Fin k, B i))) = _
    rw [hFPoint]
    exact hGPoint
  have hQBall :
      ∀ (i : Fin k) (x : B i),
        Q (Hatcher.Relative.pointQuotientProjection P x.1) =
          Hatcher.PointedWedge.inclusion (fun _ : Fin k ↦ b) i (H i x).1 := by
    intro i x
    let v : V := ⟨x.1, Set.mem_iUnion.mpr ⟨i, x.2⟩⟩
    have hAv :
        A (Hatcher.Relative.pointQuotientProjection P x.1) = (v : OnePoint V) :=
      Hatcher.Relative.compactComplementQuotientOnePointHomeomorph_apply_projection
        (TopCat.sphere.{0} n) V hV hVc v
    have hUv : U.symm v = (⟨i, x⟩ : Σ j : Fin k, B j) :=
      Hatcher.Topology.sigmaSubtypeHomeomorphUnion_symm_apply_mk
        B hDisjoint hOpen i x
    have hFx :
        F ((⟨i, x⟩ : Σ j : Fin k, B j) : OnePoint (Σ j : Fin k, B j)) =
          Hatcher.PointedWedge.inclusion
            (fun j : Fin k ↦ (∞ : OnePoint (B j))) i (x : OnePoint (B i)) :=
      Hatcher.Relative.finite_one_point_sigma_wedge_homeomorph_apply_coe
        (fun j : Fin k ↦ TopCat.of (B j)) i x
    change G (F (U.symm.onePointCongr
      (A (Hatcher.Relative.pointQuotientProjection P x.1)))) = _
    rw [hAv]
    change G (F ((U.symm v : Σ j : Fin k, B j) :
      OnePoint (Σ j : Fin k, B j))) = _
    rw [hUv, hFx, hGInclusion, hPhiCoe]
  refine ⟨{
    b := b
    last_axis := haxis
    zeroth_reflection := hreflection
    embedding_open := hj
    closed_disjoint := hclosed
    closed_properties := ?_
    ballChart := H
    quotientHomeomorph := Q
    quotient_point := hQPoint
    quotient_ball := hQBall }⟩
  intro i
  delta sphereBallClosed sphereBallOpen sphereBallEmbedding sphereBallCenter
  exact hballs i

/-- The actual complement-collapse sphere pinch into the pointed wedge of
the prescribed number of spheres, with the empty family included. -/
noncomputable def sphereBallPinch (n : ℕ) (hn : 0 < n) (k : ℕ) :
    SphereBallPinchData n hn k :=
  Classical.choice (sphere_ball_pinch_data_nonempty n hn k)

namespace SphereBallPinchData

variable {n k : ℕ} {hn : 0 < n}

/-- The pinch map is the actual point-quotient projection followed by the
constructed quotient homeomorphism. -/
noncomputable def pinchMap (D : SphereBallPinchData n hn k) :
    C(TopCat.sphere.{0} n,
      Hatcher.PointedWedge (fun _ : Fin k ↦ TopCat.sphere.{0} n) (fun _ ↦ D.b)) :=
  (⟨D.quotientHomeomorph, D.quotientHomeomorph.continuous⟩ :
    C(Hatcher.Relative.pointQuotient
        (TopPair.ofSubset (sphereBallUnion n hn k D.b)ᶜ),
      Hatcher.PointedWedge (fun _ : Fin k ↦ TopCat.sphere.{0} n) (fun _ ↦ D.b))).comp
    (Hatcher.Relative.pointQuotientProjection
      (TopPair.ofSubset (sphereBallUnion n hn k D.b)ᶜ)).hom

/-- On each actual open ball the pinch is its punctured-sphere chart
followed by the corresponding wedge inclusion. -/
theorem pinch_map_apply_ball (D : SphereBallPinchData n hn k)
    (i : Fin k) (x : sphereBallOpen hn D.b i) :
    D.pinchMap x.1 =
      Hatcher.PointedWedge.inclusion (fun _ : Fin k ↦ D.b) i (D.ballChart i x).1 :=
  D.quotient_ball i x

/-- Every point outside the actual open-ball union maps to the wedge point. -/
theorem pinch_map_apply_compl (D : SphereBallPinchData n hn k)
    (x : TopCat.sphere.{0} n) (hx : x ∉ sphereBallUnion n hn k D.b) :
    D.pinchMap x = Hatcher.PointedWedge.basepoint (fun _ : Fin k ↦ D.b) := by
  let P : TopPair.{0} := TopPair.ofSubset (sphereBallUnion n hn k D.b)ᶜ
  have hqx :
      Hatcher.Relative.pointQuotientProjection P x =
        Hatcher.Relative.pointQuotientPoint P := by
    change x ∈ Hatcher.Relative.pointQuotientProjection P ⁻¹'
      {Hatcher.Relative.pointQuotientPoint P}
    rw [Hatcher.Relative.pointQuotientProjection_preimage_point]
    exact ⟨⟨x, hx⟩, rfl⟩
  change D.quotientHomeomorph (Hatcher.Relative.pointQuotientProjection P x) = _
  rw [hqx]
  exact D.quotient_point

/-- The continuous wedge selector that preserves the chosen summand and
sends every other summand to the same actual point b. -/
noncomputable def summandSelector (D : SphereBallPinchData n hn k) (i : Fin k) :
    C(Hatcher.PointedWedge (fun _ : Fin k ↦ TopCat.sphere.{0} n) (fun _ ↦ D.b),
      TopCat.sphere.{0} n) :=
  Hatcher.PointedWedge.desc (fun _ : Fin k ↦ D.b) D.b
    (fun j ↦ if j = i then ContinuousMap.id (TopCat.sphere.{0} n)
      else ContinuousMap.const (TopCat.sphere.{0} n) D.b)
    (by
      intro j
      by_cases hji : j = i <;> simp [hji])

@[simp]
theorem summand_selector_apply_basepoint (D : SphereBallPinchData n hn k)
    (i : Fin k) :
    D.summandSelector i (Hatcher.PointedWedge.basepoint (fun _ : Fin k ↦ D.b)) = D.b :=
  rfl

/-- The selector's value on every actual summand, including the basepoint. -/
theorem summand_selector_apply_inclusion (D : SphereBallPinchData n hn k)
    (i j : Fin k) (x : TopCat.sphere.{0} n) :
    D.summandSelector i (Hatcher.PointedWedge.inclusion (fun _ : Fin k ↦ D.b) j x) =
      if j = i then x else D.b := by
  by_cases hji : j = i <;> simp [summandSelector, hji]

/-- The continuous sphere component collapse obtained from the actual
pinch map and the corresponding continuous wedge selector. -/
noncomputable def componentCollapse (D : SphereBallPinchData n hn k) (i : Fin k) :
    C(TopCat.sphere.{0} n, TopCat.sphere.{0} n) :=
  (D.summandSelector i).comp D.pinchMap

/-- The chosen ball maps through its actual punctured-sphere chart. -/
theorem component_collapse_apply_ball (D : SphereBallPinchData n hn k)
    (i : Fin k) (x : sphereBallOpen hn D.b i) :
    D.componentCollapse i x.1 = (D.ballChart i x).1 := by
  change D.summandSelector i (D.pinchMap x.1) = _
  rw [pinch_map_apply_ball, summand_selector_apply_inclusion]
  simp

/-- Every other open ball is collapsed to the actual omitted point. -/
theorem component_collapse_apply_other (D : SphereBallPinchData n hn k)
    (i j : Fin k) (hji : j ≠ i) (x : sphereBallOpen hn D.b j) :
    D.componentCollapse i x.1 = D.b := by
  change D.summandSelector i (D.pinchMap x.1) = _
  rw [pinch_map_apply_ball, summand_selector_apply_inclusion]
  simp [hji]

/-- The component collapse sends the complement of the union to b. -/
theorem component_collapse_apply_compl (D : SphereBallPinchData n hn k)
    (i : Fin k) (x : TopCat.sphere.{0} n)
    (hx : x ∉ sphereBallUnion n hn k D.b) :
    D.componentCollapse i x = D.b := by
  change D.summandSelector i (D.pinchMap x) = _
  rw [pinch_map_apply_compl D x hx]
  exact summand_selector_apply_basepoint D i

/-- A component collapse is constant at b off its selected open ball. -/
theorem component_collapse_apply_not_mem (D : SphereBallPinchData n hn k)
    (i : Fin k) (x : TopCat.sphere.{0} n) (hx : x ∉ sphereBallOpen hn D.b i) :
    D.componentCollapse i x = D.b := by
  by_cases hxV : x ∈ sphereBallUnion n hn k D.b
  · rcases Set.mem_iUnion.mp hxV with ⟨j, hxj⟩
    have hji : j ≠ i := by
      intro h
      subst j
      exact hx hxj
    exact component_collapse_apply_other D i j hji ⟨x, hxj⟩
  · exact component_collapse_apply_compl D i x hxV

/-- For zero balls, the actual pinch into the actual empty pointed wedge
is the constant map to its retained basepoint. -/
theorem pinch_map_zero (D : SphereBallPinchData n hn 0) :
    D.pinchMap = ContinuousMap.const (TopCat.sphere.{0} n)
      (Hatcher.PointedWedge.basepoint (fun _ : Fin 0 ↦ D.b)) := by
  apply ContinuousMap.ext
  intro x
  apply pinch_map_apply_compl D x
  intro hx
  rcases Set.mem_iUnion.mp hx with ⟨i, _⟩
  exact Fin.elim0 i

/-- The based continuous map from the actual empty wedge to the sphere. -/
noncomputable def emptyWedgeToSphere (D : SphereBallPinchData n hn 0) :
    C(Hatcher.PointedWedge (fun _ : Fin 0 ↦ TopCat.sphere.{0} n) (fun _ ↦ D.b),
      TopCat.sphere.{0} n) :=
  Hatcher.PointedWedge.desc (fun _ : Fin 0 ↦ D.b) D.b
    (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)

/-- The sphere map associated with the empty pinch family. -/
noncomputable def emptySphereMap (D : SphereBallPinchData n hn 0) :
    C(TopCat.sphere.{0} n, TopCat.sphere.{0} n) :=
  D.emptyWedgeToSphere.comp D.pinchMap

/-- The zero-family sphere map is the actual constant map at the same b. -/
theorem empty_sphere_map_eq_const (D : SphereBallPinchData n hn 0) :
    D.emptySphereMap = ContinuousMap.const (TopCat.sphere.{0} n) D.b := by
  apply ContinuousMap.ext
  intro x
  change D.emptyWedgeToSphere (D.pinchMap x) = D.b
  have hq :
      D.pinchMap x = Hatcher.PointedWedge.basepoint (fun _ : Fin 0 ↦ D.b) :=
    DFunLike.congr_fun (pinch_map_zero D) x
  rw [hq]
  rfl

end SphereBallPinchData

end Hatcher.Sphere

namespace Hatcher.Sphere

open CategoryTheory Topology
open scoped unitInterval

universe u

/-- An actual open neighborhood and fixed-point contraction make the
singleton inclusion in every sphere a good pair, including dimension zero. -/
noncomputable def sphereSingletonGoodPairData
    (n : ℕ) (b : TopCat.sphere.{u} n) :
    Hatcher.Relative.GoodPairData
      (TopPair.ofSubset ({b} : Set (TopCat.sphere.{u} n))) := by
  classical
  let _ : T2Space (TopCat.sphere.{u} n) :=
    (sphereULiftHomeomorph.{u} n).isEmbedding.t2Space
  have geometry : ∃ (V : Set (TopCat.sphere.{u} n)) (hb : b ∈ V),
      IsOpen V ∧ Nonempty
        ((ContinuousMap.id V).HomotopyRel
          (ContinuousMap.const V ⟨b, hb⟩) {⟨b, hb⟩}) := by
    cases n with
    | zero =>
        let e := zeroSphereIsoTwoPoint.{u}
        have hinj : Function.Injective e.hom :=
          (TopCat.mono_iff_injective e.hom).mp (by infer_instance)
        let _ : Finite (TopCat.sphere.{u} 0) :=
          Finite.of_injective e.hom hinj
        let _ : DiscreteTopology (TopCat.sphere.{u} 0) := inferInstance
        refine ⟨{b}, by simp, isOpen_discrete _, ⟨?_⟩⟩
        exact
          { toFun := fun q => q.2
            continuous_toFun := continuous_snd
            map_zero_left := fun _ => rfl
            map_one_left := fun _ => Subsingleton.elim _ _
            prop' := fun _ _ _ => rfl }
    | succ k =>
        let raw : RawSphere (k + 1) := sphereULiftHomeomorph.{u} (k + 1) b
        let p : TopCat.sphere.{u} (k + 1) :=
          (sphereULiftHomeomorph.{u} (k + 1)).symm (-raw)
        have hbp : b ≠ p := by
          intro h
          have hraw : raw = -raw :=
            (congrArg (sphereULiftHomeomorph.{u} (k + 1)) h).trans
              ((sphereULiftHomeomorph.{u} (k + 1)).apply_symm_apply (-raw))
          exact (ne_neg_of_mem_unit_sphere ℝ raw) hraw
        let V : Set (TopCat.sphere.{u} (k + 1)) := {p}ᶜ
        have hb : b ∈ V := by
          simpa only [V, Set.mem_compl_iff, Set.mem_singleton_iff] using hbp
        have hV : IsOpen V := isClosed_singleton.isOpen_compl
        let transfer : TopCat.sphere.{u} (k + 1) ≃ₜ
            TopCat.sphere.{0} (k + 1) :=
          (sphereULiftHomeomorph.{u} (k + 1)).trans
            (sphereULiftHomeomorph.{0} (k + 1)).symm
        let p₀ : TopCat.sphere.{0} (k + 1) := transfer p
        have hmem : ∀ x : TopCat.sphere.{u} (k + 1),
            x ∈ V ↔ transfer x ∈ ({p₀}ᶜ : Set (TopCat.sphere.{0} (k + 1))) := by
          intro x
          simp only [V, p₀, Set.mem_compl_iff, Set.mem_singleton_iff]
          constructor
          · intro hx hxp
            exact hx (transfer.injective hxp)
          · intro hx hxp
            exact hx (congrArg transfer hxp)
        let e : V ≃ₜ EuclideanSpace ℝ (Fin (k + 1)) :=
          (transfer.subtype hmem).trans
            (puncturedSphereHomeomorphEuclidean (k + 1) p₀)
        let bV : V := ⟨b, hb⟩
        let center := e bV
        refine ⟨V, hb, hV, ⟨?_⟩⟩
        exact
          { toFun := fun q =>
              e.symm ((1 - (q.1 : ℝ)) • e q.2 + (q.1 : ℝ) • center)
            continuous_toFun := by
              have ht : Continuous (fun q : I × V => (q.1 : ℝ)) :=
                continuous_subtype_val.comp continuous_fst
              have he : Continuous (fun q : I × V => e q.2) :=
                e.continuous.comp continuous_snd
              exact e.symm.continuous.comp
                (((continuous_const.sub ht).smul he).add (ht.smul continuous_const))
            map_zero_left := by
              intro x
              change e.symm ((1 - (0 : ℝ)) • e x + (0 : ℝ) • center) = x
              simp only [sub_zero, one_smul, zero_smul, add_zero]
              exact e.symm_apply_apply x
            map_one_left := by
              intro x
              change e.symm ((1 - (1 : ℝ)) • e x + (1 : ℝ) • center) = bV
              simp only [sub_self, zero_smul, one_smul, zero_add]
              exact e.symm_apply_apply bV
            prop' := by
              intro t x hx
              have hxb : x = bV := Set.mem_singleton_iff.mp hx
              subst x
              change e.symm ((1 - (t : ℝ)) • center + (t : ℝ) • center) = bV
              rw [← add_smul, sub_add_cancel, one_smul]
              exact e.symm_apply_apply bV }
  obtain ⟨V, hb, hV, ⟨H⟩⟩ := geometry
  let P : TopPair.{u} := TopPair.ofSubset ({b} : Set (TopCat.sphere.{u} n))
  have hrange : Set.range P.map = ({b} : Set (TopCat.sphere.{u} n)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hinterior : Set.range P.map ⊆ interior V := by
    rw [hrange, hV.interior_eq]
    exact Set.singleton_subset_iff.mpr hb
  let bV : V := ⟨b, hb⟩
  let inclusion : C(↑({b} : Set (TopCat.sphere.{u} n)), V) :=
    Hatcher.Relative.goodPairNeighborhoodInclusion P V
      (hinterior.trans interior_subset)
  let retract : C(V, ↑({b} : Set (TopCat.sphere.{u} n))) :=
    ContinuousMap.const V ⟨b, rfl⟩
  have hconstant : inclusion.comp retract = ContinuousMap.const V bV := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    rfl
  have hrangeInclusion : Set.range inclusion = ({bV} : Set V) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      exact Set.mem_singleton_iff.mp a.2
    · intro hx
      have hxb : x = bV := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨⟨b, rfl⟩, ?_⟩
      apply Subtype.ext
      rfl
  let deformation : Hatcher.StrongDeformationRetract inclusion :=
    { retract := retract
      retract_inclusion := by
        apply ContinuousMap.ext
        intro a
        exact Subsingleton.elim _ _
      deformation := by
        change (ContinuousMap.id V).HomotopyRel
          (inclusion.comp retract) (Set.range inclusion)
        rw [hconstant, hrangeInclusion]
        exact H }
  change Hatcher.Relative.GoodPairData P
  exact
    { nonempty := ⟨⟨b, rfl⟩⟩
      isClosed_range := by rw [hrange]; exact isClosed_singleton
      V := V
      range_subset_interior := hinterior
      strongDeformationRetract := deformation }

/-- Every point of every standard sphere forms a good singleton-inclusion
pair; the neighborhood and fixed-point contraction are constructed above. -/
theorem sphere_pointedPair_isGoodPair
    (n : ℕ) (b : TopCat.sphere.{u} n) :
    Hatcher.Relative.IsGoodPair
      (TopPair.ofSubset ({b} : Set (TopCat.sphere.{u} n))) :=
  ⟨sphereSingletonGoodPairData n b⟩

end Hatcher.Sphere
