import Hatcher.VanKampen.ConeAttachment
import Hatcher.Singular.GoodPair
import Hatcher.VanKampen.ConeAttachmentDeformation
import Hatcher.Sphere.HemisphereCharts
import Hatcher.Singular.PointQuotientTopology
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Analysis.Normed.Module.Connected

/-!
# A cone on the disk boundary is a disk

This module identifies the cone attachment of the identity map on the
boundary of the standard `n`-disk with the standard `n`-disk itself.
-/

noncomputable section

open Metric Set
open scoped unitInterval

namespace Hatcher.VanKampen.ConeAttachment

universe u

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private abbrev Boundary (n : ℕ) :=
  ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u)

private abbrev DiskPrequotient (n : ℕ) :=
  Prequotient (Boundary n) (Boundary n)

private def radial (n : ℕ) :
    DiskPrequotient n → Metric.closedBall (0 : E n) 1
  | Sum.inl x => ⟨x.down, mem_closedBall_zero_iff.2
      (mem_sphere_zero_iff_norm.mp x.down.2).le⟩
  | Sum.inr (Sum.inl _) => ⟨0, by simp⟩
  | Sum.inr (Sum.inr (x, t)) => ⟨(t : ℝ) • (x.down : E n), by
      rw [mem_closedBall_zero_iff, norm_smul_of_nonneg t.2.1,
        mem_sphere_zero_iff_norm.mp x.down.2, mul_one]
      exact t.2.2⟩

private theorem continuous_radial (n : ℕ) : Continuous (radial n) := by
  rw [continuous_sum_dom]
  constructor
  · exact (continuous_subtype_val.comp continuous_uliftDown).subtype_mk _
  · rw [continuous_sum_dom]
    constructor
    · exact continuous_const
    · apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_snd).smul
        (continuous_subtype_val.comp <| continuous_uliftDown.comp continuous_fst)

private theorem radial_normalForm (n : ℕ) (p : DiskPrequotient n) :
    radial n (normalForm (id : Boundary n → Boundary n) p) = radial n p := by
  cases p with
  | inl x => rfl
  | inr p =>
      cases p with
      | inl u => rfl
      | inr p =>
          rcases p with ⟨x, t⟩
          by_cases ht0 : t = 0
          · subst t
            simp [normalForm, radial]
          · by_cases ht1 : t = 1
            · subst t
              simp [normalForm, radial]
            · simp [normalForm, radial, ht0, ht1]

private theorem height_eq_zero_of_smul_eq_zero (n : ℕ)
    (x : Boundary n) (t : I) (h : (t : ℝ) • (x.down : E n) = 0) :
    t = 0 := by
  have hnorm := congrArg norm h
  have ht : (t : ℝ) = 0 := by
    simpa [norm_smul_of_nonneg t.2.1,
      mem_sphere_zero_iff_norm.mp x.down.2] using hnorm
  exact Subtype.ext ht

private theorem height_eq_one_of_sphere_eq_smul (n : ℕ)
    (x y : Boundary n) (t : I)
    (h : (x.down : E n) = (t : ℝ) • (y.down : E n)) :
    t = 1 := by
  have hnorm := congrArg norm h
  have ht : (t : ℝ) = 1 := by
    simpa [norm_smul_of_nonneg t.2.1,
      mem_sphere_zero_iff_norm.mp x.down.2,
      mem_sphere_zero_iff_norm.mp y.down.2] using hnorm.symm
  exact Subtype.ext ht

private theorem radial_coordinates_unique (n : ℕ)
    (x y : Boundary n) (t u : I) (ht : t ≠ 0) (hu : u ≠ 0)
    (h : (t : ℝ) • (x.down : E n) = (u : ℝ) • (y.down : E n)) :
    t = u ∧ x = y := by
  have hnorm := congrArg norm h
  have hnormx : ‖(t : ℝ) • (x.down : E n)‖ = (t : ℝ) := by
    rw [norm_smul_of_nonneg t.2.1,
      mem_sphere_zero_iff_norm.mp x.down.2, mul_one]
  have hnormy : ‖(u : ℝ) • (y.down : E n)‖ = (u : ℝ) := by
    rw [norm_smul_of_nonneg u.2.1,
      mem_sphere_zero_iff_norm.mp y.down.2, mul_one]
  have htu : t = u := Subtype.ext <| hnormx.symm.trans <| hnorm.trans hnormy
  subst u
  have hxy := congrArg (fun z : E n => (t : ℝ)⁻¹ • z) h
  simp [smul_smul, unitInterval.coe_ne_zero.mpr ht] at hxy
  exact ⟨rfl, ULift.ext x y <| Subtype.ext hxy⟩

private theorem normalForm_eq_of_radial_eq (n : ℕ)
    (p q : DiskPrequotient n) (h : radial n p = radial n q) :
    normalForm (id : Boundary n → Boundary n) p =
      normalForm (id : Boundary n → Boundary n) q := by
  cases p with
  | inl x =>
      cases q with
      | inl y =>
          have hraw : x.down = y.down := Subtype.ext <|
            congrArg (fun z : Metric.closedBall (0 : E n) 1 => (z : E n)) h
          have hxy : x = y := ULift.ext x y hraw
          subst y
          rfl
      | inr q =>
          cases q with
          | inl u =>
              have hval := congrArg
                (fun z : Metric.closedBall (0 : E n) 1 => (z : E n)) h
              change (x.down : E n) = 0 at hval
              exact False.elim <|
                (ne_of_mem_sphere x.down.2 one_ne_zero) hval
          | inr q =>
              rcases q with ⟨y, t⟩
              have hval := congrArg
                (fun z : Metric.closedBall (0 : E n) 1 => (z : E n)) h
              change (x.down : E n) = (t : ℝ) • (y.down : E n) at hval
              have ht := height_eq_one_of_sphere_eq_smul n x y t hval
              subst t
              have hraw : x.down = y.down := Subtype.ext <| by simpa using hval
              have hxy : x = y := ULift.ext x y hraw
              subst y
              simp [normalForm]
  | inr p =>
      cases p with
      | inl u =>
          cases q with
          | inl y =>
              have hval := congrArg
                (fun z : Metric.closedBall (0 : E n) 1 => (z : E n)) h
              change 0 = (y.down : E n) at hval
              exact False.elim <|
                (ne_of_mem_sphere y.down.2 one_ne_zero) hval.symm
          | inr q =>
              cases q with
              | inl v => rfl
              | inr q =>
                  rcases q with ⟨y, t⟩
                  have hval := congrArg
                    (fun z : Metric.closedBall (0 : E n) 1 => (z : E n)) h
                  change 0 = (t : ℝ) • (y.down : E n) at hval
                  have ht := height_eq_zero_of_smul_eq_zero n y t hval.symm
                  subst t
                  simp [normalForm]
      | inr p =>
          rcases p with ⟨x, t⟩
          cases q with
          | inl y =>
              have hval := congrArg
                (fun z : Metric.closedBall (0 : E n) 1 => (z : E n)) h
              change (t : ℝ) • (x.down : E n) = (y.down : E n) at hval
              have ht := height_eq_one_of_sphere_eq_smul n y x t hval.symm
              subst t
              have hraw : x.down = y.down := Subtype.ext <| by simpa using hval
              have hxy : x = y := ULift.ext x y hraw
              subst y
              simp [normalForm]
          | inr q =>
              cases q with
              | inl v =>
                  have hval := congrArg
                    (fun z : Metric.closedBall (0 : E n) 1 => (z : E n)) h
                  change (t : ℝ) • (x.down : E n) = 0 at hval
                  have ht := height_eq_zero_of_smul_eq_zero n x t hval
                  subst t
                  simp [normalForm]
              | inr q =>
                  rcases q with ⟨y, u⟩
                  have hval := congrArg
                    (fun z : Metric.closedBall (0 : E n) 1 => (z : E n)) h
                  change (t : ℝ) • (x.down : E n) =
                    (u : ℝ) • (y.down : E n) at hval
                  by_cases ht : t = 0
                  · subst t
                    have hu := height_eq_zero_of_smul_eq_zero n y u <| by
                      simpa using hval.symm
                    subst u
                    simp [normalForm]
                  · by_cases hu : u = 0
                    · subst u
                      have ht0 := height_eq_zero_of_smul_eq_zero n x t <| by
                        simpa using hval
                      exact False.elim <| ht ht0
                    · obtain ⟨htu, hxy⟩ :=
                        radial_coordinates_unique n x y t u ht hu hval
                      subst u
                      subst y
                      rfl

private def radialSection (n : ℕ) :
    Metric.closedBall (0 : E n) 1 → DiskPrequotient n := fun x =>
  if hx : (x : E n) = 0 then
    Sum.inr (Sum.inl ())
  else
    Sum.inr <| Sum.inr
      (ULift.up
        ⟨‖(x : E n)‖⁻¹ • (x : E n), mem_sphere_zero_iff_norm.2 <| by
          rw [norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
          exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)⟩,
        ⟨‖(x : E n)‖, norm_nonneg _, mem_closedBall_zero_iff.mp x.2⟩)

private theorem radial_rightInverse (n : ℕ) :
    Function.RightInverse (radialSection n) (radial n) := by
  intro x
  by_cases hx : (x : E n) = 0
  · simp [radialSection, radial, hx, Subtype.ext_iff]
  · simp [radialSection, radial, hx, smul_smul]

private def diskEquiv (n : ℕ) :
    Hatcher.VanKampen.ConeAttachment
        (id : Boundary n → Boundary n) ≃
      Metric.closedBall (0 : E n) 1 where
  toFun := Quotient.lift (radial n) fun a b hab => by
    change normalForm (id : Boundary n → Boundary n) a =
      normalForm (id : Boundary n → Boundary n) b at hab
    rw [← radial_normalForm n a, ← radial_normalForm n b, hab]
  invFun x := Quotient.mk'' (radialSection n x)
  left_inv q := Quotient.inductionOn' q fun p => by
    apply Quotient.sound'
    change normalForm (id : Boundary n → Boundary n)
        (radialSection n (radial n p)) =
      normalForm (id : Boundary n → Boundary n) p
    apply normalForm_eq_of_radial_eq
    exact radial_rightInverse n (radial n p)
  right_inv := radial_rightInverse n

private theorem continuous_diskEquiv (n : ℕ) : Continuous (diskEquiv n) := by
  apply Continuous.quotient_lift
  exact continuous_radial n

private def rawDiskHomeomorph (n : ℕ) :
    Hatcher.VanKampen.ConeAttachment
        (id : Boundary n → Boundary n) ≃ₜ
      Metric.closedBall (0 : E n) 1 := by
  let hq := isQuotientMap_quotientMk (id : Boundary n → Boundary n)
  letI : CompactSpace
      (Hatcher.VanKampen.ConeAttachment (id : Boundary n → Boundary n)) :=
    ⟨by
      rw [← hq.surjective.range_eq]
      exact isCompact_range hq.continuous⟩
  exact (diskEquiv n).toHomeomorphOfContinuousClosed
    (continuous_diskEquiv n) (continuous_diskEquiv n).isClosedMap

/-- Attaching a cone to the boundary of the standard `n`-disk by the identity
map recovers the standard `n`-disk. -/
def diskHomeomorph (n : ℕ) :
    Hatcher.VanKampen.ConeAttachment
        (id : ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u) →
          ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u)) ≃ₜ
      ((TopCat.disk.{u} n : TopCat.{u}) : Type u) :=
  (rawDiskHomeomorph n).trans Homeomorph.ulift.symm

/-- On the retained boundary, `diskHomeomorph` is the standard boundary
inclusion into the disk. -/
@[simp]
theorem diskHomeomorph_base_eq_diskBoundaryInclusion (n : ℕ)
    (x : ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u)) :
    diskHomeomorph n
        (base
          (id : ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u) →
            ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u)) x) =
      TopCat.diskBoundaryInclusion.{u} n x :=
  rfl

/-- The cone apex corresponds to the center of the disk. -/
@[simp]
theorem diskHomeomorph_apex (n : ℕ) :
    diskHomeomorph n
        (apex
          (id : ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u) →
            ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u))) =
      ULift.up.{u}
        (⟨0, by simp⟩ :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  rfl

/-- A cone cylinder point maps to its radial point in the disk. -/
@[simp]
theorem diskHomeomorph_cylinder (n : ℕ)
    (x : ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u)) (t : I) :
    diskHomeomorph n
        (cylinder
          (id : ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u) →
            ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u)) x t) =
      ULift.up.{u}
        (⟨(t : ℝ) • (x.down : EuclideanSpace ℝ (Fin n)), by
          rw [mem_closedBall_zero_iff, norm_smul_of_nonneg t.2.1,
            mem_sphere_zero_iff_norm.mp x.down.2, mul_one]
          exact t.2.2⟩ :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  rfl

end Hatcher.VanKampen.ConeAttachment

namespace Hatcher.Sphere

open CategoryTheory Topology
open Hatcher.VanKampen Hatcher.VanKampen.ConeAttachment

universe u

/-- The retained cone on the actual standard `n`-sphere. -/
def sphereCone (n : ℕ) : TopCat.{u} :=
  TopCat.of (ConeAttachment
    (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n))

/-- The canonical retained base of the standard sphere cone. -/
def sphereConeBase (n : ℕ) :
    TopCat.sphere.{u} n ⟶ sphereCone.{u} n :=
  TopCat.ofHom
    { toFun := base (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)
      continuous_toFun :=
        (isQuotientMap_quotientMk
          (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)).continuous.comp
          continuous_inl }

private theorem sphere_cone_base_is_closed_embedding (n : ℕ) :
    IsClosedEmbedding (sphereConeBase.{u} n) := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let B : Set E := Metric.sphere 0 1
  let D : Set E := Metric.closedBall 0 1
  have hBD : B ⊆ D := Metric.sphere_subset_closedBall
  have hB : IsClosed B := Metric.isClosed_sphere
  have hInclusion : IsClosedEmbedding (Set.inclusion hBD) :=
    IsClosedEmbedding.of_comp
      (IsEmbedding.subtypeVal : IsEmbedding ((↑) : D → E))
      hB.isClosedEmbedding_subtypeVal
  have hDisk : IsClosedEmbedding
      (TopCat.diskBoundaryInclusion.{u} (n + 1)) := by
    change IsClosedEmbedding (fun x : ULift.{u} B =>
      ULift.up (Set.inclusion hBD x.down))
    let eB : ULift.{u} B ≃ₜ B := Homeomorph.ulift
    let eD : ULift.{u} D ≃ₜ D := Homeomorph.ulift
    exact eD.symm.isClosedEmbedding.comp
      (hInclusion.comp eB.isClosedEmbedding)
  have hComp :
      diskHomeomorph.{u} (n + 1) ∘ sphereConeBase.{u} n =
        (TopCat.diskBoundaryInclusion.{u} (n + 1) :
          TopCat.sphere.{u} n → TopCat.disk.{u} (n + 1)) := by
    funext x
    exact diskHomeomorph_base_eq_diskBoundaryInclusion (n + 1) x
  rw [← hComp] at hDisk
  exact IsClosedEmbedding.of_comp
    (diskHomeomorph.{u} (n + 1)).isEmbedding hDisk

/-- The actual sphere cone paired with its retained standard sphere. -/
def sphereConePair (n : ℕ) : TopPair.{u} :=
  TopPair.of (sphereConeBase.{u} n)
    (sphere_cone_base_is_closed_embedding n).isEmbedding

/-- The open base-side cover gives genuine good-pair data on the sphere cone. -/
def sphereConeGoodPairData (n : ℕ) :
    Hatcher.Relative.GoodPairData (sphereConePair.{u} n) where
  nonempty := by
    obtain ⟨x, hx⟩ :=
      (NormedSpace.sphere_nonempty
        (x := (0 : EuclideanSpace ℝ (Fin (n + 1)))) (r := 1)).mpr
        (zero_le_one : (0 : ℝ) ≤ 1)
    exact ⟨ULift.up ⟨x, hx⟩⟩
  isClosed_range :=
    (sphere_cone_base_is_closed_embedding n).isClosed_range
  V := lowerCover (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)
  range_subset_interior := by
    change Set.range
        (base (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)) ⊆
      interior (lowerCover
        (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n))
    rw [(isOpen_lowerCover
      (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)).interior_eq]
    rintro _ ⟨x, rfl⟩
    exact (lowerBaseInclusion (ContinuousMap.id (TopCat.sphere.{u} n)) x).2
  strongDeformationRetract := by
    change Hatcher.StrongDeformationRetract
      (lowerBaseInclusion (ContinuousMap.id (TopCat.sphere.{u} n)))
    exact lowerStrongDeformationRetract _

/-- For every `n`, including zero, the actual sphere cone and its retained
base form a good pair with an open base neighborhood and contractible ambient
cone. Retained height zero is the apex, height one is the base, and the source
height is `1 - r`. -/
theorem sphere_cone_geometry (n : ℕ) :
    Hatcher.Relative.IsGoodPair (sphereConePair.{u} n) ∧
      IsOpen (sphereConeGoodPairData.{u} n).V ∧
      ContractibleSpace (sphereConePair.{u} n).fst ∧
      (∀ x : TopCat.sphere.{u} n,
        cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x 0 =
            apex (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) ∧
          cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x 1 =
            (sphereConePair.{u} n).map x) ∧
      (∀ r : I, (unitInterval.symm r : ℝ) = 1 - (r : ℝ)) := by
  refine ⟨⟨sphereConeGoodPairData n⟩, isOpen_lowerCover _, ?_, ?_, ?_⟩
  · let : ContractibleSpace
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
      Metric.contractibleSpace_closedBall (zero_le_one : (0 : ℝ) ≤ 1)
    exact ((diskHomeomorph.{u} (n + 1)).trans Homeomorph.ulift).contractibleSpace
  · intro x
    exact ⟨cylinder_zero _ x, cylinder_one _ x⟩
  · exact unitInterval.coe_symm_eq

end Hatcher.Sphere

namespace Hatcher.Sphere

open CategoryTheory Topology
open Hatcher.VanKampen.ConeAttachment

universe u

private def sphereConePreMap (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    Prequotient (TopCat.sphere.{u} n) (TopCat.sphere.{u} n) →
      Prequotient (TopCat.sphere.{u} n) (TopCat.sphere.{u} n)
  | Sum.inl x => Sum.inl (f x)
  | Sum.inr (Sum.inl a) => Sum.inr (Sum.inl a)
  | Sum.inr (Sum.inr (x, r)) => Sum.inr (Sum.inr (f x, r))

private theorem sphere_cone_pre_map_normal_form (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n)
    (p : Prequotient (TopCat.sphere.{u} n) (TopCat.sphere.{u} n)) :
    normalForm (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)
        (sphereConePreMap n f p) =
      sphereConePreMap n f
        (normalForm (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) p) := by
  rcases p with x | p
  · rfl
  · rcases p with a | ⟨x, r⟩
    · rfl
    · by_cases h0 : r = 0
      · subst r
        simp [normalForm, sphereConePreMap]
      · by_cases h1 : r = 1
        · subst r
          simp [normalForm, sphereConePreMap]
        · simp [normalForm, sphereConePreMap, h0, h1]

private theorem sphere_cone_pre_map_respects (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n)
    (a b : Prequotient (TopCat.sphere.{u} n) (TopCat.sphere.{u} n))
    (h : (setoid (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)).r a b) :
    (setoid (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)).r
      (sphereConePreMap n f a) (sphereConePreMap n f b) := by
  change normalForm (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) a =
    normalForm (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) b at h
  change normalForm (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)
      (sphereConePreMap n f a) =
    normalForm (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)
      (sphereConePreMap n f b)
  rw [sphere_cone_pre_map_normal_form n f a,
    sphere_cone_pre_map_normal_form n f b, h]

private def sphereConeMapFun (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    Hatcher.VanKampen.ConeAttachment
        (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) →
      Hatcher.VanKampen.ConeAttachment
        (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) :=
  Quotient.map'
    (s₁ := setoid (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n))
    (s₂ := setoid (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n))
    (sphereConePreMap n f) (sphere_cone_pre_map_respects n f)

private theorem continuous_sphere_cone_pre_map (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    Continuous (sphereConePreMap n f) := by
  rw [continuous_sum_dom]
  constructor
  · change Continuous (fun x : TopCat.sphere.{u} n =>
      (Sum.inl (f x) :
        Prequotient (TopCat.sphere.{u} n) (TopCat.sphere.{u} n)))
    exact continuous_inl.comp f.hom.continuous
  · rw [continuous_sum_dom]
    constructor
    · change Continuous (fun a : Unit =>
        (Sum.inr (Sum.inl a) :
          Prequotient (TopCat.sphere.{u} n) (TopCat.sphere.{u} n)))
      exact continuous_inr.comp continuous_inl
    · change Continuous (fun p : TopCat.sphere.{u} n × I =>
        (Sum.inr (Sum.inr (f p.1, p.2)) :
          Prequotient (TopCat.sphere.{u} n) (TopCat.sphere.{u} n)))
      exact continuous_inr.comp
        (continuous_inr.comp
          ((f.hom.continuous.comp continuous_fst).prodMk continuous_snd))

private theorem continuous_sphere_cone_map_fun (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    Continuous (sphereConeMapFun n f) := by
  apply (isQuotientMap_quotientMk
    (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)).continuous_iff.mpr
  change Continuous (fun p :
      Prequotient (TopCat.sphere.{u} n) (TopCat.sphere.{u} n) =>
    quotientMk (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)
      (sphereConePreMap n f p))
  exact (isQuotientMap_quotientMk
    (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)).continuous.comp
      (continuous_sphere_cone_pre_map n f)

/-- The continuous map of the retained sphere cone that applies `f` to the
sphere coordinate and preserves its height, including both endpoints. -/
def sphereConeMap (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    sphereCone.{u} n ⟶ sphereCone.{u} n :=
  TopCat.ofHom
    ⟨sphereConeMapFun n f, continuous_sphere_cone_map_fun n f⟩

/-- The retained base is mapped by the original sphere map. -/
@[simp]
theorem sphere_cone_map_base (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n)
    (x : TopCat.sphere.{u} n) :
    sphereConeMap n f (sphereConeBase n x) = sphereConeBase n (f x) :=
  rfl

/-- Every sphere cone map fixes the actual cone apex. -/
@[simp]
theorem sphere_cone_map_apex (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    sphereConeMap n f
        (apex (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)) =
      apex (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) :=
  rfl

/-- A cylinder point keeps its retained height and its sphere coordinate
is mapped by `f`. This holds also at height zero and height one. -/
@[simp]
theorem sphere_cone_map_cylinder (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n)
    (x : TopCat.sphere.{u} n) (r : I) :
    sphereConeMap n f
        (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x r) =
      cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) (f x) r :=
  rfl

/-- The sphere map and its cone map form the actual retained-base square. -/
theorem sphere_cone_map_base_square (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    f ≫ sphereConeBase n = sphereConeBase n ≫ sphereConeMap n f := by
  ext x
  exact (sphere_cone_map_base n f x).symm

/-- The cone-base pair map induced by a continuous map of the actual standard
sphere. The base component is exactly `f`; the ambient component preserves
retained height `r`, hence also Hatcher's height `t = 1 - r`. This construction
includes the zero-dimensional sphere and constant maps. -/
def sphereConePairMap (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    sphereConePair.{u} n ⟶ sphereConePair.{u} n :=
  TopPair.ofHom
    (X := sphereConePair.{u} n) (Y := sphereConePair.{u} n)
    (sphereConeMap n f) f (by
      change f ≫ sphereConeBase n = sphereConeBase n ≫ sphereConeMap n f
      exact sphere_cone_map_base_square n f)

/-- The ambient component of the induced pair map is the actual cone map. -/
@[simp]
theorem sphere_cone_pair_map_fst (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    TopPair.Hom.fst (sphereConePairMap n f) = sphereConeMap n f :=
  rfl

/-- The subspace component of the induced pair map is exactly `f`. -/
@[simp]
theorem sphere_cone_pair_map_snd (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    TopPair.Hom.snd (sphereConePairMap n f) = f :=
  rfl

/-- The identity sphere map induces the identity of the actual cone-base pair. -/
@[simp]
theorem sphere_cone_pair_map_id (n : ℕ) :
    sphereConePairMap n (𝟙 (TopCat.sphere.{u} n)) =
      𝟙 (sphereConePair.{u} n) := by
  apply MorphismProperty.Arrow.Hom.ext
  · rfl
  · change sphereConeMap n (𝟙 (TopCat.sphere.{u} n)) =
      𝟙 (sphereCone.{u} n)
    ext q
    change sphereConeMapFun n (𝟙 (TopCat.sphere.{u} n)) q = q
    refine Quotient.inductionOn q ?_
    intro p
    rcases p with x | p
    · rfl
    · rcases p with a | ⟨x, r⟩ <;> rfl

/-- Sphere cone pair maps preserve actual composition of sphere maps. -/
@[simp]
theorem sphere_cone_pair_map_comp (n : ℕ)
    (f g : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    sphereConePairMap n (f ≫ g) =
      sphereConePairMap n f ≫ sphereConePairMap n g := by
  apply MorphismProperty.Arrow.Hom.ext
  · rfl
  · change sphereConeMap n (f ≫ g) =
      sphereConeMap n f ≫ sphereConeMap n g
    ext q
    change sphereConeMapFun n (f ≫ g) q =
      sphereConeMapFun n g (sphereConeMapFun n f q)
    refine Quotient.inductionOn q ?_
    intro p
    rcases p with x | p
    · rfl
    · rcases p with a | ⟨x, r⟩ <;> rfl

end Hatcher.Sphere

namespace Hatcher.Sphere

open CategoryTheory Limits Topology
open Hatcher.Relative Hatcher.VanKampen.ConeAttachment

universe u

private def sphereConeSnocVector (m : ℕ)
    (w : EuclideanSpace ℝ (Fin m)) (z : ℝ) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.snoc (WithLp.ofLp w) z)

private theorem sphere_cone_snoc_vector_cast_succ (m : ℕ)
    (w : EuclideanSpace ℝ (Fin m)) (z : ℝ) (i : Fin m) :
    sphereConeSnocVector m w z i.castSucc = w i := by
  change Fin.snoc (α := fun _ : Fin (m + 1) => ℝ)
    (WithLp.ofLp w) z i.castSucc = w i
  simp only [Fin.snoc_castSucc]

private theorem sphere_cone_snoc_vector_last (m : ℕ)
    (w : EuclideanSpace ℝ (Fin m)) (z : ℝ) :
    sphereConeSnocVector m w z (Fin.last m) = z := by
  change Fin.snoc (α := fun _ : Fin (m + 1) => ℝ)
    (WithLp.ofLp w) z (Fin.last m) = z
  simp only [Fin.snoc_last]

private theorem sphere_cone_snoc_vector_norm_sq (m : ℕ)
    (w : EuclideanSpace ℝ (Fin m)) (z : ℝ) :
    ‖sphereConeSnocVector m w z‖ ^ 2 = ‖w‖ ^ 2 + z ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc,
    EuclideanSpace.real_norm_sq_eq]
  simp only [sphere_cone_snoc_vector_cast_succ, sphere_cone_snoc_vector_last]

private theorem sphere_cone_radicand_nonneg (r : I) :
    0 ≤ 1 - (2 * (r : ℝ) - 1) ^ 2 := by
  have h := mul_nonneg r.2.1 (sub_nonneg.mpr r.2.2)
  nlinarith

private theorem sphere_cone_radicand_pos (r : I) (h0 : r ≠ 0) (h1 : r ≠ 1) :
    0 < 1 - (2 * (r : ℝ) - 1) ^ 2 := by
  have h0r : (r : ℝ) ≠ 0 := unitInterval.coe_ne_zero.mpr h0
  have h1r : (r : ℝ) ≠ 1 := by
    intro h
    exact h1 (Subtype.ext h)
  have hr0 : 0 < (r : ℝ) := lt_of_le_of_ne r.2.1 h0r.symm
  have hr1 : (r : ℝ) < 1 := lt_of_le_of_ne r.2.2 h1r
  have h := mul_pos hr0 (sub_pos.mpr hr1)
  nlinarith

private def sphereConeCylinderVector (n : ℕ)
    (x : TopCat.sphere.{u} n) (r : I) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  sphereConeSnocVector (n + 1)
    (Real.sqrt (1 - (2 * (r : ℝ) - 1) ^ 2) • (sphereULiftHomeomorph n x).1)
    (2 * (r : ℝ) - 1)

private theorem sphere_cone_cylinder_vector_norm (n : ℕ)
    (x : TopCat.sphere.{u} n) (r : I) :
    ‖sphereConeCylinderVector n x r‖ = 1 := by
  have hsq : ‖sphereConeCylinderVector n x r‖ ^ 2 = 1 := by
    rw [sphereConeCylinderVector, sphere_cone_snoc_vector_norm_sq,
      norm_smul_of_nonneg (Real.sqrt_nonneg _),
      mem_sphere_zero_iff_norm.mp (sphereULiftHomeomorph n x).2, mul_one,
      Real.sq_sqrt (sphere_cone_radicand_nonneg r)]
    ring
  have hnonneg := norm_nonneg (sphereConeCylinderVector n x r)
  nlinarith

/-- The prescribed point of the next standard sphere at retained cylinder
height `r`. Its horizontal coordinate is multiplied by
`sqrt (1 - (2*r - 1)^2)` and its last coordinate is `2*r - 1`. -/
def sphereConeCylinderPoint (n : ℕ) (x : TopCat.sphere.{u} n) (r : I) :
    TopCat.sphere.{u} (n + 1) :=
  (sphereULiftHomeomorph (n + 1)).symm
    ⟨sphereConeCylinderVector n x r,
      mem_sphere_zero_iff_norm.2 (sphere_cone_cylinder_vector_norm n x r)⟩

/-- The complete Euclidean coordinate formula for a retained cylinder point. -/
theorem sphere_cone_cylinder_point_coordinates (n : ℕ)
    (x : TopCat.sphere.{u} n) (r : I) :
    ((sphereULiftHomeomorph (n + 1) (sphereConeCylinderPoint n x r)).1 :
        EuclideanSpace ℝ (Fin (n + 2))) =
      WithLp.toLp 2
        (Fin.snoc
          (fun i : Fin (n + 1) =>
            Real.sqrt (1 - (2 * (r : ℝ) - 1) ^ 2) *
              ((sphereULiftHomeomorph n x).1 :
                EuclideanSpace ℝ (Fin (n + 1))) i)
          (2 * (r : ℝ) - 1)) :=
  rfl

private theorem continuous_sphere_cone_cylinder_vector (n : ℕ) :
    Continuous (fun p : TopCat.sphere.{u} n × I =>
      sphereConeCylinderVector n p.1 p.2) := by
  let Z : TopCat.sphere.{u} n × I → ℝ := fun p => 2 * (p.2 : ℝ) - 1
  let A : TopCat.sphere.{u} n × I → ℝ := fun p => Real.sqrt (1 - (Z p) ^ 2)
  have hZ : Continuous Z := by
    dsimp [Z]
    exact (continuous_const.mul
      (continuous_subtype_val.comp continuous_snd)).sub continuous_const
  have hA : Continuous A := by
    dsimp [A]
    exact (continuous_const.sub (hZ.pow 2)).sqrt
  have hX : Continuous (fun p : TopCat.sphere.{u} n × I =>
      (sphereULiftHomeomorph n p.1).1) :=
    continuous_subtype_val.comp
      ((sphereULiftHomeomorph n).continuous.comp continuous_fst)
  change Continuous (fun p : TopCat.sphere.{u} n × I =>
    WithLp.toLp 2
      (Fin.snoc (α := fun _ : Fin (n + 2) => ℝ)
        (fun i : Fin (n + 1) =>
          A p * ((sphereULiftHomeomorph n p.1).1 :
            EuclideanSpace ℝ (Fin (n + 1))) i)
        (Z p)))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 2) => ℝ)).comp
  apply continuous_pi
  intro i
  cases i using Fin.lastCases with
  | last =>
      simp only [Fin.snoc_last]
      exact hZ
  | cast i =>
      simp only [Fin.snoc_castSucc]
      exact hA.mul
        ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i).comp hX)

private theorem continuous_sphere_cone_cylinder_point (n : ℕ) :
    Continuous (fun p : TopCat.sphere.{u} n × I =>
      sphereConeCylinderPoint n p.1 p.2) := by
  exact (sphereULiftHomeomorph (n + 1)).symm.continuous.comp
    ((continuous_sphere_cone_cylinder_vector n).subtype_mk
      (fun p => mem_sphere_zero_iff_norm.2
        (sphere_cone_cylinder_vector_norm n p.1 p.2)))

private theorem sphere_cone_cylinder_point_zero (n : ℕ)
    (x : TopCat.sphere.{u} n) :
    sphereConeCylinderPoint n x 0 = southPole.{u} n := by
  apply (sphereULiftHomeomorph (n + 1)).injective
  apply Subtype.ext
  change sphereConeCylinderVector n x 0 = -lastVector n
  apply PiLp.ext
  intro i
  cases i using Fin.lastCases <;>
    simp [sphereConeCylinderVector, sphere_cone_snoc_vector_cast_succ,
      sphere_cone_snoc_vector_last, lastVector]

private theorem sphere_cone_cylinder_point_one (n : ℕ)
    (x : TopCat.sphere.{u} n) :
    sphereConeCylinderPoint n x 1 = northPole.{u} n := by
  apply (sphereULiftHomeomorph (n + 1)).injective
  apply Subtype.ext
  change sphereConeCylinderVector n x 1 = lastVector n
  apply PiLp.ext
  intro i
  cases i using Fin.lastCases <;>
    norm_num [sphereConeCylinderVector, sphere_cone_snoc_vector_cast_succ,
      sphere_cone_snoc_vector_last, lastVector]

private def sphereConePreSphereMap (n : ℕ) :
    Prequotient (TopCat.sphere.{u} n) (TopCat.sphere.{u} n) →
      TopCat.sphere.{u} (n + 1)
  | Sum.inl _ => northPole n
  | Sum.inr (Sum.inl _) => southPole n
  | Sum.inr (Sum.inr (x, r)) => sphereConeCylinderPoint n x r

private theorem continuous_sphere_cone_pre_sphere_map (n : ℕ) :
    Continuous (sphereConePreSphereMap.{u} n) := by
  rw [continuous_sum_dom]
  constructor
  · exact continuous_const
  · rw [continuous_sum_dom]
    exact ⟨continuous_const, continuous_sphere_cone_cylinder_point n⟩

private theorem sphere_cone_pre_sphere_map_normal_form (n : ℕ)
    (p : Prequotient (TopCat.sphere.{u} n) (TopCat.sphere.{u} n)) :
    sphereConePreSphereMap n
        (normalForm (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) p) =
      sphereConePreSphereMap n p := by
  rcases p with x | p
  · rfl
  · rcases p with a | ⟨x, r⟩
    · rfl
    · by_cases h0 : r = 0
      · subst r
        simp [normalForm, sphereConePreSphereMap, sphere_cone_cylinder_point_zero]
      · by_cases h1 : r = 1
        · subst r
          simp [normalForm, sphereConePreSphereMap, sphere_cone_cylinder_point_one]
        · simp [normalForm, sphereConePreSphereMap, h0, h1]

private def sphereConeToSphereFun (n : ℕ) :
    Hatcher.VanKampen.ConeAttachment
        (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) →
      TopCat.sphere.{u} (n + 1) :=
  Quotient.lift (sphereConePreSphereMap n) fun a b hab => by
    change normalForm (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) a =
      normalForm (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) b at hab
    rw [← sphere_cone_pre_sphere_map_normal_form n a,
      ← sphere_cone_pre_sphere_map_normal_form n b, hab]

private theorem continuous_sphere_cone_to_sphere_fun (n : ℕ) :
    Continuous (sphereConeToSphereFun.{u} n) := by
  apply (isQuotientMap_quotientMk
    (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)).continuous_iff.mpr
  change Continuous (sphereConePreSphereMap n)
  exact continuous_sphere_cone_pre_sphere_map n

private def sphereConeToSphereMap (n : ℕ) :
    (sphereConePair.{u} n).fst ⟶ TopCat.sphere.{u} (n + 1) :=
  TopCat.ofHom
    ⟨sphereConeToSphereFun n, continuous_sphere_cone_to_sphere_fun n⟩

private def sphereConeNorthPointMap (n : ℕ) :
    TopCat.of PUnit ⟶ TopCat.sphere.{u} (n + 1) :=
  TopCat.ofHom ⟨fun _ => northPole n, continuous_const⟩

private theorem sphere_cone_to_sphere_base_square (n : ℕ) :
    (sphereConePair.{u} n).map ≫ sphereConeToSphereMap n =
      pointQuotientCollapse (sphereConePair.{u} n) ≫ sphereConeNorthPointMap n := by
  ext x
  change sphereConeToSphereFun n
    (base (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x) = northPole n
  rfl

/-- The continuous map from the actual cone-base point quotient to the next
standard sphere, descended through the retained cone and the TopCat pushout. -/
def sphereConeQuotientMap (n : ℕ) :
    pointQuotient (sphereConePair.{u} n) ⟶ TopCat.sphere.{u} (n + 1) :=
  pushout.desc (sphereConeToSphereMap n) (sphereConeNorthPointMap n)
    (sphere_cone_to_sphere_base_square n)

private theorem sphere_cone_quotient_map_projection (n : ℕ)
    (c : (sphereConePair.{u} n).fst) :
    sphereConeQuotientMap n
        (pointQuotientProjection (sphereConePair.{u} n) c) =
      sphereConeToSphereMap n c := by
  have h : pointQuotientProjection (sphereConePair.{u} n) ≫
      sphereConeQuotientMap n = sphereConeToSphereMap n := by
    dsimp [pointQuotientProjection, sphereConeQuotientMap, pointQuotient]
    apply pushout.inl_desc
  exact ConcreteCategory.congr_hom h c

private theorem sphere_cone_quotient_map_point (n : ℕ) :
    sphereConeQuotientMap n (pointQuotientPoint (sphereConePair.{u} n)) =
      northPole.{u} n := by
  have h : pointQuotientPointInclusion (sphereConePair.{u} n) ≫
      sphereConeQuotientMap n = sphereConeNorthPointMap n := by
    dsimp [pointQuotientPointInclusion, sphereConeQuotientMap, pointQuotient]
    apply pushout.inr_desc
  exact ConcreteCategory.congr_hom h PUnit.unit

private theorem sphere_cone_quotient_map_apex (n : ℕ) :
    sphereConeQuotientMap n
        (pointQuotientProjection (sphereConePair.{u} n)
          (apex (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n))) =
      southPole.{u} n := by
  exact sphere_cone_quotient_map_projection n
    (apex (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n))

private theorem sphere_cone_quotient_map_cylinder (n : ℕ)
    (x : TopCat.sphere.{u} n) (r : I) :
    sphereConeQuotientMap n
        (pointQuotientProjection (sphereConePair.{u} n)
          (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x r)) =
      sphereConeCylinderPoint n x r := by
  exact sphere_cone_quotient_map_projection n
    (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x r)

private theorem sphere_cone_quotient_projection_base (n : ℕ)
    (x : TopCat.sphere.{u} n) :
    pointQuotientProjection (sphereConePair.{u} n)
        (base (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x) =
      pointQuotientPoint (sphereConePair.{u} n) := by
  have h : base (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x ∈
      pointQuotientProjection (sphereConePair.{u} n) ⁻¹'
        {pointQuotientPoint (sphereConePair.{u} n)} := by
    rw [pointQuotientProjection_preimage_point]
    exact ⟨x, rfl⟩
  exact h

private theorem sphere_cone_quotient_cylinder_representative (n : ℕ)
    (q : pointQuotient (sphereConePair.{u} n)) :
    ∃ x : TopCat.sphere.{u} n, ∃ r : I,
      pointQuotientProjection (sphereConePair.{u} n)
        (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x r) = q := by
  let : Nonempty (sphereConePair.{u} n).snd := (sphereConeGoodPairData n).nonempty
  obtain ⟨c, hc⟩ := pointQuotientProjection_surjective (sphereConePair.{u} n) q
  change Hatcher.VanKampen.ConeAttachment
    (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) at c
  have hrep : ∃ x : TopCat.sphere.{u} n, ∃ r : I,
      cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x r = c := by
    refine Quotient.inductionOn c ?_
    intro p
    rcases p with x | p
    · exact ⟨x, 1, cylinder_one _ x⟩
    · rcases p with a | ⟨x, r⟩
      · cases a
        let x : TopCat.sphere.{u} n := Classical.choice (sphereConeGoodPairData n).nonempty
        exact ⟨x, 0, cylinder_zero _ x⟩
      · exact ⟨x, r, rfl⟩
  obtain ⟨x, r, hr⟩ := hrep
  exact ⟨x, r, (congrArg (pointQuotientProjection (sphereConePair.{u} n)) hr).trans hc⟩

private theorem sphere_cone_cylinder_point_last (n : ℕ)
    (x : TopCat.sphere.{u} n) (r : I) :
    ((sphereULiftHomeomorph (n + 1) (sphereConeCylinderPoint n x r)).1 :
      EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) = 2 * (r : ℝ) - 1 := by
  change sphereConeCylinderVector n x r (Fin.last (n + 1)) = 2 * (r : ℝ) - 1
  rw [sphereConeCylinderVector, sphere_cone_snoc_vector_last]

private theorem sphere_cone_cylinder_point_cast_succ (n : ℕ)
    (x : TopCat.sphere.{u} n) (r : I) (i : Fin (n + 1)) :
    ((sphereULiftHomeomorph (n + 1) (sphereConeCylinderPoint n x r)).1 :
        EuclideanSpace ℝ (Fin (n + 2))) i.castSucc =
      Real.sqrt (1 - (2 * (r : ℝ) - 1) ^ 2) *
        ((sphereULiftHomeomorph n x).1 : EuclideanSpace ℝ (Fin (n + 1))) i := by
  change sphereConeCylinderVector n x r i.castSucc = _
  exact sphere_cone_snoc_vector_cast_succ (n + 1)
    (Real.sqrt (1 - (2 * (r : ℝ) - 1) ^ 2) • (sphereULiftHomeomorph n x).1)
    (2 * (r : ℝ) - 1) i

private theorem sphere_cone_cylinder_point_height_eq (n : ℕ)
    (x y : TopCat.sphere.{u} n) (r s : I)
    (h : sphereConeCylinderPoint n x r = sphereConeCylinderPoint n y s) : r = s := by
  have hz : 2 * (r : ℝ) - 1 = 2 * (s : ℝ) - 1 := by
    simpa only [sphere_cone_cylinder_point_last] using
      congrArg (fun p : TopCat.sphere.{u} (n + 1) =>
        ((sphereULiftHomeomorph (n + 1) p).1 :
          EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1))) h
  exact Subtype.ext (by linarith)

private theorem sphere_cone_cylinder_point_interior_injective (n : ℕ)
    (x y : TopCat.sphere.{u} n) (r : I) (h0 : r ≠ 0) (h1 : r ≠ 1)
    (h : sphereConeCylinderPoint n x r = sphereConeCylinderPoint n y r) : x = y := by
  let a : ℝ := Real.sqrt (1 - (2 * (r : ℝ) - 1) ^ 2)
  have ha : 0 < a := Real.sqrt_pos.2 (sphere_cone_radicand_pos r h0 h1)
  have hraw : (sphereULiftHomeomorph n x).1 = (sphereULiftHomeomorph n y).1 := by
    apply PiLp.ext
    intro i
    have hcoord := congrArg (fun p : TopCat.sphere.{u} (n + 1) =>
      ((sphereULiftHomeomorph (n + 1) p).1 :
        EuclideanSpace ℝ (Fin (n + 2))) i.castSucc) h
    rw [sphere_cone_cylinder_point_cast_succ,
      sphere_cone_cylinder_point_cast_succ] at hcoord
    have hc := congrArg (fun b : ℝ => a⁻¹ * b) hcoord
    change a⁻¹ * (a * ((sphereULiftHomeomorph n x).1 :
        EuclideanSpace ℝ (Fin (n + 1))) i) =
      a⁻¹ * (a * ((sphereULiftHomeomorph n y).1 :
        EuclideanSpace ℝ (Fin (n + 1))) i) at hc
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ha), one_mul] using hc
  exact (sphereULiftHomeomorph n).injective (Subtype.ext hraw)

private theorem sphere_cone_quotient_map_injective (n : ℕ) :
    Function.Injective (sphereConeQuotientMap.{u} n) := by
  intro q q' h
  obtain ⟨x, r, hq⟩ := sphere_cone_quotient_cylinder_representative n q
  obtain ⟨y, s, hq'⟩ := sphere_cone_quotient_cylinder_representative n q'
  have hpoint : sphereConeCylinderPoint n x r = sphereConeCylinderPoint n y s := by
    rw [← hq, ← hq'] at h
    simpa only [sphere_cone_quotient_map_cylinder] using h
  have hrs := sphere_cone_cylinder_point_height_eq n x y r s hpoint
  subst s
  rw [← hq, ← hq']
  by_cases h0 : r = 0
  · subst r
    simp only [cylinder_zero]
  · by_cases h1 : r = 1
    · subst r
      simp only [cylinder_one, id_eq, sphere_cone_quotient_projection_base]
    · rw [sphere_cone_cylinder_point_interior_injective n x y r h0 h1 hpoint]

private theorem sphere_cone_cylinder_point_surjective (n : ℕ) :
    Function.Surjective (fun p : TopCat.sphere.{u} n × I =>
      sphereConeCylinderPoint n p.1 p.2) := by
  intro y
  let v : EuclideanSpace ℝ (Fin (n + 2)) := (sphereULiftHomeomorph (n + 1) y).1
  let z : ℝ := v (Fin.last (n + 1))
  let w : EuclideanSpace ℝ (Fin (n + 1)) :=
    WithLp.toLp 2 (Fin.init (WithLp.ofLp v))
  have hv : sphereConeSnocVector (n + 1) w z = v := by
    change WithLp.toLp 2
      (Fin.snoc (Fin.init (WithLp.ofLp v)) (WithLp.ofLp v (Fin.last (n + 1)))) = v
    rw [Fin.snoc_init_self, WithLp.toLp_ofLp]
  have hnorm : ‖v‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (sphereULiftHomeomorph (n + 1) y).2
  have hsq : ‖w‖ ^ 2 + z ^ 2 = 1 := by
    have h := sphere_cone_snoc_vector_norm_sq (n + 1) w z
    rw [hv, hnorm] at h
    nlinarith
  have hz : |z| ≤ 1 := by
    have h := PiLp.norm_apply_le v (Fin.last (n + 1))
    simpa only [Real.norm_eq_abs, hnorm] using h
  have hz0 : -1 ≤ z := (abs_le.mp hz).1
  have hz1 : z ≤ 1 := (abs_le.mp hz).2
  let r : I := ⟨(z + 1) / 2, by constructor <;> linarith⟩
  have hzr : 2 * (r : ℝ) - 1 = z := by
    dsimp [r]
    ring
  have hsqrt : Real.sqrt (1 - z ^ 2) = ‖w‖ := by
    have hrad : 1 - z ^ 2 = ‖w‖ ^ 2 := by linarith
    rw [hrad, Real.sqrt_sq (norm_nonneg w)]
  by_cases hw : w = 0
  · let x : TopCat.sphere.{u} n := Classical.choice (sphereConeGoodPairData n).nonempty
    have hw0 : Real.sqrt (1 - z ^ 2) = 0 := by
      rw [hsqrt, hw, norm_zero]
    refine ⟨(x, r), ?_⟩
    apply (sphereULiftHomeomorph (n + 1)).injective
    apply Subtype.ext
    change sphereConeCylinderVector n x r = v
    rw [sphereConeCylinderVector, hzr, hw0, zero_smul]
    simpa only [hw] using hv
  · let xRaw : RawSphere n :=
      ⟨‖w‖⁻¹ • w, mem_sphere_zero_iff_norm.2 (by
        rw [norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg w))]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw))⟩
    let x : TopCat.sphere.{u} n := (sphereULiftHomeomorph.{u} n).symm xRaw
    have hx : (sphereULiftHomeomorph.{u} n x).1 = ‖w‖⁻¹ • w :=
      congrArg (fun p : RawSphere n => p.1)
        ((sphereULiftHomeomorph.{u} n).apply_symm_apply xRaw)
    refine ⟨(x, r), ?_⟩
    apply (sphereULiftHomeomorph (n + 1)).injective
    apply Subtype.ext
    change sphereConeCylinderVector n x r = v
    rw [sphereConeCylinderVector, hzr, hx, hsqrt, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw), one_smul]
    exact hv

private theorem sphere_cone_quotient_map_surjective (n : ℕ) :
    Function.Surjective (sphereConeQuotientMap.{u} n) := by
  intro y
  obtain ⟨p, hp⟩ := sphere_cone_cylinder_point_surjective n y
  exact ⟨pointQuotientProjection (sphereConePair.{u} n)
      (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) p.1 p.2),
    (sphere_cone_quotient_map_cylinder n p.1 p.2).trans hp⟩

private theorem sphere_cone_compact_space (n : ℕ) :
    CompactSpace (sphereConePair.{u} n).fst := by
  change CompactSpace (Hatcher.VanKampen.ConeAttachment
    (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n))
  exact (diskHomeomorph.{u} (n + 1)).symm.compactSpace

private theorem sphere_cone_quotient_compact_space (n : ℕ) :
    CompactSpace (pointQuotient (sphereConePair.{u} n)) := by
  let : CompactSpace (sphereConePair.{u} n).fst := sphere_cone_compact_space n
  let : Nonempty (sphereConePair.{u} n).snd := (sphereConeGoodPairData n).nonempty
  exact Function.Surjective.compactSpace
    (pointQuotientProjection (sphereConePair.{u} n)).hom.continuous
    (pointQuotientProjection_surjective (sphereConePair.{u} n))

/-- The fixed cone-base quotient homeomorphism with the prescribed suspension
coordinates, for every `n`, including zero. Retained height one, the collapsed
base, goes to the existing north pole; the explicit apex at height zero goes
to the existing south pole. The retained coordinate agrees with Hatcher's
coordinate by `t = 1 - r`. -/
def sphereConeQuotientHomeomorph (n : ℕ) :
    pointQuotient (sphereConePair.{u} n) ≃ₜ TopCat.sphere.{u} (n + 1) := by
  letI : CompactSpace (pointQuotient (sphereConePair.{u} n)) :=
    sphere_cone_quotient_compact_space n
  letI : T2Space (TopCat.sphere.{u} (n + 1)) := by
    change T2Space (ULift.{u} (RawSphere (n + 1)))
    infer_instance
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (sphereConeQuotientMap n)
      ⟨sphere_cone_quotient_map_injective n, sphere_cone_quotient_map_surjective n⟩)
    (sphereConeQuotientMap n).hom.continuous

/-- The collapsed retained base maps to the existing north pole. -/
@[simp]
theorem sphere_cone_quotient_homeomorph_point (n : ℕ) :
    sphereConeQuotientHomeomorph n
        (pointQuotientPoint (sphereConePair.{u} n)) = northPole.{u} n := by
  change sphereConeQuotientMap n
    (pointQuotientPoint (sphereConePair.{u} n)) = northPole.{u} n
  exact sphere_cone_quotient_map_point n

/-- Every actual retained base point represents the north pole. -/
@[simp]
theorem sphere_cone_quotient_homeomorph_base (n : ℕ)
    (x : TopCat.sphere.{u} n) :
    sphereConeQuotientHomeomorph n
        (pointQuotientProjection (sphereConePair.{u} n)
          (base (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x)) =
      northPole.{u} n := by
  exact (congrArg (sphereConeQuotientHomeomorph n)
    (sphere_cone_quotient_projection_base n x)).trans
    (sphere_cone_quotient_homeomorph_point n)

/-- The actual cone apex maps to the existing south pole. -/
@[simp]
theorem sphere_cone_quotient_homeomorph_apex (n : ℕ) :
    sphereConeQuotientHomeomorph n
        (pointQuotientProjection (sphereConePair.{u} n)
          (apex (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n))) =
      southPole.{u} n := by
  change sphereConeQuotientMap n
    (pointQuotientProjection (sphereConePair.{u} n)
      (apex (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n))) = southPole.{u} n
  exact sphere_cone_quotient_map_apex n

/-- The homeomorphism preserves the prescribed cylinder formula at every
retained height, including both endpoint classes. -/
@[simp]
theorem sphere_cone_quotient_homeomorph_cylinder (n : ℕ)
    (x : TopCat.sphere.{u} n) (r : I) :
    sphereConeQuotientHomeomorph n
        (pointQuotientProjection (sphereConePair.{u} n)
          (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x r)) =
      sphereConeCylinderPoint n x r := by
  change sphereConeQuotientMap n
    (pointQuotientProjection (sphereConePair.{u} n)
      (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x r)) =
    sphereConeCylinderPoint n x r
  exact sphere_cone_quotient_map_cylinder n x r

/-- The complete fixed coordinate formula on an actual cone-base quotient
class: horizontal factor `sqrt (1 - (2*r - 1)^2)`, last coordinate `2*r - 1`. -/
theorem sphere_cone_quotient_homeomorph_coordinates (n : ℕ)
    (x : TopCat.sphere.{u} n) (r : I) :
    ((sphereULiftHomeomorph (n + 1)
      (sphereConeQuotientHomeomorph n
        (pointQuotientProjection (sphereConePair.{u} n)
          (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x r)))).1 :
        EuclideanSpace ℝ (Fin (n + 2))) =
      WithLp.toLp 2
        (Fin.snoc
          (fun i : Fin (n + 1) =>
            Real.sqrt (1 - (2 * (r : ℝ) - 1) ^ 2) *
              ((sphereULiftHomeomorph n x).1 :
                EuclideanSpace ℝ (Fin (n + 1))) i)
          (2 * (r : ℝ) - 1)) := by
  exact (congrArg (fun y : TopCat.sphere.{u} (n + 1) =>
    ((sphereULiftHomeomorph (n + 1) y).1 : EuclideanSpace ℝ (Fin (n + 2))))
      (sphere_cone_quotient_homeomorph_cylinder n x r)).trans
    (sphere_cone_cylinder_point_coordinates n x r)

end Hatcher.Sphere

namespace Hatcher.Sphere

open CategoryTheory
open Hatcher.Relative Hatcher.VanKampen.ConeAttachment

universe u

/-- The actual sphere cone's quotient projection followed by the fixed
homeomorphism to the next standard sphere. -/
def sphereSuspensionProjection (n : ℕ) :
    sphereCone.{u} n ⟶ TopCat.sphere.{u} (n + 1) :=
  TopCat.ofHom
    { toFun := fun c => sphereConeQuotientHomeomorph.{u} n
        (pointQuotientProjection (sphereConePair.{u} n) c)
      continuous_toFun := (sphereConeQuotientHomeomorph.{u} n).continuous.comp
        (pointQuotientProjection (sphereConePair.{u} n)).hom.continuous }

/-- The genuine suspension of a continuous standard sphere map. The actual
map induced by `sphereConePairMap n f` on its point quotient is transported
through the fixed cone-base quotient homeomorphism. This includes `n = 0`
and constant sphere maps. -/
def sphereSuspensionMap (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    TopCat.sphere.{u} (n + 1) ⟶ TopCat.sphere.{u} (n + 1) :=
  TopCat.ofHom
    { toFun := fun y => sphereConeQuotientHomeomorph.{u} n
        (pointQuotientMap (sphereConePairMap n f)
          ((sphereConeQuotientHomeomorph.{u} n).symm y))
      continuous_toFun := (sphereConeQuotientHomeomorph.{u} n).continuous.comp
        ((pointQuotientMap (sphereConePairMap n f)).hom.continuous.comp
          (sphereConeQuotientHomeomorph.{u} n).symm.continuous) }

/-- The fixed homeomorphism intertwines the actual induced quotient map
with the suspension map. -/
@[simp]
theorem sphere_suspension_map_quotient (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n)
    (z : pointQuotient (sphereConePair.{u} n)) :
    sphereSuspensionMap n f (sphereConeQuotientHomeomorph n z) =
      sphereConeQuotientHomeomorph n
        (pointQuotientMap (sphereConePairMap n f) z) := by
  change sphereConeQuotientHomeomorph.{u} n
      (pointQuotientMap (sphereConePairMap n f)
        ((sphereConeQuotientHomeomorph.{u} n).symm
          (sphereConeQuotientHomeomorph.{u} n z))) =
    sphereConeQuotientHomeomorph.{u} n
      (pointQuotientMap (sphereConePairMap n f) z)
  rw [Homeomorph.symm_apply_apply]

/-- On the actual ambient cone, `Sf ∘ q = q ∘ Cf`. -/
theorem sphere_suspension_map_ambient_naturality (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    sphereSuspensionProjection n ≫ sphereSuspensionMap n f =
      sphereConeMap n f ≫ sphereSuspensionProjection n := by
  ext c
  change sphereSuspensionMap n f
      (sphereConeQuotientHomeomorph.{u} n
        (pointQuotientProjection (sphereConePair.{u} n) c)) =
    sphereConeQuotientHomeomorph.{u} n
      (pointQuotientProjection (sphereConePair.{u} n) (sphereConeMap n f c))
  have hq := ConcreteCategory.congr_hom
    (pointQuotientProjection_naturality (sphereConePairMap n f)) c
  change pointQuotientMap (sphereConePairMap n f)
      (pointQuotientProjection (sphereConePair.{u} n) c) =
    pointQuotientProjection (sphereConePair.{u} n) (sphereConeMap n f c) at hq
  exact (sphere_suspension_map_quotient n f
    (pointQuotientProjection (sphereConePair.{u} n) c)).trans
      (congrArg (sphereConeQuotientHomeomorph.{u} n) hq)

/-- A suspension cylinder class retains its height and applies the original
sphere map to its sphere coordinate, including both endpoint classes. -/
@[simp]
theorem sphere_suspension_map_cylinder (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n)
    (x : TopCat.sphere.{u} n) (r : I) :
    sphereSuspensionMap n f
        (sphereConeQuotientHomeomorph n
          (pointQuotientProjection (sphereConePair.{u} n)
            (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x r))) =
      sphereConeQuotientHomeomorph n
        (pointQuotientProjection (sphereConePair.{u} n)
          (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) (f x) r)) := by
  change sphereSuspensionMap n f
      (sphereSuspensionProjection n
        (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x r)) =
    sphereSuspensionProjection n
      (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) (f x) r)
  have h := ConcreteCategory.congr_hom
    (sphere_suspension_map_ambient_naturality n f)
    (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x r)
  change sphereSuspensionMap n f
      (sphereSuspensionProjection n
        (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x r)) =
    sphereSuspensionProjection n
      (sphereConeMap n f
        (cylinder (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n) x r)) at h
  rw [sphere_cone_map_cylinder] at h
  exact h

/-- Every suspension fixes the existing north pole, the image of the actual
collapsed retained base. -/
@[simp]
theorem sphere_suspension_map_north_pole (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    sphereSuspensionMap n f (northPole.{u} n) = northPole.{u} n := by
  let z : pointQuotient (sphereConePair.{u} n) :=
    pointQuotientPoint (sphereConePair.{u} n)
  have hz : pointQuotientMap (sphereConePairMap n f) z = z :=
    ConcreteCategory.congr_hom
      (pointQuotientPointInclusion_naturality (sphereConePairMap n f)) PUnit.unit
  have he : sphereConeQuotientHomeomorph.{u} n z = northPole.{u} n :=
    sphere_cone_quotient_homeomorph_point n
  calc
    sphereSuspensionMap n f (northPole.{u} n) =
        sphereSuspensionMap n f (sphereConeQuotientHomeomorph n z) :=
      congrArg (sphereSuspensionMap n f) he.symm
    _ = sphereConeQuotientHomeomorph n
        (pointQuotientMap (sphereConePairMap n f) z) :=
      sphere_suspension_map_quotient n f z
    _ = sphereConeQuotientHomeomorph n z :=
      congrArg (sphereConeQuotientHomeomorph.{u} n) hz
    _ = northPole.{u} n := he

/-- Every suspension fixes the existing south pole, the image of the actual
explicit cone apex. -/
@[simp]
theorem sphere_suspension_map_south_pole (n : ℕ)
    (f : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    sphereSuspensionMap n f (southPole.{u} n) = southPole.{u} n := by
  let a : sphereCone.{u} n :=
    apex (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n)
  have ha : sphereSuspensionProjection n a = southPole.{u} n := by
    change sphereConeQuotientHomeomorph.{u} n
      (pointQuotientProjection (sphereConePair.{u} n)
        (apex (id : TopCat.sphere.{u} n → TopCat.sphere.{u} n))) = southPole.{u} n
    exact sphere_cone_quotient_homeomorph_apex n
  have hfix : sphereConeMap n f a = a := sphere_cone_map_apex n f
  have hnat : sphereSuspensionMap n f (sphereSuspensionProjection n a) =
      sphereSuspensionProjection n (sphereConeMap n f a) :=
    ConcreteCategory.congr_hom (sphere_suspension_map_ambient_naturality n f) a
  calc
    sphereSuspensionMap n f (southPole.{u} n) =
        sphereSuspensionMap n f (sphereSuspensionProjection n a) :=
      congrArg (sphereSuspensionMap n f) ha.symm
    _ = sphereSuspensionProjection n (sphereConeMap n f a) := hnat
    _ = sphereSuspensionProjection n a := congrArg (sphereSuspensionProjection n) hfix
    _ = southPole.{u} n := ha

/-- The identity sphere map suspends to the identity of the next sphere. -/
@[simp]
theorem sphere_suspension_map_id (n : ℕ) :
    sphereSuspensionMap n (𝟙 (TopCat.sphere.{u} n)) =
      𝟙 (TopCat.sphere.{u} (n + 1)) := by
  ext y
  change sphereConeQuotientHomeomorph.{u} n
    (pointQuotientMap (sphereConePairMap n (𝟙 (TopCat.sphere.{u} n)))
      ((sphereConeQuotientHomeomorph.{u} n).symm y)) = y
  rw [sphere_cone_pair_map_id, pointQuotientMap_id]
  exact (sphereConeQuotientHomeomorph.{u} n).apply_symm_apply y

/-- Suspension preserves the actual composition of continuous sphere maps. -/
@[simp]
theorem sphere_suspension_map_comp (n : ℕ)
    (f g : TopCat.sphere.{u} n ⟶ TopCat.sphere.{u} n) :
    sphereSuspensionMap n (f ≫ g) =
      sphereSuspensionMap n f ≫ sphereSuspensionMap n g := by
  ext y
  change sphereConeQuotientHomeomorph.{u} n
      (pointQuotientMap (sphereConePairMap n (f ≫ g))
        ((sphereConeQuotientHomeomorph.{u} n).symm y)) =
    sphereConeQuotientHomeomorph.{u} n
      (pointQuotientMap (sphereConePairMap n g)
        ((sphereConeQuotientHomeomorph.{u} n).symm
          (sphereConeQuotientHomeomorph.{u} n
            (pointQuotientMap (sphereConePairMap n f)
              ((sphereConeQuotientHomeomorph.{u} n).symm y)))))
  rw [sphere_cone_pair_map_comp, pointQuotientMap_comp]
  change sphereConeQuotientHomeomorph.{u} n
      (pointQuotientMap (sphereConePairMap n g)
        (pointQuotientMap (sphereConePairMap n f)
          ((sphereConeQuotientHomeomorph.{u} n).symm y))) =
    sphereConeQuotientHomeomorph.{u} n
      (pointQuotientMap (sphereConePairMap n g)
        ((sphereConeQuotientHomeomorph.{u} n).symm
          (sphereConeQuotientHomeomorph.{u} n
            (pointQuotientMap (sphereConePairMap n f)
              ((sphereConeQuotientHomeomorph.{u} n).symm y)))))
  rw [Homeomorph.symm_apply_apply]

end Hatcher.Sphere
