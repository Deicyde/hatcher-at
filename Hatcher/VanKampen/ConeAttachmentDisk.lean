import Hatcher.VanKampen.ConeAttachment
import Mathlib.Topology.Category.TopCat.Sphere

/-!
# A cone on the disk boundary is a disk

This module identifies the cone attachment of the identity map on the
boundary of the standard `n`-disk with the standard `n`-disk itself.
-/

noncomputable section

open Metric Set
open scoped unitInterval

namespace Hatcher.VanKampen.ConeAttachment

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private abbrev Boundary (n : ℕ) := (TopCat.diskBoundary n : Type)

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
        (id : ((TopCat.diskBoundary n : TopCat) : Type) →
          ((TopCat.diskBoundary n : TopCat) : Type)) ≃ₜ
      ((TopCat.disk n : TopCat) : Type) :=
  (rawDiskHomeomorph n).trans Homeomorph.ulift.symm

/-- On the retained boundary, `diskHomeomorph` is the standard boundary
inclusion into the disk. -/
@[simp]
theorem diskHomeomorph_base_eq_diskBoundaryInclusion (n : ℕ)
    (x : ((TopCat.diskBoundary n : TopCat) : Type)) :
    diskHomeomorph n
        (base
          (id : ((TopCat.diskBoundary n : TopCat) : Type) →
            ((TopCat.diskBoundary n : TopCat) : Type)) x) =
      TopCat.diskBoundaryInclusion n x :=
  rfl

/-- The cone apex corresponds to the center of the disk. -/
@[simp]
theorem diskHomeomorph_apex (n : ℕ) :
    diskHomeomorph n
        (apex
          (id : ((TopCat.diskBoundary n : TopCat) : Type) →
            ((TopCat.diskBoundary n : TopCat) : Type))) =
      ULift.up
        (⟨0, by simp⟩ :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  rfl

/-- A cone cylinder point maps to its radial point in the disk. -/
@[simp]
theorem diskHomeomorph_cylinder (n : ℕ)
    (x : ((TopCat.diskBoundary n : TopCat) : Type)) (t : I) :
    diskHomeomorph n
        (cylinder
          (id : ((TopCat.diskBoundary n : TopCat) : Type) →
            ((TopCat.diskBoundary n : TopCat) : Type)) x t) =
      ULift.up
        (⟨(t : ℝ) • (x.down : EuclideanSpace ℝ (Fin n)), by
          rw [mem_closedBall_zero_iff, norm_smul_of_nonneg t.2.1,
            mem_sphere_zero_iff_norm.mp x.down.2, mul_one]
          exact t.2.2⟩ :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  rfl

end Hatcher.VanKampen.ConeAttachment
