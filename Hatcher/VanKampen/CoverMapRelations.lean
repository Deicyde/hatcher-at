import Hatcher.VanKampen.CoverGroupPresentation
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section

namespace Hatcher.VanKampen

universe u v

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

private theorem coverMap_overlap_images_eq
    (U : ι → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i)
    (i j : ι) (ω : OverlapGroup U x₀ hx₀ i j) :
    coverMap U x₀ hx₀
        (Monoid.CoprodI.of (overlapToLeft U x₀ hx₀ i j ω)) =
      coverMap U x₀ hx₀
        (Monoid.CoprodI.of (overlapToRight U x₀ hx₀ i j ω)) := by
  simp only [coverMap, Monoid.CoprodI.lift_of, overlapToLeft,
    overlapToRight]
  induction ω using Path.Homotopic.Quotient.ind with
  | mk γ => rfl

/-- Every pairwise-overlap relator maps to the identity under the cover map. -/
theorem coverMap_overlapRelation
    (U : ι → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i)
    (i j : ι) (ω : OverlapGroup U x₀ hx₀ i j) :
    coverMap U x₀ hx₀ (overlapRelation U x₀ hx₀ i j ω) = 1 := by
  simp only [overlapRelation, map_mul, map_inv]
  rw [coverMap_overlap_images_eq, mul_inv_cancel]

/-- The normal closure of the overlap relators lies in the kernel of the
canonical cover map. -/
theorem relationSubgroup_le_ker
    (U : ι → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i) :
    relationSubgroup U x₀ hx₀ ≤ MonoidHom.ker (coverMap U x₀ hx₀) := by
  apply Subgroup.normalClosure_le_normal
  rintro r ⟨i, j, ω, rfl⟩
  exact MonoidHom.mem_ker.mpr (coverMap_overlapRelation U x₀ hx₀ i j ω)

instance relationSubgroup_normal
    (U : ι → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i) :
    (relationSubgroup U x₀ hx₀).Normal := by
  unfold relationSubgroup
  infer_instance

/-- The cover map descended to the quotient by the overlap relations. -/
def quotientCoverMap
    (U : ι → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i) :
    CoverFreeProduct U x₀ hx₀ ⧸ relationSubgroup U x₀ hx₀ →*
      FundamentalGroup X x₀ :=
  QuotientGroup.lift (relationSubgroup U x₀ hx₀) (coverMap U x₀ hx₀)
    (relationSubgroup_le_ker U x₀ hx₀)

end Hatcher.VanKampen
