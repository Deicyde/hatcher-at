import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section

namespace Hatcher

universe u

/-- Every group is isomorphic to a presented group whose generators are the
elements of the group itself. This is the algebraic construction used in
Hatcher's proof of Corollary 1.28. -/
theorem exists_presentedGroup_equiv (G : Type u) [Group G] :
    ∃ rels : Set (FreeGroup G), Nonempty (PresentedGroup rels ≃* G) := by
  let φ : FreeGroup G →* G := FreeGroup.lift id
  have hφ : Function.Surjective φ := by
    intro g
    exact ⟨FreeGroup.of g, FreeGroup.lift_apply_of⟩
  have hclosure : Subgroup.normalClosure (φ.ker : Set (FreeGroup G)) = φ.ker := by
    apply le_antisymm
    · exact Subgroup.normalClosure_le_normal fun _ h ↦ h
    · exact Subgroup.subset_normalClosure
  refine ⟨(φ.ker : Set (FreeGroup G)), ⟨?_⟩⟩
  unfold PresentedGroup
  exact (QuotientGroup.quotientMulEquivOfEq hclosure).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

end Hatcher
