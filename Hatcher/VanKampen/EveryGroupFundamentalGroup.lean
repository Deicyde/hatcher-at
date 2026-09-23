import Hatcher.VanKampen.PresentedGroup
import Hatcher.VanKampen.PresentationComplexRealization

/-!
# Every group is a fundamental group

Hatcher's Corollary 1.28 follows by realizing a presentation of an arbitrary
group as a two-dimensional presentation complex.
-/

noncomputable section

namespace Hatcher

universe u

/-- **Hatcher, Corollary 1.28 (page 52).** Every group is the fundamental
group of a two-dimensional cell complex. -/
theorem exists_twoDimensionalCWComplex_fundamentalGroupEquiv
    (G : Type u) [Group G] :
    ∃ (X : TopCat.{u}) (x₀ : X) (c : TopCat.CWComplex X),
      (∀ γ : HomotopicalAlgebra.RelativeCellComplex.Cells c, γ.j ≤ 2) ∧
        Nonempty (FundamentalGroup X x₀ ≃* G) := by
  obtain ⟨rels, ⟨eG⟩⟩ := exists_presentedGroup_equiv G
  obtain ⟨X, x₀, c, hdim, ⟨eX⟩⟩ :=
    exists_presentationComplex_fundamentalGroupEquiv G rels
  exact ⟨X, x₀, c, hdim, ⟨eX.symm.trans eG⟩⟩

end Hatcher
