import Hatcher.VanKampen.PresentationComplexCW
import Hatcher.VanKampen.PresentationComplexFundamentalGroup

/-!
# Two-dimensional presentation complexes

This file combines the CW structure and fundamental-group calculation for a
presentation complex.
-/

noncomputable section

namespace Hatcher

universe u

/-- A group presentation is realized by a two-dimensional CW complex whose
fundamental group is the corresponding presented group. -/
theorem exists_presentationComplex_fundamentalGroupEquiv
    (S : Type u) (rels : Set (FreeGroup S)) :
    ∃ (X : TopCat.{u}) (x₀ : X) (c : TopCat.CWComplex X),
      (∀ γ : HomotopicalAlgebra.RelativeCellComplex.Cells c, γ.j ≤ 2) ∧
        Nonempty (PresentedGroup rels ≃* FundamentalGroup X x₀) := by
  refine ⟨TopCat.of (presentationComplex rels),
    presentationComplexBasepoint rels,
    presentationComplexCWComplex rels,
    presentationComplexCWComplex_cells_dim_le_two rels, ?_⟩
  exact ⟨presentationComplexFundamentalGroupEquiv rels⟩

end Hatcher
