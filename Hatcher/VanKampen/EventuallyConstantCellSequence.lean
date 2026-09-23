import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.Topology.CWComplex.Abstract.Basic

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat

namespace Hatcher.VanKampen.CellAttachment

universe u

variable {X : ℕ → TopCat.{u}}

/-- A sequence is eventually constant once all of its structure maps from a
given stage onward are isomorphisms. -/
theorem ofSequence_isEventuallyConstantFrom
    (step : ∀ n, X n ⟶ X (n + 1)) (N : ℕ)
    (hstep : ∀ n, N ≤ n → IsIso (step n)) :
    (Functor.ofSequence step).IsEventuallyConstantFrom N := by
  intro j f
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom f)
  induction k with
  | zero =>
      have hf : f = 𝟙 N := Subsingleton.elim _ _
      rw [hf]
      change IsIso (Functor.OfSequence.map step N N _)
      rw [Functor.OfSequence.map_id]
      infer_instance
  | succ k ih =>
      let g : N ⟶ N + k := homOfLE (Nat.le_add_right N k)
      let s : N + k ⟶ N + k + 1 := homOfLE (Nat.le_add_right (N + k) 1)
      have hf : f = g ≫ s := Subsingleton.elim _ _
      rw [hf, Functor.map_comp]
      rw [Functor.ofSequence_map_homOfLE_succ]
      exact IsIso.comp_isIso' (ih g)
        (hstep (N + k) (Nat.le_add_right N k))

/-- Build an abstract CW complex from an eventually constant sequence of
standard cell attachments. -/
noncomputable def cwComplexOfEventuallyConstantSequence
    (X : ℕ → TopCat.{u}) (step : ∀ n, X n ⟶ X (n + 1))
    (hX₀ : IsInitial (X 0)) (N : ℕ)
    (hconst : (Functor.ofSequence step).IsEventuallyConstantFrom N)
    (cells : ∀ n, AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} n) (step n)) :
    TopCat.CWComplex (X N) where
  F := Functor.ofSequence step
  isoBot := hX₀.uniqueUpToIso initialIsInitial
  incl := hconst.cocone.ι
  isColimit := hconst.isColimitCocone
  fac := Subsingleton.elim _ _
  attachCells n _ :=
    (cells n).ofArrowIso
      (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
        exact Functor.ofSequence_map_homOfLE_succ step n))

/-- If no cells occur from stage `N` onward, every cell of the resulting CW
complex has dimension strictly less than `N`. -/
theorem cwComplexOfEventuallyConstantSequence_cell_dim_lt
    (X : ℕ → TopCat.{u}) (step : ∀ n, X n ⟶ X (n + 1))
    (hX₀ : IsInitial (X 0)) (N : ℕ)
    (hconst : (Functor.ofSequence step).IsEventuallyConstantFrom N)
    (cells : ∀ n, AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} n) (step n))
    (hempty : ∀ n, N ≤ n → IsEmpty (cells n).ι)
    (c : (cwComplexOfEventuallyConstantSequence X step hX₀ N hconst cells).Cells) :
    c.j < N := by
  by_contra h
  apply (hempty c.j (Nat.le_of_not_gt h)).false
  exact c.k

end Hatcher.VanKampen.CellAttachment
