/-
Hatcher, *Algebraic Topology*, Proposition 1.30 (page 60).
-/
import Mathlib.Topology.Homotopy.Lifting

open unitInterval

namespace Hatcher.Covering

variable {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace A] {p : E → X}

/-- **Hatcher, Proposition 1.30 (page 60).** A homotopy and a lift of its
time-zero map lift uniquely through a covering map. -/
theorem existsUnique_liftHomotopy (cov : IsCoveringMap p) (H : C(I × A, X))
    (f₀ : C(A, E)) (H₀ : ∀ a, H (0, a) = p (f₀ a)) :
    ∃! H' : C(I × A, E), p ∘ H' = H ∧ ∀ a, H' (0, a) = f₀ a := by
  refine ⟨cov.liftHomotopy H f₀ H₀,
    ⟨cov.liftHomotopy_lifts H f₀ H₀, cov.liftHomotopy_zero H f₀ H₀⟩, ?_⟩
  intro H' hH'
  exact (cov.eq_liftHomotopy_iff' H₀ H').mpr hH'

end Hatcher.Covering
