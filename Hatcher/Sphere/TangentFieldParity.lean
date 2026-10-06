/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.OddTangentField
import Hatcher.Sphere.TangentFieldObstruction

/-!
# Nonvanishing tangent fields on spheres

The degree obstruction and Hatcher's explicit paired-coordinate construction
combine to characterize exactly which positive-dimensional spheres possess a
continuous nonvanishing tangent vector field.
-/

noncomputable section

namespace Hatcher.Sphere

/-- **Hatcher, Theorem 2.28 (printed page 135).** A positive-dimensional
sphere admits a continuous nonvanishing tangent vector field if and only if
its dimension is odd. The reverse implication returns Hatcher's explicit
paired-coordinate quarter-turn field. -/
theorem exists_nonvanishingTangentVectorField_iff_odd
    (n : ℕ) (hn : 0 < n) :
    (∃ v : TangentVectorField n, v.Nonvanishing) ↔ Odd n := by
  constructor
  · rintro ⟨v, hv⟩
    exact odd_of_nonvanishingTangentVectorField n hn v hv
  · intro hnodd
    exact ⟨nonvanishingTangentVectorFieldOfOdd n hnodd,
      nonvanishingTangentVectorFieldOfOdd_nonvanishing n hnodd⟩

end Hatcher.Sphere
