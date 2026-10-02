/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Disc.BrouwerGeneral
import Hatcher.Disc.NoRetractionHomology

/-!
# Brouwer's fixed-point theorem for disks

The boundary-ray construction and the homological no-retraction theorem imply
the positive-dimensional Brouwer fixed-point theorem.
-/

namespace Hatcher.Disc

/-- **Hatcher, Corollary 2.15 (pages 114–115).** Every continuous self-map of
a positive-dimensional disk has a fixed point. -/
theorem exists_fixed_point_disk (n : ℕ)
    (f : TopCat.disk.{0} (n + 1) ⟶ TopCat.disk.{0} (n + 1)) :
    ∃ x, f x = x := by
  by_contra hfixed
  push Not at hfixed
  exact not_exists_diskBoundary_retraction n
    (exists_diskBoundary_retraction_of_fixedPointFree n f hfixed)

end Hatcher.Disc
