/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.ReflectionDegree
import Mathlib.Data.List.FinRange

/-!
# Degree of the antipodal map

The antipodal homeomorphism is the ordered composite of the `n+1` exact
coordinate reflections.  Multiplicativity of degree and the reflection
calculation therefore give degree `(-1)^(n+1)` without replacing the explicit
map by a merely homotopic one.
-/

noncomputable section

open CategoryTheory

namespace Hatcher.Sphere

/-- The ordered categorical composite of the coordinate reflections listed
in `l`. The head reflection is applied first. -/
noncomputable def coordinateReflectionComposite (n : ℕ) :
    List (Fin (n + 1)) →
      (TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
  | [] => 𝟙 _
  | i :: l =>
      (coordinateReflectionIso n i).hom ≫
        coordinateReflectionComposite n l

private theorem coordinateSignChangeIso_empty (n : ℕ) :
    (coordinateSignChangeIso n ∅).hom = 𝟙 _ := by
  ext x
  apply (sphereULiftHomeomorph n).injective
  apply Subtype.ext
  apply PiLp.ext
  intro i
  rw [sphereULiftHomeomorph_coordinateSignChangeIso_apply]
  simp

/-- A duplicate-free ordered composite of coordinate reflections changes the
signs of exactly the coordinates occurring in the list. -/
theorem coordinateReflectionComposite_eq_signChange
    (n : ℕ) (l : List (Fin (n + 1))) (hl : l.Nodup) :
    coordinateReflectionComposite n l =
      (coordinateSignChangeIso n l.toFinset).hom := by
  induction l with
  | nil =>
      simpa [coordinateReflectionComposite] using
        (coordinateSignChangeIso_empty n).symm
  | cons i l ih =>
      have hil : i ∉ l.toFinset := by
        simpa using (List.nodup_cons.mp hl).1
      have hdisjoint : Disjoint ({i} : Finset (Fin (n + 1))) l.toFinset := by
        simp [hil]
      rw [coordinateReflectionComposite, ih (List.nodup_cons.mp hl).2]
      change (coordinateSignChangeIso n {i}).hom ≫
          (coordinateSignChangeIso n l.toFinset).hom = _
      rw [coordinateSignChangeIso_hom_comp_of_disjoint n hdisjoint]
      rw [show ({i} : Finset (Fin (n + 1))) ∪ l.toFinset =
          (i :: l).toFinset by
        ext j
        simp]

/-- The ordered list of all coordinate reflections is exactly the explicit
antipodal homeomorphism. -/
theorem coordinateReflectionComposite_finRange (n : ℕ) :
    coordinateReflectionComposite n (List.finRange (n + 1)) =
      (antipodalIso n).hom := by
  rw [coordinateReflectionComposite_eq_signChange n _
    (List.nodup_finRange (n + 1))]
  change (coordinateSignChangeIso n (List.finRange (n + 1)).toFinset).hom =
    (coordinateSignChangeIso n Finset.univ).hom
  rw [show (List.finRange (n + 1)).toFinset = Finset.univ by
    ext i
    simp]

/-- The degree of an ordered composite of `k` coordinate reflections is
`(-1)^k`. Repetitions are allowed in this algebraic statement. -/
theorem degree_coordinateReflectionComposite
    (n : ℕ) (hn : 0 < n) (l : List (Fin (n + 1))) :
    degree n hn (coordinateReflectionComposite n l) =
      (-1 : ℤ) ^ l.length := by
  induction l with
  | nil =>
      simp [coordinateReflectionComposite, degree_id]
  | cons i l ih =>
      rw [coordinateReflectionComposite, degree_comp,
        degree_coordinateReflection, ih, List.length_cons, pow_succ']

/-- **Hatcher, degree property (f), printed page 134.** The antipodal map on
`Sⁿ` has degree `(-1)^(n+1)`. -/
theorem degree_antipodal (n : ℕ) (hn : 0 < n) :
    degree n hn (antipodalIso n).hom = (-1 : ℤ) ^ (n + 1) := by
  rw [← coordinateReflectionComposite_finRange]
  simpa using degree_coordinateReflectionComposite n hn
    (List.finRange (n + 1))

end Hatcher.Sphere
