import Hatcher.Sphere.HemisphereCharts
import Mathlib.Analysis.Convex.Contractible

/-!
# Stereographic projection from a punctured sphere

This file exposes the full opposite-point chart used implicitly in the sphere
calculations.  The public source remains `TopCat.sphere`; the only passage to
Mathlib's metric-sphere model is the existing `sphereULiftHomeomorph`.
-/

open Metric Set
open scoped EuclideanSpace

namespace Hatcher.Sphere

private noncomputable def rawPuncturedSphereHomeomorphEuclidean
    (n : ℕ) (p : RawSphere n) :
    ({p}ᶜ : Set (RawSphere n)) ≃ₜ EuclideanSpace ℝ (Fin n) := by
  let e := stereographic' n p
  exact
    (Homeomorph.setCongr (stereographic'_source p).symm).trans
      (e.toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr (stereographic'_target p)).trans
          (Homeomorph.Set.univ _)))

private noncomputable def puncturedSphereRawHomeomorph
    (n : ℕ) (p : TopCat.sphere.{0} n) :
    ({p}ᶜ : Set (TopCat.sphere.{0} n)) ≃ₜ
      ({sphereULiftHomeomorph n p}ᶜ : Set (RawSphere n)) :=
  (sphereULiftHomeomorph n).subtype fun x => by simp

/-- Stereographic projection from `p` identifies the complement of `p` in the
standard `n`-sphere with Euclidean `n`-space. -/
noncomputable def puncturedSphereHomeomorphEuclidean
    (n : ℕ) (p : TopCat.sphere.{0} n) :
    ({p}ᶜ : Set (TopCat.sphere.{0} n)) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (puncturedSphereRawHomeomorph n p).trans
    (rawPuncturedSphereHomeomorphEuclidean n (sphereULiftHomeomorph n p))

/-- The complement of a point in the standard sphere is contractible. -/
noncomputable instance puncturedSphereContractibleSpace
    (n : ℕ) (p : TopCat.sphere.{0} n) :
    ContractibleSpace ({p}ᶜ : Set (TopCat.sphere.{0} n)) :=
  Homeomorph.contractibleSpace (puncturedSphereHomeomorphEuclidean n p)

end Hatcher.Sphere
