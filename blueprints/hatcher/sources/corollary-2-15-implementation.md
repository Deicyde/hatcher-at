# Corollary 2.15 implementation specification

This is a project-authored implementation specification for Hatcher §2.1,
Corollary 2.15. It is not an independent mathematical source. The cited
statement and proof are in the official Hatcher PDF at the locations recorded
in the [§2.1 source note](hatcher-2-1.md); the fixed-point construction is the
ray argument from [Theorem 1.9](hatcher-1-1.md).

## Mathematical scope

For every `n : ℕ`, formalize the two conclusions

- the boundary `∂D^(n+1) = S^n` is not a retract of `D^(n+1)`; and
- every continuous self-map of `D^(n+1)` has a fixed point.

The successor indexing states exactly the positive-dimensional case used by
Hatcher's reduced-homology proof. The degenerate `D⁰` case is outside the main
contract and may be added later as a trivial corollary.

## Topological model

Use Mathlib's exact universe-zero public objects `TopCat.disk.{0} (n + 1)` and
`TopCat.diskBoundary.{0} (n + 1)`, together with
`TopCat.diskBoundaryInclusion.{0} (n + 1)`. Mathlib defines
`TopCat.sphere.{0} n` to be `TopCat.diskBoundary.{0} (n + 1)`, so the completed
integral sphere calculation applies without a competing sphere model. Keeping
the public declarations at universe zero makes
`Hatcher.Sphere.reducedHomology_sphere_int` apply directly.

Point-set calculations for Brouwer may cross `ULift` and work on
`Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1`. The public theorem
must return to the `TopCat.disk.{0}` model. Supporting formulas may use real
inner products, but they do not constitute a second public disk API.

## Homological no-retraction argument

A putative retraction `r` satisfies

`TopCat.diskBoundaryInclusion.{0} (n + 1) ≫ r = 𝟙 _`.

Apply reduced integral homology in degree `n`. The boundary object is
`TopCat.sphere.{0} n`, whose reduced homology is isomorphic to `ℤ` by the completed
Corollary 2.14 theorem. The disk is contractible, so its reduced homology is a
zero object. Functoriality would therefore make the identity of a nonzero
object factor through a zero object, a contradiction.

Use `Hatcher.Sphere.reducedHomology_sphere_int` and
`Hatcher.Reduced.isZero_homology_of_contractible`. The contractible-space
instance for the raw disk comes from `Metric.contractibleSpace_closedBall` and
is transported through the lift. No good-pair quotient sequence, degree, or
orientation theory is needed.

## Fixed-point-free maps and the boundary ray

For a fixed-point-free continuous self-map `f` of the disk, send `x` to the
point where the ray beginning at `f(x)` and passing through `x` exits the unit
ball. Prove the exit point is defined continuously and that it equals `x` when
`x` lies on the boundary. This yields a map from the disk to its boundary whose
restriction to the boundary is the identity: `r ∘ i = id_{∂D}`, or in Lean's
categorical order, `TopCat.diskBoundaryInclusion.{0} (n + 1) ≫ r = 𝟙 _`.

Keep the exit-time formula, its norm calculation, continuity, and boundary
restriction in the fixed-point-free-retraction review unit. The source-facing
Brouwer theorem should then be the short contradiction between this retraction
and the independent homological obstruction.

## Intended public contract

The fine roadmap has three main results:

1. `Hatcher.Disc.not_exists_diskBoundary_retraction`;
2. `Hatcher.Disc.exists_diskBoundary_retraction_of_fixedPointFree`; and
3. `Hatcher.Disc.exists_fixed_point_disk`.

Exact helper names may follow surrounding conventions, but these three
semantic completion targets and their dependency order are fixed.

## Pinned API and prior art

The repository pins Mathlib `v4.34.1` at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. It contains the disk, boundary,
and inclusion objects, closed-ball contractibility, categorical split-mono and
zero-object tools, and the Euclidean inner-product continuity lemmas needed by
the ray calculation. It does not contain Brouwer's theorem or the disk-boundary
no-retraction theorem.

The completed local two-dimensional results
`Hatcher.Disc.not_exists_retraction` and `Hatcher.Disc.exists_fixed_point` are
implementation prior art, not mathematical prerequisites. The Lean 3 project
[Shamrock-Frost/BrouwerFixedPoint](https://github.com/Shamrock-Frost/BrouwerFixedPoint)
contains an older homological and boundary-ray implementation. The current
[Econlib Brouwer development](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Math/Topology/Brouwer.lean)
proves a stronger compact-convex theorem through Sperner's lemma; it is an
alternative route rather than a dependency. Mathlib issue
[#25231](https://github.com/leanprover-community/mathlib4/issues/25231) tracks
active Sperner work, while PR
[#36770](https://github.com/leanprover-community/mathlib4/pull/36770) develops
invariance of domain assuming Brouwer. None is exact merged coverage at this
project's pin, so no new node is marked `mathlib: true`.

## Explicit exclusions

This milestone does not include degree or orientation theory, invariance of
dimension, invariance of domain, higher Borsuk–Ulam, Theorem 2.13,
Proposition 2.22, or the remaining Δ-complex comparison results. Those require
separate source decisions and roadmap milestones.
