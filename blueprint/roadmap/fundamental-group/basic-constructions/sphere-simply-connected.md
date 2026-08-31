---
declaration: theorem
origin: cited
---

# Higher spheres are simply connected

**Hatcher, Proposition 1.14 (page 35).** `π₁(Sⁿ) = 0` for `n ≥ 2`.

Cover `Sⁿ` by two open sets `A₁` and `A₂`, each the complement of a point and
so homeomorphic to `ℝⁿ`. Their intersection is homotopy equivalent to
`Sⁿ⁻¹`, which is path-connected precisely when `n ≥ 2`. By the
[open cover lemma](loop-in-open-cover.md), every loop is homotopic to a product
of loops each lying in `A₁` or in `A₂`; each of those is nullhomotopic because
`ℝⁿ` is simply connected. Hence every loop in `Sⁿ` is nullhomotopic.

The hypothesis `n ≥ 2` enters exactly once, at path-connectedness of
`A₁ ∩ A₂`, and it is sharp: `π₁(S¹) ≅ ℤ`.

Mathlib has `SimplyConnectedSpace` and the contractibility of `ℝⁿ` but no
instance for spheres; the only `SimplyConnectedSpace` mentions near spheres are
the `proof_wanted` statements of the Poincaré conjecture in
`Geometry/Manifold/PoincareConjecture.lean`, which are unrelated.

[Mathlib PR #28246](https://github.com/leanprover-community/mathlib4/pull/28246)
now supplies `EuclideanSphere.simplyConnectedSpace` and a corresponding
instance, using the same open-cover route. The PR is open and not part of the
pinned Mathlib, so this node is not marked formalized; it should be reviewed
for reuse before a project-local implementation is started.

Intended artifact: `Hatcher.Sphere.simplyConnectedSpace` in
`Hatcher/Sphere/SimplyConnected.lean`, ideally as an instance.

## Proof depends on

- [A loop splits across an open cover](loop-in-open-cover.md)

## Sources

- [Hatcher §1.1, Proposition 1.14, page 35](../../../sources/hatcher-1-1.md)
