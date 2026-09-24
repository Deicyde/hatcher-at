---
article_id: af_c84b824b4ed5b5be3e947b7b
source_units: [hatcher-1-1-basic-constructions]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Sphere.exists_eq_neg
---

# Borsuk–Ulam for the two-sphere

**Hatcher, Theorem 1.10 (pages 32–33).** For every continuous `f : S² → ℝ²`
there is a point `x ∈ S²` with `f(x) = f(−x)`.

Suppose not, and set `g(x) = (f(x) − f(−x)) / |f(x) − f(−x)|`, a map
`S² → S¹` with `g(−x) = −g(x)`. Restrict `g` to the equator `S¹ ⊆ S²` and call
the resulting loop `η`. Because `η` is odd, its winding number is odd, in
particular nonzero, so `η` is not nullhomotopic. But the equator bounds a disc
in `S²`, over which `η` extends, so `η` is nullhomotopic. Contradiction.

Hatcher obtains the nullhomotopy directly because the equator bounds a
hemisphere disc. The current DAG instead routes this step through
[simple connectivity of `S²`](sphere-simply-connected.md). That is a valid but
strictly stronger Lean route, not an attribution to Hatcher's proof. The other
dependency is the [circle computation](fundamental-group-circle.md): proving an
odd loop has odd winding number carries the real formalization cost, since its
lift must satisfy `η̃(s + 1/2) = η̃(s) + (2k+1)/2`.

Borsuk–Ulam is not in the pinned Mathlib in any dimension.

Formalized as `Hatcher.Sphere.exists_eq_neg` in
`Hatcher/Sphere/BorsukUlam.lean`. The implementation replaces the coordinate
equator by an arbitrary path from `x` to `-x` followed by its antipodal image;
this avoids coordinate bookkeeping while preserving Hatcher's odd-winding
obstruction.

## Depends on

- [The fundamental group of the circle](fundamental-group-circle.md)
- [Higher spheres are simply connected](sphere-simply-connected.md)

## Sources

- [Hatcher §1.1, Theorem 1.10, pages 32–33](../../../sources/hatcher-1-1.md)
