---
declaration: theorem
origin: cited
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

Intended artifact: `Hatcher.Sphere.exists_eq_neg` in
`Hatcher/Sphere/BorsukUlam.lean`.

## Proof depends on

- [The fundamental group of the circle](fundamental-group-circle.md)
- [Higher spheres are simply connected](sphere-simply-connected.md)

## Sources

- [Hatcher §1.1, Theorem 1.10, pages 32–33](../../../sources/hatcher-1-1.md)
