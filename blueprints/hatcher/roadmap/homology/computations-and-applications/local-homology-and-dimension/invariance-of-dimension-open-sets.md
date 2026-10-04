---
article_id: af_95e4bb7e36db9514602e747b
source_units: [hatcher-2-1-post-excision-applications]
declaration: theorem
origin: cited
lean: Hatcher.Euclidean.invarianceOfDimension_open
statement: formalized
proof: formalized
---

# Homeomorphic nonempty Euclidean open sets have equal dimension

**Hatcher, Theorem 2.26 (printed page 126).** Let
`U ⊆ EuclideanSpace ℝ (Fin m)` and
`V ⊆ EuclideanSpace ℝ (Fin n)` be nonempty open sets. If their subtype
spaces are homeomorphic, then `m = n`.

The intended main result is
`Hatcher.Euclidean.invarianceOfDimension_open`. For positive dimensions,
choose a point of `U`, compare the local relative-homology groups through the
homeomorphism and the open-neighborhood theorem, and use the punctured
Euclidean calculation with integral coefficients to detect the unique nonzero
degree. The contradiction uses the nonzero object `AddCommGrpCat.of ℤ`; it is
not stated for an arbitrary coefficient object, which could be zero.

Handle dimension zero separately: a nonempty open subset of
zero-dimensional Euclidean space is subsingleton, while a nonempty open subset
in positive dimension contains two distinct points. Do not use `m - 1`, a
fictitious negative sphere, or the stronger invariance-of-domain theorem.

## Depends on

None beyond the Euclidean open-set and homeomorphism data in the statement.

## Proof depends on

- [Local homology is unchanged on an open neighborhood](local-homology-open-neighborhood.md)
- [Local homology of positive-dimensional Euclidean space](punctured-euclidean-local-homology.md)

## Sources

- [Hatcher §2.1, Theorem 2.26, page 126](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)

## Prior art

Open Mathlib PR
[#36770](https://github.com/leanprover-community/mathlib4/pull/36770)
uses Brouwer's fixed-point theorem to prove invariance of domain and a
conditional dimension theorem for whole finite-dimensional spaces. It is not
present at the project pin and does not state this open-subset homological
theorem.
