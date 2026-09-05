---
article_id: af_66d5f24ab6fa333843941b48
source_units: [hatcher-2-1-selected-spine]
declaration: def
origin: cited
mathlib: true
mathlib_declaration: TopCat.singularHomology₀Iso
mathlib_file: Mathlib/AlgebraicTopology/SingularHomology/HomologyZero.lean
---

# Zeroth homology is free on path components

**Hatcher, Proposition 2.7 (pages 109–110).** For a space `X`, zeroth
singular homology with coefficients in `R` is isomorphic to the
coproduct of one copy of `R` for each path component of `X`. In particular, a
nonempty path-connected space has integral zeroth homology isomorphic to `ℤ`.

The pinned definition `TopCat.singularHomology₀Iso` gives the component-indexed
isomorphism using `ZerothHomotopy X`. The associated augmentation is
`TopCat.singularHomology₀ε`, and Mathlib supplies its `IsIso` instance for a
path-connected space.

## Depends on

- [Singular homology](singular-homology.md)

## Sources

- [Hatcher §2.1, Proposition 2.7](../../../sources/hatcher-2-1.md)
