---
article_id: af_01a39a5c18f0240f7888c0f7
source_units: [hatcher-1-1-basic-constructions]
declaration: theorem
origin: cited
mathlib: true
mathlib_declaration: Path.Homotopic.equivalence
mathlib_file: Mathlib/Topology/Homotopy/Path.lean
---

# Path homotopy is an equivalence relation

**Hatcher, Proposition 1.2 (page 26).** Homotopy of paths relative to their
endpoints is an equivalence relation.

This is exactly the pinned theorem `Path.Homotopic.equivalence`:
`Equivalence (@Path.Homotopic X _ x₀ x₁)`. Mathlib also installs the resulting
`IsEquiv` instance, which makes endpoint-preserving homotopy classes available
as `Path.Homotopic.Quotient x₀ x₁`.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.1, Proposition 1.2, page 26](../../../sources/hatcher-1-1.md)
