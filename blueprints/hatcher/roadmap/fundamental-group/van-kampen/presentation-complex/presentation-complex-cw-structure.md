---
article_id: af_5722cc28c5abdb41e886a338
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.presentationComplexCWComplex
---

# The presentation complex is an abstract two-dimensional CW complex

Equip the concrete presentation complex with Mathlib's abstract CW-complex
structure by assembling its zero-, one-, and two-cell attachments and an
empty constant tail.

Intended main artifact:

```lean
noncomputable def Hatcher.presentationComplexCWComplex
    {S : Type u} (rels : Set (FreeGroup S)) :
    TopCat.CWComplex (TopCat.of (Hatcher.presentationComplex rels))
```

Also expose the source-facing dimension bound:

```lean
theorem Hatcher.presentationComplexCWComplex_cells_dim_le_two
    {S : Type u} (rels : Set (FreeGroup S))
    (γ : HomotopicalAlgebra.RelativeCellComplex.Cells
      (Hatcher.presentationComplexCWComplex rels)) :
    γ.j ≤ 2
```

Use the sequence `initial → point → wedge → presentationComplex`, constant
from stage three onward. Its cell indices are one point in dimension zero,
`S` in dimension one, `rels` in dimension two, and empty in every higher
dimension. The empty tail, not an informal dimension convention, must prove
the bound.

## Depends on

- [A point is one standard zero-cell](point-zero-cell-attachment.md)
- [A wedge of circles is an indexed one-cell attachment](wedge-circles-one-skeleton.md)
- [Free-group relators form a standard two-cell attachment](relator-cell-attachment.md)
- [The identity attaches an empty family of cells](empty-cell-attachment-constructor.md)
- [Eventually constant cell sequences form abstract CW complexes](eventually-constant-cell-sequence.md)

## Sources

- [Hatcher §1.2, proof of Corollary 1.28, page 52](../../../../sources/hatcher-1-2.md)
- [Presentation-complex implementation specification](../../../../sources/presentation-complex-implementation.md)
