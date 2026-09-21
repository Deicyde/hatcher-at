---
article_id: af_5d288dd83abaf2eee954ea08
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
---

# Presented groups have two-dimensional presentation complexes

For a generator type `S` and relators `rels : Set (FreeGroup S)`, construct
the presentation complex with one vertex, one oriented 1-cell for each
generator, and one 2-cell for each relator. Prove that it is an abstract
two-dimensional CW complex and that its fundamental group is the corresponding
`PresentedGroup`.

Intended artifact:
`Hatcher.exists_presentationComplex_fundamentalGroupEquiv`.

The source-facing Lean statement should be equivalent to:

```lean
theorem exists_presentationComplex_fundamentalGroupEquiv
    (S : Type u) (rels : Set (FreeGroup S)) :
    ∃ (X : TopCat.{u}) (x₀ : X) (c : TopCat.CWComplex X),
      (∀ γ : HomotopicalAlgebra.RelativeCellComplex.Cells c, γ.j ≤ 2) ∧
        Nonempty (PresentedGroup rels ≃* FundamentalGroup X x₀)
```

The construction must use the wedge of `S` circles as the 1-skeleton and
attach one 2-cell along a loop representing each relator. The proof must check
that these are the only positive-dimensional cells; merely producing a space
with the required fundamental group does not establish Hatcher's
two-dimensional conclusion.

The generic 2-cell attachment model and theorem are formalized. The remaining
construction is now decomposed in
[presentation-complex support](README.md):
it supplies the wedge's one-cell attachment, based representatives for
relators, the concrete two-cell attachment and group calculation, and the
eventually constant CW sequence with its dimension bound. These interfaces
avoid the unrelated unresolved bridge between Mathlib's classical and
categorical CW APIs.

Once this theorem exists, the arbitrary-group corollary is only the
composition of its equivalence with `Hatcher.exists_presentedGroup_equiv`.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [The presentation complex has the presented fundamental group](presentation-complex-fundamental-group.md)
- [The presentation complex is an abstract two-dimensional CW complex](presentation-complex-cw-structure.md)

## Sources

- [Hatcher §1.2, proof of Corollary 1.28, page 52](../../../../sources/hatcher-1-2.md)
- [Presentation-complex implementation specification](../../../../sources/presentation-complex-implementation.md)
