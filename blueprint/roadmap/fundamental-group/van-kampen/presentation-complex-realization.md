---
declaration: theorem
origin: bridged
not_ready: true
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

This node is not ready. Mathlib's `HomotopicalAlgebra.AttachCells` records an
abstract coproduct and pushout, but it does not provide the point-set
adjunction-space model, collar neighborhoods, or deformation data needed by
the current proof of the 2-cell attachment theorem. The required well-pointed
neighborhood of the circle is now formalized, but the attachment geometry
remains a separate obligation rather than a consequence of `PresentedGroup`.

Once this theorem exists, the arbitrary-group corollary is only the
composition of its equivalence with `Hatcher.exists_presentedGroup_equiv`.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [The fundamental group of a wedge of circles](wedge-circles-free-group.md)
- [Attaching 2-cells adds the attaching relations](attach-two-cells-fundamental-group.md)

## Sources

- [Hatcher §1.2, proof of Corollary 1.28, page 52](../../../sources/hatcher-1-2.md)
