---
article_id: af_40ecfa37c3493430859955e2
source_units: [hatcher-2-1-small-chains-excision]
declaration: theorem
origin: bridged
---

# The binary-cover excision chain map is a homotopy equivalence

Let `A` and `B` be subsets of `X` with
`interior A ∪ interior B = Set.univ`. This review unit exposes the supporting
public predicate `Hatcher.Excision.CoverCondition A B` and, for
`h : CoverCondition A B`, the canonical map
`Hatcher.Excision.coverPairHom h` of topological pairs

`(B, A ∩ B) → (X, A)`.

For `{C : Type u}`, `[Category.{v} C]`, `[Preadditive C]`,
`[HasCoproducts.{w} C]`, and `R : C`, the main theorem, intended as
`Hatcher.Excision.coverChainMap_homotopyEquivalence`, says that the image of
`coverPairHom h` under `Hatcher.Relative.chainComplexFunctor R` is a
chain-homotopy equivalence. These two supporting declarations are why the
homology endpoint has a statement dependency on this review unit.

Use the existing `Hatcher.Relative.singularPairFunctor`; do not introduce a
second conversion from topological pairs to simplicial-set pairs. The proof
identifies the binary small-simplices subcomplex with the union of the two
subcomplexes, applies Proposition 2.21, and transports the result through the
relative-chain dévissage theorem.

## Depends on

- [Relative singular chains and homology](../relative-singular-homology.md)

## Proof depends on

- [Small singular chains include by a chain-homotopy equivalence](small-chain-inclusion-homotopy-equivalence.md)
- [Relative excision reduces to the union subcomplex](relative-chain-union-devissage.md)

## Sources

- [Hatcher §2.1, binary-cover proof of Theorem 2.20, page 124](../../../../../sources/hatcher-2-1.md)
- [Singular excision implementation specification](../../../../../sources/excision-implementation.md)
- [Riou's chain-level excision implementation prior art](https://github.com/joelriou/excision/blob/8b56cd0c8e5f39a7c2f36418c80b298e469596a6/Excision/Excision.lean)
