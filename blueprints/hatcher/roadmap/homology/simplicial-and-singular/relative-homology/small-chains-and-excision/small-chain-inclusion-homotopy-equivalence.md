---
article_id: af_d49202a5a6ec350660634b56
source_units: [hatcher-2-1-small-chains-excision]
declaration: def
origin: cited
---

# Small singular chains include by a chain-homotopy equivalence

**Hatcher, Proposition 2.21 (pages 119–124).** For a family of subsets whose
interiors cover `X`, the canonical inclusion from the subordinate singular
chain complex into the full singular chain complex is a chain-homotopy
equivalence. State the categorical form for `X : TopCat.{w}`, `{C : Type u}`,
`[Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]`, and `R : C`;
Hatcher's integral version is the specialization to `AddCommGrpCat.of ℤ`.

The main artifact, intended as
`Hatcher.Excision.smallChainInclusionHomotopyEquiv`, must have that canonical
inclusion as its forward map. Choose the least subdivision depth `m(σ)` for
each simplex, prove that faces require no greater depth, form Hatcher's
variable-depth homotopy, and define the corrected retraction
`ρ = 1 - ∂D - D∂`. Verify that `ρ` lands in the subordinate subcomplex,
that `ρ ∘ ι = id`, and that `ι ∘ ρ` is homotopic to the identity. A
homology-isomorphism statement may
be recorded as a corollary, but it is not a substitute for the chain-level
main result.

## Depends on

- [Iterated subdivision eventually makes every singular simplex small](eventually-small-singular-simplices.md)

## Proof depends on

- [Singular-chain subdivision is naturally homotopic to the identity](singular-chain-subdivision-homotopy.md)

## Sources

- [Hatcher §2.1, Proposition 2.21, pages 119–124](../../../../../sources/hatcher-2-1.md)
- [Singular excision implementation specification](../../../../../sources/excision-implementation.md)
- [Riou's small-chain implementation prior art](https://github.com/joelriou/excision/blob/8b56cd0c8e5f39a7c2f36418c80b298e469596a6/Excision/SmallSimplices.lean)
