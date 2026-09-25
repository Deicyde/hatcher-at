---
article_id: af_53042df9d43d42059a2311d5
source_units: [hatcher-2-1-relative-homology-les]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Relative.congr_homologyMap
---

# Homotopic maps of pairs induce the same relative-homology map

**Hatcher, Proposition 2.19 (page 118).** If two maps
`f,g : (X,A) ⟶ (Y,B)` are homotopic through maps of pairs, then they induce
the same map `Hₙ(X,A;R) ⟶ Hₙ(Y,B;R)` in every degree.

`Hatcher.Relative.congr_homologyMap` applies chain-homotopy invariance to the
compatible relative chain homotopy constructed by
`Hatcher.Relative.chainHomotopyOfPairHomotopy`. The proof therefore descends
the explicit ambient and subspace homotopies to relative chains before passing
to homology; it does not treat the `HomologyPretheory.IsHomotopyInvariant`
interface as a proof of the result.

## Depends on

- [Relative singular chains and homology](relative-singular-homology.md)

## Proof depends on

- [A homotopy of pairs gives a relative chain homotopy](relative-singular-chain-homotopy.md)
- [Chain-homotopic maps induce the same homology map](../chain-homotopy-invariance.md)

## Sources

- [Hatcher §2.1, Proposition 2.19, page 118](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
