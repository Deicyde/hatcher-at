---
article_id: af_6cab8eafd3aeafc53888d4dd
source_units: [hatcher-2-1-relative-homology-les]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Relative.chainHomotopyOfPairHomotopy
---

# A homotopy of pairs gives a relative chain homotopy

For homotopic maps of topological pairs, descend the compatible singular-chain
homotopies on the ambient spaces and subspaces through the relative-chain
cokernels. The result is a chain homotopy between the induced maps on relative
singular chain complexes.

`Hatcher.Relative.chainHomotopyOfPairHomotopy` carries this out degreewise by
the cokernel universal property. It first proves that the ambient and subspace
singular-chain homotopies commute with the inclusions, then descends the
ambient homotopy to the relative quotient. This compatibility is essential:
an unrelated pair of absolute chain homotopies does not define a map on the
quotient complex.

## Depends on

- [Relative singular chains and homology](relative-singular-homology.md)

## Proof depends on

- [A topological homotopy gives a singular-chain homotopy](../topological-homotopy-chain-homotopy.md)

## Sources

- [Hatcher §2.1, proof of Proposition 2.19, page 118](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
