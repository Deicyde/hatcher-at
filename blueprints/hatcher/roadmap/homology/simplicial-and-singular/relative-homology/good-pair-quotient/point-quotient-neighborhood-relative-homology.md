---
article_id: af_345a2474df13c2f42cc9e4eb
source_units: [hatcher-2-1-good-pair-quotient]
declaration: instance
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Relative.GoodPairData.pointQuotientPairToNeighborhoodPair_homologyMap_isIso
---

# Enlarging the quotient point preserves relative homology

For good-pair data, prove that the canonical map

`H_n(X/A,A/A;R) → H_n(X/A,V/A;R)`

is an isomorphism in every degree. The quotient-neighborhood contraction gives
the required component homotopy equivalence; apply the componentwise
relative-homology criterion and retain the canonical functorial map.

The ambient component of `pointQuotientPairToNeighborhoodPair` is the
identity on `X/A`, while its subspace component is definitionally the forward
map of `pointQuotientNeighborhoodHomotopyEquiv`. Ordinary homology therefore
sends both components to isomorphisms, and `homologyMap_isIso_of_components`
proves that the exact canonical relative-homology map is an isomorphism for
every degree, including degree zero.

## Depends on

- [Restricting the quotient to a good-pair neighborhood](good-pair-neighborhood-quotient.md)

## Proof depends on

- [The quotient neighborhood contracts to its point](point-quotient-neighborhood-contraction.md)
- [Componentwise isomorphisms imply a relative isomorphism](relative-homology-map-isomorphism-criterion.md)
- [A homotopy equivalence induces homology isomorphisms](../../homotopy-equivalence-homology-iso.md)

## Sources

- [Hatcher §2.1, proof of Proposition 2.22, page 124](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
