---
article_id: af_1259fc0c85b68b0d2f27a1bc
source_units: [hatcher-2-1-good-pair-quotient]
declaration: instance
origin: bridged
---

# Enlarging to the chosen neighborhood preserves relative homology

For good-pair data on `(X,A)`, prove that the canonical map

`H_n(X,A;R) → H_n(X,V;R)`

is an isomorphism in every degree. The intended main declaration is an
`IsIso` instance for the exact map produced by
`Hatcher.Relative.homologyFunctor`.

Use the chosen deformation retraction to identify the subspace component and
the componentwise relative-homology criterion. The canonical map, not an
unspecified object isomorphism, is the endpoint.

## Depends on

- [Good pairs and neighborhood deformation retracts](good-pair-data.md)

## Proof depends on

- [Componentwise isomorphisms imply a relative isomorphism](relative-homology-map-isomorphism-criterion.md)
- [A homotopy equivalence induces homology isomorphisms](../../homotopy-equivalence-homology-iso.md)

## Sources

- [Hatcher §2.1, proof of Proposition 2.22, page 124](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
