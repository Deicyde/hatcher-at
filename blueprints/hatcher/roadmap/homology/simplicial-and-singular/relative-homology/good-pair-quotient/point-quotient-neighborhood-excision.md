---
article_id: af_ca7400a4baee60c2a4693910
source_units: [hatcher-2-1-good-pair-quotient]
declaration: instance
origin: bridged
---

# The neighborhood quotient map preserves relative homology

Prove that the canonical map

`H_n(X,V;R) → H_n(X/A,V/A;R)`

is an isomorphism. Compare both sides by deleted-subset excision and the
homeomorphism induced by the quotient map on complements. The intended main
declaration is an `IsIso` instance for the exact vertical map in the
complementary excision diagram.

## Depends on

- [The complementary excision diagram](good-pair-excision-diagram.md)

## Proof depends on

- [Deleted-subset excision induces homology isomorphisms](../small-chains-and-excision/deleted-subset-excision-homology-isomorphism.md)

## Sources

- [Hatcher §2.1, proof of Proposition 2.22, page 124](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
