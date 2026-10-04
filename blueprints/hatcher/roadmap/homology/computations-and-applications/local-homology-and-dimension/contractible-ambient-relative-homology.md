---
article_id: af_eb5fb984d257557c4e2ad751
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: bridged
statement: formalized
lean: Hatcher.Relative.contractibleAmbientRelativeHomologyIso
---

# Relative homology in a contractible ambient space

Let `P : TopPair` have nonempty subspace and contractible ambient space. For
adjacent degrees `i + 1 = n`, construct the canonical isomorphism

`H_n(P.fst, P.snd;R) ≅ H̃_i(P.snd;R)`

whose forward map is the connecting morphism in the reduced long exact
sequence of the pair. Prove separately that `H_0(P.fst,P.snd;R)` is a zero
object. The main result is
`Hatcher.Relative.contractibleAmbientRelativeHomologyIso`; the degree-zero
statement is part of the same public review unit.

This packages the exact-sequence calculation used by Hatcher for punctured
Euclidean space. It must retain the canonical connecting map rather than
choosing an unrelated isomorphism.

## Depends on

- [The reduced long exact sequence of a nonempty pair](../../simplicial-and-singular/relative-homology/reduced-pair-long-exact-sequence.md)

## Proof depends on

- [Reduced homology of a contractible space vanishes](../sphere-homology/contractible-space-reduced-homology.md)

## Sources

- [Hatcher §2.1, proof of Theorem 2.26, page 126](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)
