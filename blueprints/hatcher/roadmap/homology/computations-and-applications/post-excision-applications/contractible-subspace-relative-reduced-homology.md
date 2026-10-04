---
article_id: af_5af80c1672a496d005d3afa3
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Relative.contractibleSubspaceHomologyIso
---

# A contractible subspace identifies reduced and relative homology

Let `P : TopPair.{w}` have contractible subspace `P.snd`. For an object `R` in
an abelian category with the coproducts required by singular chains, construct
in every degree `n` an isomorphism

`Hatcher.Relative.contractibleSubspaceHomologyIso P R n :`
`  (Hatcher.Reduced.homologyFunctor R n).obj P.fst ≅`
`    (Hatcher.Relative.homologyFunctor R n).obj P`.

The forward morphism must be exactly
`Hatcher.Relative.reducedPairProjection P R n`, not an unspecified isomorphism.
First prove the supporting instance
`Hatcher.Relative.reducedPairProjection_isIso_of_contractibleSubspace` and
define the displayed isomorphism with `asIso`.

This is the reusable exact-sequence step behind the first isomorphism on
Hatcher page 125. Reduced homology of the contractible subspace vanishes in
all degrees. For positive-degree windows, exactness makes the reduced-pair
projection both monic and epic; degree zero must use the separately formalized
terminal sequence
`H̃₀(P.snd) ⟶ H̃₀(P.fst) ⟶ H₀(P) ⟶ 0`.
The contractibility assumption already supplies nonemptiness, so do not add a
redundant chosen point or strengthen the topological hypotheses.

## Depends on

- [Relative singular chains and homology](../../simplicial-and-singular/relative-homology/relative-singular-homology.md)
- [Reduced singular homology](../../simplicial-and-singular/relative-homology/reduced-singular-homology.md)
- [The pointed relative-to-reduced comparison is natural](../../simplicial-and-singular/relative-homology/good-pair-quotient/pointed-relative-reduced-homology-naturality.md)

## Proof depends on

- [The reduced long exact sequence of a nonempty pair](../../simplicial-and-singular/relative-homology/reduced-pair-long-exact-sequence.md)
- [Reduced homology of a contractible space vanishes](../sphere-homology/contractible-space-reduced-homology.md)

## Sources

- [Hatcher §2.1, arbitrary-pair mapping-cone comparison, page 125](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)
