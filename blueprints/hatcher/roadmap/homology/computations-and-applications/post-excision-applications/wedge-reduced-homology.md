---
article_id: af_c8461d2db3fb08c9bd7f4e52
source_units: [hatcher-2-1-post-excision-applications]
declaration: corollary
origin: cited
lean: Hatcher.PointedWedge.reducedHomologyCoproductMap_isIso
statement: formalized
proof: formalized
---

# Reduced homology of a wedge is the direct sum of the summands

**Hatcher, Corollary 2.25 (printed page 126).** For a family of pointed
spaces `(X i,x₀ i)`, define the canonical morphism

```lean
Hatcher.PointedWedge.reducedHomologyCoproductMap X x₀ R n :
  (∐ i, H̃_n(X i;R)) ⟶ H̃_n(PointedWedge X x₀;R)
```

as `Sigma.desc` of the reduced-homology maps induced by the canonical summand
inclusions. If every pointed pair `(X i,{x₀ i})` is good and the relevant
coproducts are exact, prove that this exact morphism is an isomorphism. The
main theorem is
`Hatcher.PointedWedge.reducedHomologyCoproductMap_isIso`.

For a nonempty family, compare pointed relative homology summandwise, use the
relative-homology coproduct isomorphism, apply Proposition 2.22 to the sigma
good pair, and identify its point quotient with the existing wedge. Use the
completed naturality theorems to prove that the resulting composite is the
displayed canonical map. For an empty family, prove the result directly from
the contractibility of the empty pointed wedge and the initial empty
coproduct.

Expose an integral specialization with no explicit AB4 hypothesis; this is
Hatcher's direct sum of abelian groups.

## Depends on

- [Relative homology commutes with exact coproducts](relative-homology-coproduct.md)
- [A nonempty coproduct of pointed good pairs is good](sigma-good-pair.md)
- [The pointed wedge is the point quotient of the sigma pair](pointed-wedge-point-quotient.md)
- [Relative homology at a basepoint is reduced homology](../../simplicial-and-singular/relative-homology/pointed-relative-reduced-homology.md)

## Proof depends on

- [The pointed relative-to-reduced comparison is natural](../../simplicial-and-singular/relative-homology/good-pair-quotient/pointed-relative-reduced-homology-naturality.md)
- [The good-pair quotient comparison is natural](../../simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-quotient-comparison-naturality.md)
- [Reduced homology of a contractible space vanishes](../sphere-homology/contractible-space-reduced-homology.md)
- [The standard cover of a well-pointed wedge](../../../fundamental-group/van-kampen/well-pointed-wedge-cover.md)

## Sources

- [Hatcher §2.1, Corollary 2.25, printed page 126](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)
