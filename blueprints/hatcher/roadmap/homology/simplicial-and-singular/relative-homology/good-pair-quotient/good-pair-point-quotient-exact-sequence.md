---
article_id: af_e11b1e1dac0e10649ea63070
source_units: [hatcher-2-1-good-pair-quotient]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Relative.goodPairPointQuotientSequence_exact
---

# The good-pair quotient exact sequence

**Hatcher, Theorem 2.13 (printed page 114).** For a good pair `(X,A)`, define
the adjacent six-term windows in the reduced sequence

`H̃_n(A;R) → H̃_n(X;R) → H̃_n(X/A;R) →`
`H̃_m(A;R) → H̃_m(X;R) → H̃_m(X/A;R)`

for `m + 1 = n`, and prove every position exact. Include overlap lemmas, the
terminal exact sequence ending `H̃_0(X/A;R) → 0`, endpoint glue, and a
long-exact package.

Both maps into quotient homology must literally be induced by the ambient
quotient `q`. Define the connecting map by transporting the reduced-pair
connecting morphism through the Proposition 2.22 comparison.

Formalized in
`Hatcher/Singular/GoodPairPointQuotientExactSequence.lean`. The definition
`Hatcher.Relative.goodPairPointQuotientSequence` writes both maps into
quotient homology literally as the maps induced by
`pointQuotientProjection`. The connecting morphism is the inverse of the
canonical Proposition 2.22 comparison followed by `reducedPairConnecting`.
`Hatcher.Relative.goodPairPointQuotientSequence_exact` proves every six-term
window exact by transport from the reduced-pair sequence. The same module
proves consecutive-window overlap, the exact terminal degree-zero sequence,
its glue to the degree-one/degree-zero window, and the combined theorem
`Hatcher.Relative.goodPairPointQuotientLongExact`.

## Depends on

- [The good-pair quotient comparison is natural](good-pair-quotient-comparison-naturality.md)
- [The reduced long exact sequence of a nonempty pair](../reduced-pair-long-exact-sequence.md)

## Sources

- [Hatcher §2.1, Theorem 2.13, page 114](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
