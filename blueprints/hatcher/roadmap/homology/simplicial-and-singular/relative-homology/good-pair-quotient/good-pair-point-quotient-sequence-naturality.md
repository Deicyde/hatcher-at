---
article_id: af_1681cfca508c6b0f47bd1569
source_units: [hatcher-2-1-good-pair-quotient]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Relative.goodPairPointQuotientConnecting_naturality
---

# Naturality of the good-pair quotient sequence

**Hatcher, §2.1 (printed page 128).** Every map of good pairs induces the
corresponding map between quotient exact sequences. Define the morphisms of
six-term windows and prove every square commutes, including the connecting
square, overlap compatibility, and the degree-zero endpoint.

The induced map `X/A → Y/B` comes from the point-quotient functor. The theorem
must not require the map of pairs to preserve chosen neighborhood or
deformation-retraction witnesses.

Formalized in
`Hatcher/Singular/GoodPairPointQuotientSequenceNaturality.lean`. The main
theorem `Hatcher.Relative.goodPairPointQuotientConnecting_naturality`
transports reduced-pair connecting naturality through the Proposition 2.22
natural isomorphism. The definitions
`Hatcher.Relative.goodPairPointQuotientSequenceMap` and
`Hatcher.Relative.goodPairPointQuotientZeroSequenceMap` package the six-term
and terminal degree-zero sequence maps. Their quotient components are exactly
the reduced-homology maps induced by `pointQuotientMap f.hom`; the module also
records both quotient squares, compatibility on all three terms shared by
successive windows, the final square to zero, and compatibility of the
terminal sequence with the degree-one/degree-zero window. All declarations
take an ordinary morphism in the full good-pair subcategory and use no chosen
good-pair witness data.

## Depends on

- [The good-pair quotient exact sequence](good-pair-point-quotient-exact-sequence.md)

## Proof depends on

- [The pointed relative-to-reduced comparison is natural](pointed-relative-reduced-homology-naturality.md)
- [The good-pair quotient comparison is natural](good-pair-quotient-comparison-naturality.md)
- [The reduced pair long exact sequence is natural](../reduced-pair-long-exact-sequence-naturality.md)

## Sources

- [Hatcher §2.1, naturality of Theorem 2.13, page 128](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
