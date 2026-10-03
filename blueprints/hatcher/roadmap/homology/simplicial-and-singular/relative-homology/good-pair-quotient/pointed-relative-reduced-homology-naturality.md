---
article_id: af_90639a13c044152fff528cfe
source_units: [hatcher-2-1-good-pair-quotient]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Relative.pointedPairHomologyIso_naturality
---

# The pointed relative-to-reduced comparison is natural

For a based continuous map, prove naturality of
`Hatcher.Relative.pointedPairHomologyIso` in every degree. Include naturality
of the reduced-pair projection and the degree-zero sequence map, so the result
does not silently omit the terminal endpoint.

The intended main theorem is
`Hatcher.Relative.pointedPairHomologyIso_naturality`. It is a general bridge,
not restricted to good pairs.

## Depends on

- [Relative homology at a basepoint is reduced homology](../pointed-relative-reduced-homology.md)

## Proof depends on

- [The reduced pair long exact sequence is natural](../reduced-pair-long-exact-sequence-naturality.md)

## Sources

- [Hatcher §2.1, naturality of reduced pair sequences, pages 127–128](../../../../../sources/hatcher-2-1.md)
- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
