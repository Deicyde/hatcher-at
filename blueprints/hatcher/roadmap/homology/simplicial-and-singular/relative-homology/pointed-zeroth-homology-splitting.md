---
article_id: af_3c5607bf6881ebacd23e2767
source_units: [hatcher-2-1-relative-homology-les]
declaration: def
origin: cited
---

# Zeroth homology splits into reduced homology and the coefficient object

**Hatcher, §2.1 (page 110).** For a space `X` with a chosen point and
coefficient object `R`, split the augmentation to obtain
`H₀(X;R) ≅ H̃₀(X;R) ⊞ R`.

The main artifact should be `Hatcher.Reduced.homologyZeroIso`. The chosen
point supplies a section of the augmentation. The result is deliberately not
claimed to be natural for unpointed spaces.

## Depends on

- [Reduced singular homology](reduced-singular-homology.md)
- [Zeroth homology is free on path components](../zeroth-homology-components.md)

## Sources

- [Hatcher §2.1, reduced homology, page 110](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
