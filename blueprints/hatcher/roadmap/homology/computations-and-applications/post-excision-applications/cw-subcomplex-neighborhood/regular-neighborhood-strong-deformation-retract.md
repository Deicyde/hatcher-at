---
article_id: af_3397bfd09838597452912b09
source_units: [appendix-proposition-a-5]
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.ClassicalCW.regularNeighborhoodStrongDeformationRetract
---

# A regular neighborhood strongly deformation retracts onto its subcomplex

**Hatcher, Appendix Proposition A.5 (printed page 523).** For every
subcomplex `A` of a classical CW complex, the canonical inclusion of `A` into
its fixed-width regular neighborhood is a strong deformation retract:

```lean
def Hatcher.ClassicalCW.regularNeighborhoodStrongDeformationRetract
    (A : CWComplex.Subcomplex C) :
    Hatcher.StrongDeformationRetract
      (regularNeighborhoodInclusion A)
```

Assemble the cellwise radial deformations dimension by dimension, fixing `A`
throughout. The proof must establish continuity of the global homotopy, not
merely continuity on each open cell; it may use the existing compact-subset
and successor-skeleton infrastructure to justify the closed-cell-times-
interval gluing step.

## Depends on

- [A common regular-neighborhood system for subcomplexes](regular-neighborhood-system.md)
- [Strong deformation retracts](../../../simplicial-and-singular/relative-homology/good-pair-quotient/strong-deformation-retract.md)

## Sources

- [Hatcher, Appendix Proposition A.5, printed page 523](../../../../../sources/hatcher-appendix-a5.md)
- [CW-subcomplex neighborhood implementation specification](../../../../../sources/cw-subcomplex-neighborhood-implementation.md)
