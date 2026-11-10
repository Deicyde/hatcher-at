---
article_id: af_07101a56629e9ad3a0c03550
declaration: theorem
origin: bridged
---

# Positive-dimensional skeletal pairs have the cell basis

For every n > 0 and classical CW complex X, Hₖ(Xⁿ,Xⁿ⁻¹;ℤ) vanishes when
k ≠ n. In degree n, construct its isomorphism with the finite-support integer
functions on the actual n-cells. The standard vector of a cell maps to the
relative fundamental class induced by its characteristic map, with the
fixed orientation of the standard cell. Include arbitrary cell families.

## Proof sketch

For a nonempty lower skeleton, use its good pair, the actual quotient-wedge
homeomorphism, good-pair comparison naturality, wedge additivity and the
oriented sphere calculation. If the lower skeleton is empty, a positive cell
would send its nonempty boundary into that empty space; hence no such cell
exists and the successor skeleton is empty. Transport the fixed generators
across universe lifts when needed.

## Depends on

- [Relative singular homology](../../simplicial-and-singular/relative-homology/relative-singular-homology.md)

## Proof depends on

- [Nonempty subcomplex good pair](nonempty-subcomplex-good-pair.md)
- [Skeleton quotient wedge](skeleton-quotient-wedge.md)
- [Sphere point good pair](sphere-point-good-pair.md)
- [Good pair point quotient relative homology](../../simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-point-quotient-relative-homology.md)
- [Good pair quotient comparison naturality](../../simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-quotient-comparison-naturality.md)
- [Wedge reduced homology](../post-excision-applications/wedge-reduced-homology.md)
- [Sphere reduced homology](../sphere-homology/sphere-reduced-homology.md)
- [Double simplex sphere homeomorphism](../post-excision-applications/double-simplex-sphere-homeomorphism.md)
- [Reduced positive degree comparison](../../simplicial-and-singular/relative-homology/reduced-positive-degree-comparison.md)

- [The ordered sphere generator lifts with its defining cycle](sphere-lifted-ordered-fundamental-class.md)

## Sources

- [Hatcher §2.2, cellular homology, printed pages 137–140](../../../../sources/hatcher-2-2-cellular.md#lemma-234)
- [Cellular-homology implementation specification](../../../../sources/cellular-homology-implementation.md)
