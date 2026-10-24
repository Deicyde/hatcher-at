---
article_id: af_b27bb3e374b92a7334095698
source_units: [hatcher-2-2-degree-realization-suspension]
declaration: theorem
origin: bridged
---

# A puncture-preserving local homotopy preserves local degree

For n > 0, let f and g be continuous self-maps of the standard n-sphere. Suppose U is open and contains x, and a continuous H : I × U → Sⁿ joins their restrictions. Assume H(t,x) = y and H(t,z) ≠ y for every t and every z in U other than x. Then x is an isolated preimage for both maps and their signed local degrees at x over y agree, independently of the witnesses.

## Proof sketch

Restrict H to the punctured neighborhood to obtain an actual homotopy of pair maps (U,U−{x}) → (Sⁿ,Sⁿ−{y}). Relative homotopy invariance identifies the induced maps, and the two local fundamental-class equations identify the integers. An arbitrary local homotopy without the puncture-preserving condition is not enough.

## Depends on

- [local degree well defined](../../local-degree/local-degree-well-defined.md)

## Proof depends on

- [relative homology homotopy invariance](../../../simplicial-and-singular/relative-homology/relative-homology-homotopy-invariance.md)
- [neighborhood local degree](../../local-degree/neighborhood-local-degree.md)

## Sources

- [Hatcher §2.2, printed pages 136–137](../../../../../sources/hatcher-2-2-degree-applications.md#example-232)
- [Degree-realization and suspension specification](../../../../../sources/degree-applications-implementation.md)
