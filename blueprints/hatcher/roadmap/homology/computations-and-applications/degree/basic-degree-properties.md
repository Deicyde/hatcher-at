---
article_id: af_c25aace6019fc7573293d3ca
source_units: [hatcher-2-2-degree-foundations]
declaration: theorem
origin: cited
---

# The formal properties of degree

Prove that sphere degree sends the identity to `1`, is multiplicative under
composition, and is invariant under homotopy. The unique main result is

```lean
theorem Hatcher.Sphere.degree_eq_one_or_neg_one_of_homotopyEquiv ... :
  degree n hn f = 1 ∨ degree n hn f = -1
```

for the forward map of a sphere self-homotopy-equivalence. Supporting lemmas
must retain the categorical composition order used by `TopCat` and expose the
integer multiplier rather than an unspecified automorphism of homology.

Do not formalize the converse “equal degree implies homotopic”; Hatcher
postpones it to Corollary 4.25.

## Depends on

- [Degree is the multiplier of the ordered sphere class](sphere-degree-definition.md)

## Sources

- [Hatcher §2.2, degree properties (a), (c), and (d), printed page 134](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
