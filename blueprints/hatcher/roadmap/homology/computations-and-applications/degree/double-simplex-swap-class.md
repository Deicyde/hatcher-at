---
article_id: af_e6003b902922b5db4aeeda3f
source_units: [hatcher-2-2-degree-foundations]
declaration: theorem
origin: bridged
---

# Swapping the double simplex negates its fundamental class

Define the automorphism of `Hatcher.Simplex.doubleSimplex n` induced by
exchanging its two standard-simplex summands. Its restrictions to the common
ordered boundary must agree, so the map descends through the pushout.

Prove at chain level that the swap sends the first-simplex-minus-second-
simplex cycle to its negative. The main result is the corresponding homology
formula

```lean
theorem Hatcher.Simplex.doubleSimplexFundamentalClass_map_swap ... :
  doubleSimplexFundamentalClass R n ≫
      (Hatcher.Reduced.homologyFunctor R n).map
        (doubleSimplexSwapIso n).hom =
    -doubleSimplexFundamentalClass R n
```

with integral coefficients as the source-facing specialization.

## Depends on

- [The ordered difference of the two simplices is a cycle](../post-excision-applications/double-simplex-fundamental-cycle.md)
- [The double-simplex difference generates reduced homology](../post-excision-applications/double-simplex-fundamental-class.md)

## Sources

- [Hatcher §2.2, reflection calculation in property (e), printed page 134](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
