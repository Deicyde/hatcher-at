---
article_id: af_a3e5e85d8bde5ed4ffd0a743
source_units: [hatcher-2-2-degree-foundations]
declaration: theorem
origin: cited
---

# Degree is the multiplier of the ordered sphere class

For `0 < n` and `f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n`, define

```lean
noncomputable def Hatcher.Sphere.degree
    (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) : ℤ
```

by conjugating the induced endomorphism of ordinary integral homology through
the ordered orientation isomorphism and evaluating the resulting endomorphism
of `ℤ` at `1`.

The main result is the source-facing class equation

```lean
theorem Hatcher.Sphere.integralSphereFundamentalClass_map ... :
  integralSphereFundamentalClass n hn ≫ H.map f =
    AddCommGrpCat.asHom (degree n hn f) ≫
      integralSphereFundamentalClass n hn
```

together with the equivalent characterization of the conjugated
endomorphism. This fixes the sign convention used by every later node.

## Depends on

- [The ordered class orients ordinary sphere homology](integral-sphere-orientation.md)

## Sources

- [Hatcher §2.2, definition of degree, printed page 134](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
