---
article_id: af_11fc9a48da227190dd7e1eeb
source_units: [hatcher-2-2-local-degree]
declaration: def
origin: cited
---

# Finite-puncture homology is the coproduct of the local groups

Compose the relative-homology sigma-pair isomorphism with the homology
isomorphism induced by `finitePuncturePairHom`. The main artifact
`Hatcher.Sphere.finitePunctureHomologyIso` has type

`∐ x : fiber f y, H_n(U_x, U_x - {x}; ℤ)`
`  ≅ H_n(Sⁿ, Sⁿ - fiber f y; ℤ)`.

Prove the exact component formula: the `x`th coproduct injection followed by
the forward isomorphism is the homology map induced by inclusion of the `x`th
local punctured pair into the finite-puncture pair. Also expose the inverse
component maps used to test equality of morphisms into the finite coproduct.

## Depends on

- [Relative homology commutes with coproducts of arbitrary pairs](relative-homology-sigma-pair.md)
- [The disjoint local pairs excise to the finite-puncture pair](finite-puncture-pair-excision.md)

## Sources

- [Hatcher §2.2, direct-sum identification in Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
