---
article_id: af_11fc9a48da227190dd7e1eeb
source_units: [hatcher-2-2-local-degree]
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Sphere.finitePunctureHomologyIso
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

Define `Hatcher.Sphere.finitePunctureHomologyIso D hfinite k` by composing
`relativeIntegralHomologySigmaPairIso` for the named local-pair family with the
isomorphism induced by `finitePuncturePairHom D`. Name the reassociated
component theorem
`Hatcher.Sphere.ι_finitePunctureHomologyIso_hom`.

Expose
`Hatcher.Sphere.finitePunctureHomologyProjection D hfinite k i` as the inverse
isomorphism followed by the `i`th finite-biproduct projection, together with a
hom-ext theorem for maps into finite-puncture homology. Install all `Fintype`,
`DecidableEq`, and finite-biproduct instances internally from `hfinite`; none
belongs in a public signature. The construction works in every degree and for
an empty fiber without branching.

## Depends on

- [Relative homology commutes with coproducts of arbitrary pairs](relative-homology-sigma-pair.md)
- [The disjoint local pairs excise to the finite-puncture pair](finite-puncture-pair-excision.md)

## Sources

- [Hatcher §2.2, direct-sum identification in Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
