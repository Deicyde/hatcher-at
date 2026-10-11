---
article_id: af_01985c349aff3cf79987cf88
source_units: [hatcher-2-2-local-degree]
declaration: theorem
origin: bridged
---

# The finite-fiber pair map carries the global degree

Define `Hatcher.Sphere.finitePunctureFundamentalClass n f y` from `ℤ` to the
degree-`n` relative homology of `(Sⁿ,Sⁿ-fiber f y)` as the ordered reduced
sphere class followed by `reducedPairProjection`. This definition needs
neither a positivity nor a finiteness witness. The finite-fiber pair map
induced by `f` takes this class to the global-degree multiple of the target
local class.

The main theorem `Hatcher.Sphere.finiteFiberFundamentalClass_map` identifies
the multiplier exactly:

`finitePunctureFundamentalClass ≫ H.map finiteFiberPairMap =`
`  AddCommGrpCat.asHom (degree n hn f) ≫`
`    integralSphereLocalFundamentalClass n hn y`.

Prove the square by naturality of `reducedPairProjection` and the completed
positive-degree comparison between reduced and ordinary homology, using the
morphism-level equation `finiteFiberPairMap_fst = f`. The theorem itself needs
no fiber-finiteness hypothesis. The sign must therefore be the ordered global
degree, not merely some integer with the same absolute value.

## Depends on

- [The ordered sphere class orients local homology](sphere-local-orientation.md)
- [A finite sphere-map fiber has disjoint isolated neighborhoods](finite-fiber-neighborhoods.md)
- [Degree is the multiplier of the ordered sphere class](../degree/sphere-degree-definition.md)

## Sources

- [Hatcher §2.2, lower square in Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
