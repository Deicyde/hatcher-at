---
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: bridged
---

# The zero face identifies the two simplex point quotients

Show that the square formed by the boundary of the zero face, the zero face,
the zero horn, and the full boundary is a pushout in `TopCat`:

`∂Δ[n] → Δ[n]`

`↓          ↓`

`Λ⁰[n+1] → ∂Δ[n+1]`.

Use pushout pasting to construct the resulting isomorphism between point
quotients. The main artifact is
`Hatcher.Simplex.zeroFacePointQuotientIso`. Its forward map must be the
functorial `pointQuotientMap` induced by the canonical zero-face morphism of
pairs.

The proof uses the finite closed-cover gluing property of the face and horn;
it must not appeal to the later simplicial-versus-singular comparison.

## Depends on

- [The boundary and zero horn of a standard topological simplex](standard-simplex-boundary-horn.md)
- [Functorial point quotients of topological pairs](../good-pair-quotient/point-quotient-functor.md)

## Sources

- [Hatcher §2.1, quotient-space comparison in Example 2.23, printed page 125](../../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../../sources/post-excision-applications-implementation.md)
