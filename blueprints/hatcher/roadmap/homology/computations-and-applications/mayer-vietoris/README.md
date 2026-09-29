---
article_id: af_83c72696eec342f329b6802b
---

# Mayer–Vietoris sequences

Hatcher §2.2, printed pages 149–150. This milestone constructs the ordinary
and reduced Mayer–Vietoris sequences for two subspaces whose interiors cover
the ambient space. It uses the already formalized small-chain equivalence from
Proposition 2.21, so the chain complex of chains supported in one cover member
can replace the full singular chain complex.

The source fixes the signs: the intersection map is `x ↦ (x,-x)`, the union
map is `(x,y) ↦ x+y`, and the connecting map sends a small cycle represented
as `x+y` to the class of `∂x=-∂y`. The reduced version comes from augmenting
the same short exact sequence.

## Ordinary sequence

- [The binary-cover Mayer–Vietoris chain complex](binary-cover-chain-complex.md)
- [Binary-cover chains form a short exact sequence](binary-cover-chain-short-exact-sequence.md)
- [The binary-cover Mayer–Vietoris sequence](binary-cover-mayer-vietoris-sequence.md)

## Reduced sequence

- [Small augmented chains include by a chain-homotopy equivalence](small-augmented-chain-inclusion-homotopy-equivalence.md)
- [Augmented binary-cover chains form a short exact sequence](augmented-binary-cover-chain-short-exact-sequence.md)
- [The reduced binary-cover Mayer–Vietoris sequence](reduced-binary-cover-mayer-vietoris-sequence.md)

## Boundary

This milestone ends with exact ordinary and reduced binary interior-cover
sequences. It excludes the neighborhood-retract extension, the sphere and
Klein-bottle examples, naturality for a new category of cover maps, degree,
and cellular homology.

## Sources

- [Hatcher §2.2, Mayer–Vietoris, pages 149–150](../../../../sources/hatcher-2-2.md)
- [Mayer–Vietoris implementation specification](../../../../sources/mayer-vietoris-implementation.md)
