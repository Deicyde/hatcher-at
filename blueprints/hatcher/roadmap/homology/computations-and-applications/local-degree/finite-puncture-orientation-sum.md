---
article_id: af_6df77f1cf20ec9e15cb7abbd
source_units: [hatcher-2-2-local-degree]
declaration: theorem
origin: cited
---

# The finite-puncture class is the sum of the local classes

Use `Hatcher.Sphere.finitePunctureFundamentalClass` from the global-degree
fiber-square node; do not redefine the class.

The main theorem `Hatcher.Sphere.finitePunctureFundamentalClass_eq_sum` says
that this class is the image, under `finitePunctureHomologyIso`, of the finite
sum of the transported oriented local classes in the coproduct summands.

For each fiber point, prove first that projection to the pair punctured only
at that point sends the finite-puncture class to the ordered local class and
kills all other summands. Then use the finite biproduct extensionality
principle. This theorem is the formal version of Hatcher's equation
`j(1) = (1,…,1) = ∑ᵢ kᵢ(1)`.

## Depends on

- [The ordered sphere class orients local homology](sphere-local-orientation.md)
- [Finite-puncture projections have the diagonal matrix](finite-puncture-projection-matrix.md)
- [The finite-fiber pair map carries the global degree](global-degree-fiber-square.md)

## Sources

- [Hatcher §2.2, equation for the finite-puncture class in Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
