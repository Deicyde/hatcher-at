---
article_id: af_dabd641d4db49f64a116b034
---

# Mayer–Vietoris transport and sphere homology

Hatcher §2.1, printed pages 109–114, and §2.2, printed page 150. This
milestone transports the completed Mayer–Vietoris sequences across supplied
neighborhood deformation retractions, applies the reduced sequence to the
northern and southern hemispheres, and derives the reduced homology of every
sphere.

The public result uses Mathlib's `TopCat.sphere` and remains general in the
coefficient object. Hatcher's integral Corollary 2.14 is an explicit
specialization. The recurrence follows Example 2.46 rather than the deferred
good-pair quotient proof that originally precedes Corollary 2.14.

## Reduced homotopy invariance

- [Homotopic maps induce the same reduced-homology map](reduced-homology-homotopy-invariance.md)
- [A homotopy equivalence induces reduced-homology isomorphisms](homotopy-equivalence-reduced-homology-iso.md)
- [Reduced homology of a contractible space vanishes](contractible-space-reduced-homology.md)

## Neighborhood transport

- [The ordinary neighborhood-retract Mayer–Vietoris sequence](ordinary-neighborhood-mayer-vietoris.md)
- [The reduced neighborhood-retract Mayer–Vietoris sequence](reduced-neighborhood-mayer-vietoris.md)

## Hemisphere geometry

- [A closed ball strongly deformation retracts from Euclidean space](closed-ball-radial-deformation-retract.md)
- [A sphere strongly deformation retracts from punctured Euclidean space](punctured-space-radial-deformation-retract.md)
- [Stereographic models for hemispheres and the equator](sphere-hemisphere-stereographic-models.md)
- [The hemispheres have compatible neighborhood deformation retractions](sphere-hemisphere-neighborhood-cover.md)

## Sphere calculation

- [The reduced homology of spheres satisfies the suspension recurrence](sphere-reduced-homology-recurrence.md)
- [The zero-sphere is a two-point space](zero-sphere-two-point-homeomorphism.md)
- [Reduced homology of the zero-sphere](zero-sphere-reduced-homology.md)
- [Reduced homology of spheres](sphere-reduced-homology.md)

## Boundary

This milestone assumes the neighborhoods and deformation retractions in the
general transport theorem, and constructs only the sphere-specific witnesses
needed for Example 2.46. It excludes Hatcher's general CW-subcomplex
`Nε(A)` construction, Theorem 2.13 and Proposition 2.22, Corollary 2.15,
degree and orientation theory, cellular homology, Examples 2.47–2.48, mapping
tori, relative Mayer–Vietoris, and coefficients as a separate source topic.

## Sources

- [Hatcher §2.1 source note](../../../../sources/hatcher-2-1.md)
- [Hatcher §2.2 source note](../../../../sources/hatcher-2-2.md)
- [Sphere-homology implementation specification](../../../../sources/sphere-homology-implementation.md)
