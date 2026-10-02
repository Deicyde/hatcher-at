---
article_id: af_0f89993a3608e24f605cc5a8
source_units: [hatcher-2-2-mv-transport-sphere-recurrence]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Sphere.reducedHomology_sphereSucc
---

# The reduced homology of spheres satisfies the suspension recurrence

Let `C` be an abelian category with `HasCoproducts.{w} C`, and let `R : C`.
For a sphere dimension `n`, the main packaged theorem
`Hatcher.Sphere.reducedHomology_sphereSucc R n` has the completion criterion

`(∀ i, Nonempty (H̃_{i+1}(TopCat.sphere (n+1);R) ≅`
`  H̃_i(TopCat.sphere n;R))) ∧`
`  IsZero (H̃_0(TopCat.sphere (n+1);R))`.

It keeps `n` and `i` separate and uses successor indices rather than truncated
subtraction.

Apply the reduced neighborhood Mayer–Vietoris sequence to the two
hemispheres. Contractibility makes the two middle summands zero, so exactness
makes the connecting morphism both mono and epi and hence an isomorphism. Use
the equator homeomorphism to identify the source-facing target with
`TopCat.sphere n`.

## Depends on

- [Reduced singular homology](../../simplicial-and-singular/relative-homology/reduced-singular-homology.md)

## Proof depends on

- [Reduced homology of a contractible space vanishes](contractible-space-reduced-homology.md)
- [The reduced neighborhood-retract Mayer–Vietoris sequence](reduced-neighborhood-mayer-vietoris.md)
- [Stereographic models for hemispheres and the equator](sphere-hemisphere-stereographic-models.md)
- [The hemispheres have compatible neighborhood deformation retractions](sphere-hemisphere-neighborhood-cover.md)

## Sources

- [Hatcher §2.2, Example 2.46, page 150](../../../../sources/hatcher-2-2.md)
- [Sphere-homology implementation specification](../../../../sources/sphere-homology-implementation.md)
