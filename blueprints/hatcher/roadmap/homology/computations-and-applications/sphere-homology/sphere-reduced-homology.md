---
article_id: af_fc6563b922b5d53422e79281
source_units: [hatcher-2-1-sphere-homology, hatcher-2-2-mv-transport-sphere-recurrence]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Sphere.reducedHomology_sphere
---

# Reduced homology of spheres

Let `C` be an abelian category with `HasCoproducts.{w} C`, and let `R : C`.
For every sphere dimension `n`, the main theorem
`Hatcher.Sphere.reducedHomology_sphere R n` has the completion criterion

`Nonempty (H̃_n(TopCat.sphere n;R) ≅ R) ∧`
`  ∀ i, i ≠ n → IsZero (H̃_i(TopCat.sphere n;R))`.

Induct on the sphere dimension using the successor recurrence and the direct
`S⁰` calculation. Return the diagonal isomorphism under `Nonempty` rather than
choosing an orientation. Include
`Hatcher.Sphere.reducedHomology_sphere_int` as the explicit specialization to
`AddCommGrpCat.of ℤ` matching Hatcher's Corollary 2.14.

## Depends on

- [Reduced singular homology](../../simplicial-and-singular/relative-homology/reduced-singular-homology.md)

## Proof depends on

- [The reduced homology of spheres satisfies the suspension recurrence](sphere-reduced-homology-recurrence.md)
- [Reduced homology of the zero-sphere](zero-sphere-reduced-homology.md)

## Sources

- [Hatcher §2.1, Corollary 2.14, page 114](../../../../sources/hatcher-2-1.md)
- [Hatcher §2.2, alternative proof in Example 2.46, page 150](../../../../sources/hatcher-2-2.md)
- [Sphere-homology implementation specification](../../../../sources/sphere-homology-implementation.md)
