---
article_id: af_1c27eabf2c01f79d636b09ff
source_units: [hatcher-2-2-degree-foundations]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Sphere.puncturedSphereHomeomorphEuclidean
---

# A punctured sphere is Euclidean space

For every `p : TopCat.sphere.{0} n`, construct a stereographic homeomorphism

```lean
noncomputable def Hatcher.Sphere.puncturedSphereHomeomorphEuclidean
    (n : ℕ) (p : TopCat.sphere.{0} n) :
    ({p}ᶜ : Set (TopCat.sphere.{0} n)) ≃ₜ EuclideanSpace ℝ (Fin n)
```

and publish the resulting contractibility of the punctured sphere. Reuse
Mathlib's `stereographic'` and the project's existing sphere chart
conventions; do not create a competing public sphere model.

The construction
uses the existing `sphereULiftHomeomorph` once, restricts it to the complements
of the selected point and its raw-sphere image, and then applies Mathlib's
stereographic chart. The public `puncturedSphereContractibleSpace` instance is
transported across this exact homeomorphism.

## Depends on

None.

## Proof depends on

- [Stereographic models for hemispheres and the equator](../sphere-homology/sphere-hemisphere-stereographic-models.md)

## Sources

- [Hatcher §2.2, proof of degree property (b), printed page 134](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
