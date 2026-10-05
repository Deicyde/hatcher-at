---
article_id: af_973242ed62dcdeb1142aae93
source_units: [hatcher-2-2-degree-foundations]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Sphere.doubleSimplexSwap_isoSphere
---

# Coordinate sign changes on the sphere

Construct a sphere homeomorphism that changes the signs of an arbitrary
finite set of coordinates. Define the one-coordinate reflections and the
all-coordinate antipodal homeomorphism as special cases, with composition
formulas for disjoint or symmetric-difference sign sets.

For the final coordinate, prove that the sign change fixes the equator,
exchanges the two closed hemispheres, and corresponds under
`Hatcher.Simplex.doubleSimplexIsoSphere` to the double-simplex swap. The main
compatibility result is

```lean
theorem Hatcher.Sphere.doubleSimplexSwap_isoSphere ... :
  (Hatcher.Simplex.doubleSimplexSwapIso n).hom ≫
      (Hatcher.Simplex.doubleSimplexIsoSphere n).hom =
    (Hatcher.Simplex.doubleSimplexIsoSphere n).hom ≫
      (coordinateReflectionIso n (Fin.last n)).hom
```

Formalized in `Hatcher/Sphere/CoordinateSignChanges.lean` and
`Hatcher/Singular/DoubleSimplexSphere.lean`. Coordinate sign changes are
restrictions of a coordinatewise linear isometry of Euclidean space, so their
homeomorphism, composition, reflection, and antipodal laws share one model.
The last-coordinate calculation is performed on the two explicit hemisphere
parametrizations defining `doubleSimplexIsoSphere`, which proves the displayed
compatibility as an equality of the actual `TopCat` morphisms.

## Depends on

- [Swapping the double simplex negates its fundamental class](double-simplex-swap-class.md)
- [The double simplex is a sphere](../post-excision-applications/double-simplex-sphere-homeomorphism.md)

## Sources

- [Hatcher §2.2, coordinate reflections in properties (e)–(f), printed page 134](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
