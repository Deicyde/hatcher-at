# The cone over a sphere forms a contractible good pair

Uncompiled checks for `Hatcher.Sphere.sphere_cone_geometry` and its supporting
constructions in `Hatcher.VanKampen.ConeAttachmentDisk`:

- Confirm that the closed disk-boundary inclusion's `ULift` expression is
  definitionally the standard `TopCat.diskBoundaryInclusion (n + 1)`.
- Confirm that `goodPairNeighborhoodInclusion` for the chosen `lowerCover id`
  is definitionally `lowerBaseInclusion (ContinuousMap.id _)`.
- Check the `n = 0` specialization: the actual sphere is the boundary of the
  one-dimensional disk, and the nonemptiness proof uses `Fin (n + 1)`.
- Check the public theorem's axioms and unused arguments after compilation.

The candidate has not been compiled or reviewed. The associated roadmap
article retains its original assertions.
