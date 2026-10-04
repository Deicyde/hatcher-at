---
article_id: af_1174b6b1a3e283fe5bfe011c
source_units: [hatcher-2-1-post-excision-applications]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Euclidean.localHomology
---

# Local homology of positive-dimensional Euclidean space

Let `d : ℕ`, let
`E := EuclideanSpace ℝ (Fin (d + 1))`, and let `x : E`. For every coefficient
object `R` in the supported abelian target category, prove

`Nonempty (H_(d+1)(E, E \ {x};R) ≅ R)`

and prove that `H_i(E,E \ {x};R)` is a zero object whenever `i ≠ d + 1`.
The main result is `Hatcher.Euclidean.localHomology` with an integral
specialization matching Hatcher's displayed groups.

Translate `x` to the origin, use the radial strong deformation retraction of
punctured Euclidean space onto `S^d`, and combine the sphere calculation with
the contractible-ambient relative comparison. The theorem is intentionally
indexed by `d + 1`; dimension zero belongs to the final point-set split and is
not represented by a nonexistent negative sphere.

## Depends on

None beyond the Euclidean-space and relative-homology objects named above.

## Proof depends on

- [Relative homology in a contractible ambient space](contractible-ambient-relative-homology.md)
- [A sphere strongly deformation retracts from punctured Euclidean space](../sphere-homology/punctured-space-radial-deformation-retract.md)
- [A homotopy equivalence induces reduced-homology isomorphisms](../sphere-homology/homotopy-equivalence-reduced-homology-iso.md)
- [Reduced homology of spheres](../sphere-homology/sphere-reduced-homology.md)

## Sources

- [Hatcher §2.1, proof of Theorem 2.26, page 126](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)
