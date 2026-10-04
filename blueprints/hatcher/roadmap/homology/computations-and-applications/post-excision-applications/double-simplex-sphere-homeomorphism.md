---
article_id: af_4da2fc5b7cd04ae7b7ed5f40
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: bridged
---

# The double simplex is a sphere

Construct a homeomorphism

`Hatcher.Simplex.doubleSimplex n ≅ TopCat.sphere n`.

The main artifact is `Hatcher.Simplex.doubleSimplexIsoSphere`. First carry
each standard simplex to a closed disk by the simplex-pair homeomorphism, then
identify the double of the disk along its boundary with the standard unit
sphere. The two disk maps must agree on the common boundary so that the
homeomorphism descends from the pushout.

Transport the double-simplex fundamental class across this homeomorphism and
record that the transported class morphism is an isomorphism. Keep the
ordered double-simplex class as the source-facing orientation datum: the
existing sphere calculation returns only a nonempty type of isomorphisms and
does not identify Hatcher's named cycle.

## Depends on

- [The standard simplex pair is homeomorphic to the disk pair](standard-simplex-disk-pair-homeomorphism.md)
- [The ordered difference of the two simplices is a cycle](double-simplex-fundamental-cycle.md)
- [The double-simplex difference generates reduced homology](double-simplex-fundamental-class.md)

## Sources

- [Hatcher §2.1, two-simplex model of the sphere in Example 2.23, printed page 125](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)
