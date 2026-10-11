---
article_id: af_8413c196d3f1b253bf582afb
source_units: [hatcher-2-2-local-degree]
declaration: def
origin: bridged
---

# A finite sphere-map fiber has disjoint isolated neighborhoods

For `f : Sⁿ → Sⁿ`, `y : Sⁿ`, and a finite set-theoretic fiber
`f ⁻¹' {y}`, define the named subtype set `Hatcher.Sphere.fiber f y`, its
membership lemma, and a local-installation
`Hatcher.Sphere.finiteFiberFintype hfinite`; do not install a global instance
that hides the finiteness witness. Use
`Set.Finite.t2_separation` to choose an open neighborhood of every fiber point
so that the neighborhoods are pairwise disjoint.

The main artifact `Hatcher.Sphere.finiteFiberNeighborhoods f y hfinite`
packages these sets, their openness and center membership, pairwise
disjointness, and the resulting `LocalDegreeNeighborhood` at every fiber
point. Expose named projections for the sets, openness, center membership, and
pairwise disjointness. Also prove that their union is open, contains the entire
fiber, and is empty when the fiber is empty.

As neutral supporting data, define `Hatcher.Sphere.finiteFiberPairMap`, the
canonical map `(Sⁿ,Sⁿ-fiber f y) ⟶ (Sⁿ,Sⁿ-{y})` induced by `f`, and record its
ambient and subspace formulas. This definition is independent of the chosen
separated neighborhoods and of a finiteness proof.

The construction is noncomputable but its stated properties may not depend on
an enumeration or a decidable equality chosen by callers. It must also support
the empty fiber, with an empty family and empty union.

## Depends on

- [An isolated preimage gives a map of punctured pairs](isolated-preimage-neighborhood.md)

## Sources

- [Hatcher §2.2, disjoint neighborhoods of a finite fiber, printed pages 135–136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
