# Simplicial and singular homology

Hatcher §2.1 (pages 102–133). Mapped, not yet decomposed.

Simplicial homology takes a Δ-complex structure and forms the chain complex of
its simplices; it is finite and computable but depends on the chosen structure.
Singular homology takes all continuous maps `Δⁿ → X` as generators; it is
manifestly a homotopy-invariant functor but visibly enormous. The section
proves homotopy invariance of singular homology by a prism decomposition,
builds the long exact sequence of a pair, proves excision by barycentric
subdivision, and concludes that the two theories agree on Δ-complexes.

Mathlib has the singular chain complex, its homotopy invariance, and `H₀`
(`AlgebraicTopology/SingularHomology/`), plus simplicial machinery and the
Dold–Kan correspondence. The long exact sequence of a pair, relative homology,
excision, and the comparison with simplicial homology are absent. Excision is
the one that gates Chapter 2 and much of Chapter 3.

## Sources

- [Hatcher §2.1](../../../sources/hatcher.md)
