---
declaration: theorem
origin: bridged
not_ready: true
---

# Classical skeleton inclusions are abstract cell attachments

For a classical Mathlib CW complex, present the inclusion from one skeleton to
the next as an instance of the categorical cell-attachment construction
`HomotopicalAlgebra.AttachCells` for `TopCat.RelativeCWComplex.basicCell`.
The cells and attaching maps must be obtained from the classical
`Topology.CWComplex` characteristic maps.

Intended artifact: `Hatcher.classicalSkeletonInclusion_relativeCWComplex`.

This is the bridge needed to apply the abstract attachment theorem to the
classical `CWComplex.skeleton` used by Hatcher's Proposition 1.26(c) and
Appendix Proposition A.1. Mathlib documents the equivalence of its abstract and
classical CW-complex definitions as a TODO and currently provides no bridge.
The node remains not ready until the exact categorical pushout comparison is
specified.

The precise missing result is an `IsPushout` theorem for the coproduct square
of the classical characteristic maps. The current API provides only the set
identity describing the next skeleton and the weak-topology closed-set axiom.
There is also no packaged arrow isomorphism between the classical sup-norm
ball/sphere inclusion and the abstract `basicCell`, which uses an `ULift`ed
Euclidean space with its L2 norm. Both pieces are prerequisites for an
`AttachCells` bridge.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2 and Appendix prerequisite](../../sources/hatcher-1-2.md)
- [Mathlib abstract CW-complex implementation notes](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Topology/CWComplex/Abstract/Basic.lean)
