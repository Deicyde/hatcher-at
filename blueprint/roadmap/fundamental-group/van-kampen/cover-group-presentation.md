---
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.relationSubgroup
---

# The group presentation associated to an open cover

Fix an indexed family of subsets `U i ⊆ X` containing a common basepoint
`x₀`. Let `G i = π₁(U i, x₀)` and let
`P = Monoid.CoprodI G` be their indexed free product. The inclusions
`U i ↪ X` induce a canonical homomorphism

`Φ : P →* π₁(X, x₀)`.

For each pair `i,j` and each loop class `ω` in `U i ∩ U j`, the two inclusion
maps give elements of `G i` and `G j`. Define the overlap relation

`of_i(ω in U i) * of_j(ω in U j)⁻¹`

in `P`, and let `N` be the normal closure of all such relations. The main
artifact is `Hatcher.VanKampen.relationSubgroup`; the same file should define
the supporting map `Hatcher.VanKampen.coverMap`.

This is the algebraic object occurring in Hatcher's Theorem 1.20. The general
cover cannot be represented by `Monoid.PushoutI`, which has only one common
amalgamating group.

Formalized in `Hatcher/VanKampen/CoverGroupPresentation.lean`. The same file
exports `Hatcher.VanKampen.coverMap`, the two overlap homomorphisms, and the
explicit overlap relators before taking their normal closure.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2, free products and Theorem 1.20](../../../sources/hatcher-1-2.md)
