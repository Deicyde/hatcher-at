# Covering spaces

Hatcher §1.3 (pages 56–82). Mapped, not yet decomposed.

A covering space `p : X̃ → X` lets loops in `X` be studied by lifting them, the
technique that computes `π₁(S¹)`. The section makes the technique structural.
The lifting criterion says a map `f : Y → X` lifts through `p` exactly when
`f∗π₁(Y)` lands inside `p∗π₁(X̃)`. The classification theorem then puts
connected covering spaces of a sufficiently nice `X` in bijection with
conjugacy classes of subgroups of `π₁(X)`, with the universal cover
corresponding to the trivial subgroup. Deck transformations realize the
normalizer, so a normal covering has deck group `π₁(X)/p∗π₁(X̃)`.

Mathlib has the lifting theorems in `Mathlib/Topology/Homotopy/Lifting.lean`
and `IsCoveringMap` in `Mathlib/Topology/Covering/`, but no lifting criterion in
terms of `π₁`, no classification, no universal cover construction, and no deck
transformation API. The semilocal simple connectedness hypothesis needed to
build the universal cover is also absent.

## Sources

- [Hatcher §1.3](../../../sources/hatcher.md)
