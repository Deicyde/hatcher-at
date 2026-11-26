# Homotopy groups

Hatcher §4.1 (pages 339–359). Mapped, not yet decomposed.

`πₙ(X, x₀)` is the set of homotopy classes of maps `(Sⁿ, s₀) → (X, x₀)`, a
group for `n ≥ 1` and abelian for `n ≥ 2`. The section establishes the basic
constructions, then proves Whitehead's theorem: a map between connected CW
complexes inducing isomorphisms on every `πₙ` is a homotopy equivalence. The
proof needs cellular approximation, that every map of CW complexes is homotopic
to one preserving skeleta, and the section closes with CW approximation,
replacing an arbitrary space by a weakly equivalent CW complex.

Mathlib has `HomotopyGroup` with its group structure. Whitehead's theorem,
cellular approximation, and CW approximation are absent, though Mathlib's model
category infrastructure provides an alternative framework in which some of
these are more naturally stated.

## Sources

- [Hatcher §4.1](../../../sources/hatcher.md)
