---
declaration: theorem
origin: bridged
mathlib: true
mathlib_declaration: Convex.contractibleSpace
mathlib_file: Mathlib/Analysis/Convex/Contractible.lean
---

# Convex sets have trivial fundamental group

**Hatcher, Example 1.4 (page 27).** A nonempty convex subset of `ℝⁿ` has
trivial fundamental group.

The pinned protected theorem `Convex.contractibleSpace` says that a nonempty
convex set in a real topological vector space is a `ContractibleSpace`.
Mathlib's instance `SimplyConnectedSpace.ofContractible` then makes it simply
connected, and the `Subsingleton (FundamentalGroup X x)` instance in
`Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean` makes
every based loop class equal to the identity.

The frontmatter tracks the exact contractibility theorem. Pinned Mathlib has no
single named declaration whose statement is Hatcher's final group-theoretic
sentence; the result is the checked composition of these declarations and
instances.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [Simply connected spaces have unique path-homotopy classes](simply-connected-unique-path-classes.md)

## Sources

- [Hatcher §1.1, Example 1.4, page 27](../../../sources/hatcher-1-1.md)
