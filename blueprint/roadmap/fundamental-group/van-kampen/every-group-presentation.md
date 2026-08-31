---
declaration: theorem
origin: bridged
---

# Every group admits a generators-and-relations presentation

For every group `G`, produce a generator type, a family of relators in the free
group on those generators, and a multiplicative equivalence from the resulting
`PresentedGroup` to `G`.

Intended artifact: `Hatcher.exists_presentedGroup_equiv`.

Hatcher takes all elements of `G` as generators and a generating family for
the kernel of the evaluation map as relators. Mathlib supplies
`PresentedGroup`, but the required arbitrary-group equivalence is a theorem to
prove rather than an existing declaration.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2, proof of Corollary 1.28 on page 52](../../../sources/hatcher-1-2.md)
