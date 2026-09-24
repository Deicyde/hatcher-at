---
article_id: af_b46833ba0dee42bdf8a7f504
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.exists_presentedGroup_equiv
---

# Every group admits a generators-and-relations presentation

For every group `G`, produce a generator type, a family of relators in the free
group on those generators, and a multiplicative equivalence from the resulting
`PresentedGroup` to `G`.

Formalized as `Hatcher.exists_presentedGroup_equiv` in
`Hatcher/VanKampen/PresentedGroup.lean`. The theorem chooses `G` itself as the
generator type and the kernel of free-group evaluation as the relator set.

Hatcher takes all elements of `G` as generators and a generating family for
the kernel of the evaluation map as relators. Mathlib supplies
`PresentedGroup`, but the required arbitrary-group equivalence is a theorem to
prove rather than an existing declaration.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2, proof of Corollary 1.28 on page 52](../../../sources/hatcher-1-2.md)
