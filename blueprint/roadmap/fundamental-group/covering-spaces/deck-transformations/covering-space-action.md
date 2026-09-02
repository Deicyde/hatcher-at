---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.IsCoveringSpaceAction.isQuotientCoveringMap_orbitQuotient
---

# Covering-space actions give quotient coverings

Assume `[Group G]`, `[MulAction G Y]`, `[TopologicalSpace Y]`, and
`[ContinuousConstSMul G Y]`. Define Hatcher's covering-space action condition
`Hatcher.IsCoveringSpaceAction G Y` by requiring that each `y : Y` have a
neighborhood `U` such that

`((g • ·) '' U ∩ U).Nonempty → g = 1`

for every `g : G`. Also record the equivalent pairwise-disjoint-translates
form used in Hatcher's condition `(*)`.

For the orbit projection

`q : Y → Quotient (MulAction.orbitRel G Y)`,

the main artifact is
`Hatcher.IsCoveringSpaceAction.isQuotientCoveringMap_orbitQuotient`, proving
`IsQuotientCoveringMap q G` directly from the pinned quotient-map API. The
same file should define the canonical homomorphism
`Hatcher.Covering.actionToDeck : G →* deck q`.

Also record Hatcher's preceding unnumbered observation: if `p : E → X` is a
covering map and `E` is path-connected, then the canonical action of `deck p`
on `E` is a covering-space action. Choose one covering sheet at a point; if two
of its deck translates meet, unique lifting forces the corresponding deck
transformations to be equal.

Do not replace this hypothesis with `ProperlyDiscontinuousSMul`: Mathlib's
class expresses finiteness of translates meeting pairs of compact sets, not
Hatcher's local pairwise-disjoint condition. The pinned theorem converting
that class to a quotient covering additionally assumes `LocallyCompactSpace`
and `T2Space`, which would strengthen this result. No connectedness,
Hausdorffness, or local compactness is needed for this node.

Formalized in `Hatcher/Covering/CoveringSpaceAction.lean`. The file also
defines `Hatcher.Covering.actionToDeck`, proves the pairwise-disjoint-translates
characterization, and shows that the deck action of a covering with
path-connected total space is a covering-space action.

## Depends on

- [Deck transformations and normal covers](deck-transformation-group.md)

## Proof depends on

- [A lift is determined by one point](../unique-lifting.md)

## Sources

- [Hatcher §1.3, condition (*) and Proposition 1.40 on page 72](../../../../sources/hatcher-1-3.md)
