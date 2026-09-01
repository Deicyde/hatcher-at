# Covering spaces

Hatcher §1.3 (pages 56–82). The selected slice follows the classification and
deck-transformation spine from lifting properties through Proposition 1.40.
Permutation reconstruction and geometric examples remain deferred.

The pinned Mathlib already contains most of the hard lifting theory. The
roadmap separates exact upstream declarations from the thin source-facing
wrappers Hatcher's statements require. Universal covers and the classification
itself are absent from the pin.

## Lifting and monodromy

Proposition 1.30 is a source-facing wrapper around Mathlib's existing lifted
homotopy and its uniqueness characterization.

- [Homotopies lift uniquely through a covering map](homotopy-lifting.md)

The next nodes package the based monodromy action, identify the induced
subgroup, and derive Hatcher's sheet-index calculation. The primary statement
for Proposition 1.32 is a fiber-to-coset equivalence, since Mathlib's
natural-number subgroup index encodes infinite index as zero.

- [The fundamental group acts on a covering fiber](monodromy-action.md)
- [Covering maps inject path-homotopy classes](covering-injective-path-classes.md)
- [The induced subgroup consists of loops with closed lifts](closed-lift-image.md)
- [Sheets are cosets of the induced subgroup](sheet-index.md)

The lifting criterion already exists in its difficult direction; the local
node supplies Hatcher's exact equivalence. Proposition 1.34 is an exact pinned
declaration.

- [A map lifts exactly when its fundamental group lands in the covering subgroup](lifting-criterion.md)
- [A lift is determined by one point](unique-lifting.md)
- [Local path-connectedness ascends along a covering](locally-path-connected-total-space.md)

## The path-class universal cover

Hatcher's construction needs a local nullhomotopy condition, a basis of small
path-connected opens, and topology on endpoint-preserving path classes. This
roadmap uses Hatcher's `U[γ]` basis directly. Open Mathlib PR
[#38292](https://github.com/leanprover-community/mathlib4/pull/38292)
contains implementation prior art for based paths and universal covers, but its
compact-open quotient topology is not silently mixed with the direct basis.

- [The path-class universal cover](universal-cover/README.md)
- [Semilocally simply-connected spaces](universal-cover/semilocally-simply-connected.md)
- [Small nullhomotopy neighborhoods form a basis](universal-cover/nullhomotopic-open-basis.md)
- [The path-class universal-cover space](universal-cover/universal-cover-path-space.md)
- [The universal-cover basic sets form a basis](universal-cover/universal-cover-basis.md)
- [The endpoint map is a covering](universal-cover/universal-cover-is-covering.md)
- [The path-class cover is path-connected](universal-cover/universal-cover-path-connected.md)
- [The path-class cover is simply-connected](universal-cover/universal-cover-simply-connected.md)

## Subgroups and classification

For a subgroup `H ≤ π₁(X,x₀)`, quotient the path-class cover by Hatcher's
same-endpoint relation and calculate the image subgroup. This is Proposition
1.36.

- [The covering space associated to a subgroup](subgroup-cover-space.md)
- [The subgroup projection is a path-connected covering](subgroup-cover-is-covering.md)
- [The subgroup cover realizes the chosen subgroup](subgroup-cover-image.md)

The classification is phrased through a small project-local bundle of pointed
connected covers. Realization and rigidity do not need a category of all
objects over `X`. The literal quotient of covers by isomorphism is marked not
ready until its universe boundary is fixed.

- [Pointed connected covering spaces](based-connected-cover.md)
- [Equal image subgroups characterize pointed cover isomorphism](pointed-cover-rigidity.md)
- [Pointed connected covers are classified by subgroups](pointed-cover-classification.md)
- [Changing the lifted basepoint conjugates the image subgroup](cover-basepoint-conjugacy.md)
- [Connected covers are classified by conjugacy classes](unpointed-cover-classification.md)
- [A simply-connected cover maps uniquely to every pointed connected cover](universal-cover-initial.md)

## Deck transformations and quotient actions

Proposition 1.39 turns the induced subgroup into a deck-group calculation.
The normalizer acts on the cover, its kernel is the covering subgroup, and
normal covers are exactly those whose image subgroup is normal. Proposition
1.40 applies this to orbit quotients satisfying Hatcher's exact local-disjoint
condition.

- [Deck transformations and quotient actions](deck-transformations/README.md)
- [Deck transformations and normal covers](deck-transformations/deck-transformation-group.md)
- [A deck transformation is determined by one lifted point](deck-transformations/deck-realization.md)
- [The normalizer acts by deck transformations](deck-transformations/normalizer-to-deck.md)
- [The normalizer map is surjective with kernel the covering subgroup](deck-transformations/normalizer-to-deck-exactness.md)
- [The deck group is the normalizer quotient](deck-transformations/deck-group-calculation.md)
- [Covering-space actions give quotient coverings](deck-transformations/covering-space-action.md)
- [Orbit quotients are normal and have the expected deck group](deck-transformations/orbit-quotient-deck-group.md)
- [The orbit-quotient fundamental group recovers the acting group](deck-transformations/orbit-quotient-fundamental-group.md)

## Deferred within §1.3

Example 1.35, the reconstruction of arbitrary covers from permutation actions,
and Examples 1.41–1.48 are deferred. Code from post-pin Mathlib PR #40135
supplies useful deck-group prior art, but it is not part of this build.

## Sources

- [Hatcher §1.3](../../../sources/hatcher-1-3.md)
