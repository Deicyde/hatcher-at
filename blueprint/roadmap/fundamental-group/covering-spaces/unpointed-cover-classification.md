---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.ConnectedCover.classificationEquivConjClasses
---

# Connected covers are classified by conjugacy classes

**Hatcher, Theorem 1.38, unbased clause (pages 67–68).** For a
path-connected, locally path-connected, semilocally simply-connected `X`,
isomorphism classes of path-connected covers of `X` correspond bijectively to
conjugacy classes of subgroups of `π₁(X,x₀)`.

Intended artifact: `Hatcher.ConnectedCover.classificationEquivConjClasses`.

Formalized in `Hatcher/Covering/UnpointedCoverClassification.lean`. The
classification uses the quotient of connected covers whose total spaces live
in the same universe as `X`, and the quotient of subgroups by Mathlib's
conjugation-orbit relation. Changing the chosen point over `x₀` changes the
image subgroup only by conjugacy, so the resulting class is independent of
that choice.

As in the pointed classification, fixing the universe avoids a size mismatch
between the type of all covers and the subgroup type. The cross-universe
theorem `Hatcher.ConnectedCover.isomorphic_ofSubgroup_chosenRange` shows that
every connected cover in any universe is isomorphic to a canonical subgroup
cover in the fixed universe.

## Depends on

- [Pointed connected covering spaces](based-connected-cover.md)
- [Semilocally simply-connected spaces](universal-cover/semilocally-simply-connected.md)

## Proof depends on

- [Changing the lifted basepoint conjugates the image subgroup](cover-basepoint-conjugacy.md)
- [Pointed connected covers are classified by subgroups](pointed-cover-classification.md)

## Sources

- [Hatcher §1.3, Theorem 1.38, unbased clause](../../../sources/hatcher-1-3.md)
