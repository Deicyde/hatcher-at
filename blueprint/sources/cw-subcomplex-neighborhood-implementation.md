# CW-subcomplex neighborhood implementation specification

This is a project-authored implementation specification for Hatcher's
Appendix Proposition A.5 and the intersection identity immediately following
it on printed page 523. It is not an independent mathematical source. The
construction supports Corollary 2.24 in the selected §2.1 post-excision
milestone.

## Mathematical scope

For a classical Mathlib CW complex `C` and a subcomplex `A`, construct one
canonical fixed-radius open regular neighborhood `N(A)` such that:

- the carrier of `A` is contained in `N(A)`;
- `N(A)` strongly deformation retracts onto `A`; and
- for subcomplexes `A` and `B`, `N(A) ∩ N(B) = N(A ∩ B)`.

This is the amount of Proposition A.5 needed for Hatcher's Corollary 2.24. It
does not attempt to expose every varying `εα` choice from the book.

## Representation

Use Mathlib's classical `CWComplex.Subcomplex` and its closed carrier. Add the
missing carrier intersection operation and prove that its cells are exactly
the cells common to both subcomplexes.

Fix the cellwise collar radius to `1/2`. In every cell outside `A`, define the
neighborhood portion by Hatcher's radial product collar of the cell boundary,
and define the deformation by sliding points outward along radial segments.
On cells belonging to `A`, the deformation is stationary. The cellwise maps
must agree on boundaries.

Prove continuity by the weak topology of the classical CW complex. If the
available closed-cell gluing lemmas do not directly cover the homotopy, isolate
the closed-cell-times-interval continuity statement as supporting material in
the same deformation-retraction review unit; do not hide it as an assumed
fact.

Package the result using `Hatcher.StrongDeformationRetract` for the canonical
subtype inclusion `A → N(A)`. The construction must work for the empty
subcomplex as well: its neighborhood is empty and the later relative-homology
argument still handles an empty intersection.

For ambient subcomplexes `A` and `B`, package `N(A)`, `N(B)`, and
`N(A ∩ B)` as the open cover consumed by binary-cover excision. The equality
of the intersection is part of this Appendix source unit, not an implementation
convenience to be weakened to an unspecified homotopy equivalence.

## Pinned boundary

The pinned Mathlib has classical and relative CW-complex structures,
subcomplex carriers, inherited CW instances, closed cells, skeletons, and weak
topology. It has no regular-neighborhood, subcomplex cofibration,
neighborhood-deformation-retract, or subcomplex-lattice API matching
Proposition A.5. The existing project files for compact subsets and classical
skeleton attachments are proof-engineering prior art, not exact coverage. No
leaf is `mathlib: true`.

## Fine decomposition

The Appendix source unit has five formalization leaves:

1. intersection of classical CW subcomplexes;
2. the radial collar and deformation on one closed cell;
3. the shared fixed-radius regular-neighborhood system and intersection law;
4. the global strong deformation retraction onto a subcomplex; and
5. the compatible neighborhood cover for two subcomplexes and their
   intersection.
