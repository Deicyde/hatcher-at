## README.md

### The kernel calculation

Draft Mathlib PR
[#41603](https://github.com/leanprover-community/mathlib4/pull/41603)
proves a broader groupoid/cosheaf theorem and is useful implementation prior
art. It is generated, unreviewed, absent from the pinned revision, and not
treated as Mathlib coverage here.

### Wedges and cell complexes

Mathlib supplies the abstract coproduct-and-pushout data in
`HomotopicalAlgebra.AttachCells`. This project now compares that data with an
explicit indexed cone quotient and formalizes Hatcher's strip-enlarged space,
binary cover, deformation retractions, and overlap cover. Together with the
binary-cover algebra, these interfaces prove both the 2-cell and higher-cell
clauses of Proposition 1.26. These are local formalizations, not existing
Mathlib coverage.

The 2-skeleton argument uses Mathlib's classical CW-complex API, while the
attachment theorem uses its categorical API. The bridge between them is
supplied by a bounded [Appendix support chain](../../appendix/classical-cw-bridge/README.md):
it compares the two cell shapes, proves the successor-skeleton quotient, and
packages the inclusion as `AttachCells`. Separate connectivity and
finite-stage nodes discharge the path-connectedness hypotheses needed during
the induction rather than assuming them silently.

The presentation-complex branch is complete. Its support roadmap separates the
formalized pointed-wedge mapping and connectivity interfaces, zero- and
one-cell models, arbitrary relator family, quotient calculation, and finite
CW-sequence assembly. The cyclic quotient calculation and concrete
single-two-cell example are formalized as well.
