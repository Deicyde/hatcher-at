## README.md

### Lifting and monodromy

Proposition 1.30 is a source-facing wrapper around Mathlib's existing lifted
homotopy and its uniqueness characterization.

The based monodromy action is now supplied by Mathlib. The next local nodes
identify the induced subgroup and derive Hatcher's sheet-index calculation.
The primary statement for Proposition 1.32 is a fiber-to-coset equivalence,
since Mathlib's natural-number subgroup index encodes infinite index as zero.

The lifting criterion already exists in its difficult direction; the local
node supplies Hatcher's exact equivalence. Proposition 1.34 is an exact pinned
declaration.

### The path-class universal cover

Open Mathlib PR
[#38292](https://github.com/leanprover-community/mathlib4/pull/38292)
contains implementation prior art for based paths and universal covers, but its
compact-open quotient topology is not silently mixed with the direct basis.

### Subgroups and classification

The classification is phrased through a small project-local bundle of pointed
connected covers. Realization and rigidity do not need a category of all
objects over `X`. The formalized classification uses a fixed-universe quotient
of covers by isomorphism, while a separate cross-universe theorem identifies
every pointed connected cover with its canonical subgroup-cover representative.

### Deferred within §1.3

Mathlib PR #40135 is the historical
source of the basic deck-group API now included in v4.34.1; the normalizer,
normal-cover, and quotient-action consequences in this roadmap remain local.
