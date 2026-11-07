# Local degree at a genuine suspension pole

Selected article: `af_5ead003fab03dbcaedbcd8d7`.
Revision: `6ca046581fb285d5ecbdebbd0a25345be1d0b9734864fa7151808bcfb0c69bc5`.
This is an uncompiled source candidate for root's remote CI and independent
review; this note asserts no formalization progress.

## Sole public target

`Hatcher.Sphere.sphere_suspension_pole_local_degree`, appended to the existing
`Hatcher/Sphere/DegreeLocalSum.lean`.

The theorem quantifies over every `n : ℕ`, arbitrary
`f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n`, and an actual point `p` of
the existing next sphere satisfying `p = northPole n ∨ p = southPole n`.
It derives `IsolatedPreimage (sphereSuspensionMap n f) p p` and proves

`localDegree (n + 1) (Nat.zero_lt_succ n) (sphereSuspensionMap n f) p p h =`
`  degree (n + 1) (Nat.zero_lt_succ n) (sphereSuspensionMap n f)`

for every isolation proof `h`. North and south specialize with `Or.inl rfl`
and `Or.inr rfl`. All quantities use the existing universe-zero standard
sphere and signed local/ordinary degree APIs. In particular, `n = 0` suspends
an actual `S⁰` map to `S¹`; positivity is used only for `n + 1`.

## Reached proof APIs

The actual `fiber` definition is exactly the preimage of the target singleton.
An explicit `change` exposes that formula. Case analysis on the pole equality
then uses the north or south component of
`sphere_suspension_pole_fibers n f`.

`singletonFiberIsolatedPreimage` derives isolation from this equation;
`localDegree_eq_degree_of_fiber_eq_singleton` applies in dimension `n + 1`
and gives the equality for the caller's arbitrary proof `h`. The singleton
comparison already derives finiteness and proves witness independence from
Proposition 2.30, so those proofs are reused through its public API.

No new helper, neighborhood choice, local-homeomorphism condition, orientation
or sign premise is introduced. The suspension-degree-preservation theorem is
outside this leaf's reached DAG and is unused here.

## Pre-edit context, source reading, and searches

The owned checkout starts at accepted shared source
`348f77920b042e6d5ba335087a0c436ce5a31e62`. Its refreshed work context matches
all seven root-frontier fields: statement phase, five dependencies, no blockers,
the selected revision, no open statements, no assumptions, and no revision
request. The full leaf, all five dependency articles, current Lean definitions,
cited source note/specification, and private original pole paragraph were read.
The prior private plan's proposed extra cone import became unnecessary after
degree-preservation integration.

The unchanged existing header already reaches the actual cone module through
`DegreeLocalSum → HomeomorphismLocalDegree → DegreeProperties → Homology →`
`ConeAttachmentDisk`. No header or import is edited.

Current immutable e64 CLI searches were run before the target was appended,
with every returned declaration statement read:

| Query | Matches |
| --- | ---: |
| `sphere_suspension_pole_local_degree` | 0 |
| `localDegree_eq_degree_of_fiber_eq_singleton` | 1 |
| `singletonFiberIsolatedPreimage` | 1 |
| `sphere_suspension_pole_fibers` | 1 |
| `suspension pole local degree` | 8 including grouping articles |

The sole helper article is already directly reached. `library list` was run
once for the current owned checkout; all nine packages are absent, so indexed
library coverage is unavailable. No package was fetched or indexed. Pinned
Mathlib remains `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1; the
previous checked successor-positivity API supplies `Nat.zero_lt_succ n`.

## Scope and uncompiled checks

All original DegreeLocalSum bytes, source SHA-256
`82ea5d0ab65d919beec6baf06fdab9cfed7902ecadd57f887f5033d16236cc1f`,
are preserved as an unchanged prefix. The sole source change is this public
theorem append, and the only other file is this selected implementation note.
The fresh audit retains the existing InvarianceOfDimension unscoped-limit
finding and unrelated pinch declaration-size advisory.

Remote CI must elaborate the explicit fiber conversion, universe-zero pole
specialization, and singleton comparison's successor-positivity argument.
No local Lean/Lake/REPL/LSP/probe/skeleton/test job was run.
