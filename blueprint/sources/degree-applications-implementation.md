# Degree-realization and suspension specification

This is a project-authored representation and decomposition contract, not a
statement from Hatcher or a record of completed Lean work. Its source boundary
is [Examples 2.31–2.32, Proposition 2.33, and the pole observation](hatcher-2-2-degree-applications.md).

## Models and coefficients

Keep the standard Euclidean n-sphere, its actual continuous maps, and the
existing signed integral global and neighborhood-independent local degrees.
The completed standard S¹-to-complex-circle homeomorphism fixes the power-map
model. No new orientation, abstract sphere proxy, or given-degree field is a
substitute for the existing quantities.

The new milestone has three shared comparisons, ten pinch-construction leaves,
nine circle-power leaves, and nine suspension/pole leaves. Each introduces
one main construction or theorem. Its dependency edges distinguish the
objects needed to state a result from the results used only in its proof.

## Pinch and fold

Construct disjoint embedded closed balls through stereographic projection,
with open interiors and an omitted axial point b. Identify the actual
complement-collapse quotient with the finite pointed wedge through one-point
compactifications. The empty family must give a one-point wedge and a
constant sphere map.

Component collapse maps have singleton regular fibers and are locally
homeomorphisms, so their degrees are proved units. Correct each sign by
identity or a coordinate reflection fixing b. Compute the signed fold's local
degrees through germ equality with these corrected component maps, then use
Proposition 2.30. Do not assume oriented chart degrees or merely postulate a
map whose degree equals the requested integer.

## Circle powers

Integer powers are continuous on the actual unit circle. Inversion is complex
conjugation and hence the corresponding standard coordinate reflection.
Positive fibers are the actual roots, not an abstract finite set introduced
with its cardinality as an assumption.

Use open centered angular charts. On |t| < π/(2k), deform the scale k to 1
by the positive factor (1−s)k+s. This fixes the central target and avoids it
elsewhere for every homotopy parameter. The common punctured-pair homotopy,
not an unsupported global argument map or same-map shrinking theorem, proves
local-degree invariance. Rotations have degree 1 by an actual homotopy to the
identity. Treat the zero exponent separately from the finite-fiber proof.

## Suspension

Use the genuine cone-base pair, retaining the existing cone endpoint
convention and proving its change to the source coordinate. Prove both the
good-pair witness and cone contractibility using the actual cone-to-disk
homeomorphism and open base retraction.

The cone self-map applies the original map to the sphere coordinate and
preserves height. Transport its actual quotient map through the fixed
sphere-suspension homeomorphism. The natural boundary isomorphism is the
specified good-pair quotient comparison followed by the pair connecting map;
its invertibility comes from the proved cone geometry.

The ordered-class conjugate of this boundary isomorphism is an automorphism
of ℤ. Its unit multiplier cancels in the naturality equation, so no unproved
sign equation is an extra hypothesis. The reduced comparison includes S⁰;
the ordinary degree endpoint keeps n > 0. Exact singleton pole fibers derive
isolation even for constant suspended maps, and the arbitrary local-degree
realization starts in sphere dimension two.

## Preservation and execution handoff

Preserve all existing declarations, formalization markers, source statements,
and the strict no-open-statements policy. The thirty-one continuation leaves
have durable IDs assigned by the migration tool. Germ invariance and the
singleton-fiber comparison are now complete; twenty-nine leaves remain unproved.
Lean-side API names and library findings belong in their hidden per-article
implementation notes. Formalize owns all proof execution after this DAG is
validated and committed. No source text or operational state belongs in the
mathematical vault.
