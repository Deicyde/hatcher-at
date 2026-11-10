# Finite-stage homology stability: source proposal

Status: complete uncompiled Lean source proposal. Statement/proof completion is unrecorded. Exact remote compilation, full public evidence, axioms/linters and independent review remain pending.

Public endpoint: `Hatcher.ClassicalCW.finiteStageHomologyStability`.

The map is the literal continuous subtype inclusion between the actual standard finite skeleta. Private identity and composition equations are proved pointwise on the same underlying X-points. Both canonical source and target alignment isomorphisms connect a standard one-step inclusion to the accepted literal step pair. The resulting actual homology map is obtained by functoriality and typed morphism equalities.

Upper-stage induction includes the identity case and composes actual preimages for surjectivity. The result is surjective when k≤n and IsIso when k<n. Ordinary H0, empty complexes, arbitrary cell families and unbounded ambient dimension are retained. The identity map is proved IsIso in every degree without using degree-window assumptions.

The coefficient object is explicitly lifted integers in the universe-u abelian-group category. The source calls only reached step/singular and pinned CW APIs; it does not use the vanishing, bounded-chain or cellular-complex siblings. The existing module body and imports are preserved. No supplied map, stability, homology or finite-cell certificate is added.

Pending compiler seams are the canonical set/cast alignment computations, typed composition and group-map coercions, and dependent upper-index induction. The complete source has no placeholders. No local Lean run has been used as verification evidence.
