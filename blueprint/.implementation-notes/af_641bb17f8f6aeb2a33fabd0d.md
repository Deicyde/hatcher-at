# Global degree of a positive circle power

**Uncompiled source draft.** The proposed theorem is
`Hatcher.Sphere.circlePowerMap_positive_degree` in
`Hatcher/Sphere/DegreeLocalSum.lean`.

The proof chooses the standard target point and extracts the actual fiber's
equivalence with `Fin k` from `circlePowerMap_positive_fiber`. The membership
equivalence `mem_fiber` converts its equation subtype to the named set fiber
without changing the underlying sphere points. This derives finiteness and
cardinality rather than assuming either.

The temporary E-derived finite indexing instance is used only to prove
finiteness. The degree sum then uses the same `finiteFiberFintype hfinite`
instance that `degree_eq_sum_localDegree` installs in its proposition.
`circlePowerMap_positive_localDegree` supplies one for every canonical summand,
after its target is rewritten using actual fiber membership. The constant sum
is evaluated using `Fintype.card_congr E` and `Fintype.card_fin`.

Remaining elaboration checks concern the fiber subtype conversion, temporary
`Set.toFinite` instance synthesis, canonical Fintype alignment, dependent
isolation-witness target rewriting, and the final integer sum. No compilation,
axiom check, or independent proof review of this new theorem has been recorded.
