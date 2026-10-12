---
article_id: af_2420d65a757f7dd87b503542
source_units: [hatcher-2-2-local-degree]
declaration: theorem
origin: cited
---

# Finite-puncture projections have the diagonal matrix

For a fiber point `x`, inclusion of complements defines Hatcher's projection

`p_x : H_n(Sⁿ,Sⁿ-fiber f y) → H_n(Sⁿ,Sⁿ-{x})`.

Name the underlying pair map
`Hatcher.Sphere.finitePunctureProjectionPairHom`, its induced integral map
`Hatcher.Sphere.finitePunctureProjectionMap`, and their component formulas.
Also prove the reusable generic lemma that a relative-homology map is zero
when its ambient component factors through the target subspace; do not claim
that the pair morphism itself is zero.

The main theorem `Hatcher.Sphere.finitePunctureProjection_comp_summand` says
that, under `finitePunctureHomologyIso`, composing `p_x` with the `z`th
summand is the local-neighborhood inclusion when `z = x` and is zero when
`z ≠ x`.

State separate reassociated diagonal and off-diagonal component theorems. For
the off-diagonal factorization, use pairwise disjointness and the fact that the
center `x` lies in its own chosen neighborhood.

For the off-diagonal case, prove the reusable supporting lemma that a map of
relative pairs induces the zero map when its ambient component factors through
the target subspace. Apply it because the `z`th disjoint neighborhood misses
`x`. Package the resulting finite biproduct projection formula, with all
`DecidableEq` and finite-biproduct instances kept internal.

Normalize Hatcher's projection by the inverse open-neighborhood local-homology
map and identify it exactly with
`finitePunctureHomologyIso.inv ≫ Sigma.π _ x`. The point-indexed formulas are
vacuous for an empty fiber and require no `Nonempty` hypothesis.

## Depends on

- [Finite-puncture homology is the coproduct of the local groups](finite-puncture-homology-coproduct.md)

## Sources

- [Hatcher §2.2, the calculation `pᵢkⱼ = 0` in Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
