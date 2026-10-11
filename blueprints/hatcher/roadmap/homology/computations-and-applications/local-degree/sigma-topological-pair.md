---
article_id: af_85e59358edc190186cfde9fb
source_units: [hatcher-2-2-local-degree]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Relative.sigmaPair
---

# The coproduct of a family of topological pairs

For `P : ι → TopPair`, define `Hatcher.Relative.sigmaPair P`. Its ambient
space is `Σ i, (P i).fst`, its subspace is `Σ i, (P i).snd`, and its structure
map applies `(P i).map` in the same summand. The main artifact is
`Hatcher.Relative.sigmaPair`.

For every `i`, also expose the canonical morphism
`Hatcher.Relative.sigmaPairι P i : P i ⟶ sigmaPair P` and prove formulas for
the structure map and its ambient and subspace components, both as morphisms
and on elements. Make the generic construction the implementation core while
preserving the existing `sigmaPointedPair` and `sigmaPointedPairι` names as
definitional wrappers. Publish named exact compatibility equalities for the
pointed object and every summand inclusion; do not maintain two independent
implementations or supply only an object isomorphism with no summand triangle.
The construction requires no `Nonempty ι` hypothesis and includes the empty
family.

The canonical summand map is `Hatcher.Relative.sigmaPairι`. The structure-map
and summand-component formulas are
`Hatcher.Relative.sigmaPair_map_apply`,
`Hatcher.Relative.sigmaPairι_fst`,
`Hatcher.Relative.sigmaPairι_fst_apply`,
`Hatcher.Relative.sigmaPairι_snd`, and
`Hatcher.Relative.sigmaPairι_snd_apply`.

The existing pointed constructions are definitional wrappers. Their named
exact compatibility equalities are
`Hatcher.Relative.sigmaPointedPair_eq_sigmaPair` and
`Hatcher.Relative.sigmaPointedPairι_eq_sigmaPairι`.

## Depends on

- [The coproduct pair of a family of pointed spaces](../post-excision-applications/sigma-pointed-pair.md)

## Sources

- [Hatcher §2.2, direct-sum step in Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
