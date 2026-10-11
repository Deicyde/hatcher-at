---
article_id: af_85e59358edc190186cfde9fb
source_units: [hatcher-2-2-local-degree]
declaration: def
origin: bridged
---

# The coproduct of a family of topological pairs

For `P : ι → TopPair`, define `Hatcher.Relative.sigmaPair P`. Its ambient
space is `Σ i, (P i).fst`, its subspace is `Σ i, (P i).snd`, and its structure
map applies `(P i).map` in the same summand. The main artifact is
`Hatcher.Relative.sigmaPair`.

For every `i`, also expose the canonical morphism
`Hatcher.Relative.sigmaPairι P i : P i ⟶ sigmaPair P` and prove formulas for
its ambient and subspace components. Specializing to pointed pairs must recover
the existing `sigmaPointedPair` construction up to a named pair isomorphism or
an exact compatibility theorem.

## Depends on

None.

## Sources

- [Hatcher §2.2, direct-sum step in Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
