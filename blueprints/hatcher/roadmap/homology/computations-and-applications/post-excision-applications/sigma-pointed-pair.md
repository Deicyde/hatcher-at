---
article_id: af_47796e967178521ad49710b5
source_units: [hatcher-2-1-post-excision-applications]
declaration: def
origin: background
---

# The coproduct pair of a family of pointed spaces

For a family of pointed spaces `(X i, x₀ i)`, define the topological pair

`(Σ i, X i ; Σ i, {x₀ i})`

whose structure map sends `⟨i, unit⟩` to `⟨i, x₀ i⟩`. The main artifact is
`Hatcher.Relative.sigmaPointedPair`. For every index `i`, expose the canonical
map from `pointedPair (X i) (x₀ i)` to the sigma pair and prove its component
formulas.

The construction uses the ordinary topological sigma type, which is the
coproduct in `TopCat`. It includes the empty family: then both the ambient and
subspace of the sigma pair are empty.

## Depends on

None beyond the existing topological-pair and coproduct APIs.

## Sources

- [Hatcher §2.1, proof of Corollary 2.25, printed page 126](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)
