---
article_id: af_67ed4905c351d887224e90d5
source_units: [hatcher-1-1-basic-constructions]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.PathConcatenationGroup.fromPath_trans
---

# Path concatenation gives the fundamental-group law

**Hatcher, Proposition 1.3 (page 26).** The path-homotopy classes of loops at
`x₀` form a group with multiplication `[p][q] = [p · q]`, where `p · q`
traverses `p` first and then `q`.

Mathlib defines `FundamentalGroup X x` as the endomorphism group of `x` in the
fundamental groupoid and installs its `Group` instance in
`Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`.
Categorical composition uses the convention opposite to Hatcher's displayed
product, so the local abbreviation `Hatcher.PathConcatenationGroup` takes the
opposite group. The theorem
`Hatcher.PathConcatenationGroup.fromPath_trans` then states exactly
`fromPath (p.trans q) = fromPath p * fromPath q`.

## Depends on

- [Path homotopy is an equivalence relation](path-homotopy-equivalence.md)

## Sources

- [Hatcher §1.1, Proposition 1.3, page 26](../../../sources/hatcher-1-1.md)
