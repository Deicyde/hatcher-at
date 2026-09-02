---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.UniversalCover.isTopologicalBasis_basicOpen
---

# The sets U[γ] form the universal-cover basis

For a small path-connected open set `U` and a path class `[γ]` ending in `U`,
let `U[γ]` consist of classes obtained by extending `γ` along a path inside
`U`. These sets form a topological basis on `Hatcher.UniversalCover X x₀`.
Moreover, `U[γ] = U[γ']` whenever `[γ'] ∈ U[γ]`, and endpoint projection is a
bijection from `U[γ]` to `U`.

Intended artifact: `Hatcher.UniversalCover.isTopologicalBasis_basicOpen`.

This node uses Hatcher's direct basis argument. It does not require the
compact-open tube-neighborhood API from PR #38292.

Formalized in `Hatcher/Covering/UniversalCoverBasis.lean`. The same file proves
`basicOpen_eq_of_mem` and `bijOn_proj_basicOpen`, covering the equality and
endpoint-bijection clauses of the source statement.

## Depends on

- [The path-class universal-cover space](universal-cover-path-space.md)

## Proof depends on

- [Small nullhomotopy neighborhoods form a basis](nullhomotopic-open-basis.md)

## Sources

- [Hatcher §1.3, universal-cover basic sets on page 64](../../../../sources/hatcher-1-3.md)
