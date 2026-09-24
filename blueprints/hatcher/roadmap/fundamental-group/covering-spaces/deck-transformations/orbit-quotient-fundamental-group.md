---
article_id: af_4f74ca06c7815be5efe37f5c
source_units: [hatcher-1-3-selected-spine]
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Covering.orbitQuotientFundamentalGroupEquiv
---

# The orbit-quotient fundamental group recovers the acting group

**Hatcher, Proposition 1.40(c) (page 72).** Let `G` act on a path-connected,
locally path-connected space `Y` by a covering-space action, let `q` be the
orbit projection, and choose `y₀ : Y`. Then there is a group isomorphism

`π₁(Y/G, q(y₀)) ⧸ range(π₁(q)) ≃* G`.

Intended artifact:
`Hatcher.Covering.orbitQuotientFundamentalGroupEquiv`.

Use the path-connected and locally path-connected structures inherited by the
orbit quotient, namely `Quotient.instPathConnectedSpace` and
`Quotient.locPathConnectedSpace`. The subgroup is the range of
`FundamentalGroup.map ⟨q, ...⟩ y₀`, where the continuous map is the orbit
projection; `mapOfEq` is unnecessary because the target basepoint is
definitionally `q y₀`. Proposition 1.39 identifies the deck group with the
displayed fundamental-group quotient, and Proposition 1.40(b) identifies the
same deck group with `G`. Form the quotient only after obtaining the
normal-subgroup instance from normality of the orbit cover.

Formalized in `Hatcher/Covering/OrbitQuotientFundamentalGroup.lean`. The proof
explicitly identifies the direct `FundamentalGroup.map` range with the
`mapOfEq` range stored by the pointed-cover structure before transporting the
quotient equivalence.

## Depends on

- [Covering-space actions give quotient coverings](covering-space-action.md)

## Proof depends on

- [The deck group is the normalizer quotient](deck-group-calculation.md)
- [Orbit quotients are normal and have the expected deck group](orbit-quotient-deck-group.md)

## Sources

- [Hatcher §1.3, Proposition 1.40(c)](../../../../sources/hatcher-1-3.md)
