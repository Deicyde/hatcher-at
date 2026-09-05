---
article_id: af_e566022fcd1062ff9f95ca71
---

# Deck transformations and quotient actions

Hatcher's Propositions 1.39 and 1.40 identify the deck group of a connected
cover from its fundamental-group subgroup, then recover this calculation for
orbit quotients by covering-space actions.

The pinned Mathlib has the quotient-covering machinery but no deck group.
Code from Mathlib PR
[#40135](https://github.com/leanprover-community/mathlib4/pull/40135)
landed on Mathlib master after the pin and supplies useful API prior art. This
roadmap keeps the required compatibility layer local and does not mark that
post-pin code as present in the build.

- [Deck transformations and normal covers](deck-transformation-group.md)
- [A deck transformation is determined by one lifted point](deck-realization.md)
- [The normalizer acts by deck transformations](normalizer-to-deck.md)
- [The normalizer map is surjective with kernel the covering subgroup](normalizer-to-deck-exactness.md)
- [The deck group is the normalizer quotient](deck-group-calculation.md)
- [Covering-space actions give quotient coverings](covering-space-action.md)
- [Orbit quotients are normal and have the expected deck group](orbit-quotient-deck-group.md)
- [The orbit-quotient fundamental group recovers the acting group](orbit-quotient-fundamental-group.md)

## Sources

- [Hatcher §1.3, Propositions 1.39 and 1.40](../../../../sources/hatcher-1-3.md)
