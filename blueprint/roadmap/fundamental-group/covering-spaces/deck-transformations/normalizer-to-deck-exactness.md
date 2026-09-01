---
declaration: theorem
origin: bridged
---

# The normalizer map is surjective with kernel the covering subgroup

For a pointed connected cover over a path-connected, locally path-connected
base, the normalizer homomorphism is surjective and has kernel

`H.subgroupOf (normalizer H)`.

The main artifact should package these two assertions as
`Hatcher.BasedConnectedCover.normalizerToDeck_ker_and_surjective`. The same
file should expose the representative calculation: a lifted endpoint is in
the deck orbit of the chosen point exactly when the represented loop class
lies in `normalizer H`.

For the kernel, use the closed-lift characterization and the inverse in the
normalizer action formula. For surjectivity, join `e₀` to the image of `e₀`
under an arbitrary deck transformation, project this path to a loop, and use
deck extensionality after matching the endpoint.

## Depends on

- [The normalizer acts by deck transformations](normalizer-to-deck.md)

## Proof depends on

- [The induced subgroup consists of loops with closed lifts](../closed-lift-image.md)
- [A deck transformation is determined by one lifted point](deck-realization.md)

## Sources

- [Hatcher §1.3, proof of Proposition 1.39 on page 71](../../../../sources/hatcher-1-3.md)
