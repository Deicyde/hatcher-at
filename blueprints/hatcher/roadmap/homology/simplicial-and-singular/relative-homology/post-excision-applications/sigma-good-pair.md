---
source_units: [hatcher-2-1-post-excision-applications]
declaration: theorem
origin: bridged
---

# A nonempty coproduct of pointed good pairs is good

Let the index type be nonempty and suppose every pointed pair
`(X i,{x₀ i})` is good. Prove that their sigma pair is good:

```lean
theorem Hatcher.Relative.sigmaPointedPair_isGoodPair
    [Nonempty ι]
    (h : ∀ i, IsGoodPair (pointedPair (X i) (x₀ i))) :
    IsGoodPair (sigmaPointedPair x₀)
```

Assemble the chosen neighborhoods fiberwise. Prove their sigma is open,
prove the sigma of the closed basepoint images is closed, and assemble the
pointwise strong deformation retractions into one sigma deformation. The
nonempty-index assumption supplies the nonempty subspace required by
`GoodPairData`.

Keep the empty-index case out of this theorem. It is handled directly by the
contractibility of the project's empty pointed wedge in Corollary 2.25.

## Depends on

- [The coproduct pair of a family of pointed spaces](sigma-pointed-pair.md)
- [Good pairs and neighborhood deformation retracts](../good-pair-quotient/good-pair-data.md)
- [Strong deformation retracts](../good-pair-quotient/strong-deformation-retract.md)

## Sources

- [Hatcher §2.1, good-pair hypothesis in Corollary 2.25, printed page 126](../../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../../sources/post-excision-applications-implementation.md)
