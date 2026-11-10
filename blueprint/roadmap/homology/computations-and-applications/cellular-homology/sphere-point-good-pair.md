---
article_id: af_989591aa389447da1fa6d34d
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Sphere.sphere_pointedPair_isGoodPair, Hatcher.Sphere.sphereSingletonGoodPairData
---

# Every pointed sphere is a good pair

For every sphere dimension n and point b ∈ Sⁿ, the actual pair (Sⁿ,{b}) is
good. Construct its neighborhood and a contraction fixing b at every time.
The conclusion includes the two-point sphere S⁰.

## Proof sketch

For n > 0, use the chart omitting the antipode of b and linearly contract its
Euclidean coordinates to the chart image of b. Transport the contraction
back and retain the actual inclusion. In S⁰, use the discrete singleton
neighborhood. Hausdorffness supplies the closed singleton.

## Depends on

- [Good pair data](../../simplicial-and-singular/relative-homology/good-pair-quotient/good-pair-data.md)

## Proof depends on

- [Punctured sphere stereographic](../degree/punctured-sphere-stereographic.md)
- [Sphere hemisphere stereographic models](../sphere-homology/sphere-hemisphere-stereographic-models.md)
- [Zero sphere two point homeomorphism](../sphere-homology/zero-sphere-two-point-homeomorphism.md)

## Sources

- [Hatcher §2.2, cellular homology, printed pages 137–140](../../../../sources/hatcher-2-2-cellular.md#lemma-234)
- [Cellular-homology implementation specification](../../../../sources/cellular-homology-implementation.md)
