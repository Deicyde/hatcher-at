---
article_id: af_c25fd700a7f3e9d9ce373eb6
source_units: [hatcher-2-2-degree-realization-suspension]
declaration: theorem
origin: cited
---

# Every integer is the degree of a sphere map

**Hatcher, Example 2.31.** For every n > 0 and every d : ℤ, there exists a continuous f : Sⁿ → Sⁿ with degree(f) = d. The witness is the geometric pinch-and-fold map, not a map supplied with its degree as a hypothesis.

## Proof sketch

Use k = |d| balls and give every summand sign +1 or −1 according to d. The signed degree-sum formula gives d. When d = 0 the empty pinch family yields the constant map. This proves the source construction in all positive sphere dimensions.

## Depends on

- [sphere degree definition](../../degree/sphere-degree-definition.md)

## Proof depends on

- [A positive-dimensional sphere contains any finite number of disjoint balls](finite-disjoint-sphere-balls.md)
- [Reflections correct the signs of a sphere fold map](signed-sphere-fold-map.md)
- [The degree of a signed pinch map is the sum of its signs](signed-pinch-degree-sum.md)

## Sources

- [Hatcher §2.2, printed pages 136–137](../../../../../sources/hatcher-2-2-degree-applications.md#example-231)
- [Degree-realization and suspension specification](../../../../../sources/degree-applications-implementation.md)
