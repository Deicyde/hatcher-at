---
article_id: af_24f895b6cfca07ed98a9e342
source_units: [hatcher-2-1-post-excision-applications]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Relative.tripleConnecting_eq, Hatcher.Relative.tripleConnecting_isIso
---

# The triple connecting map sends a relative cycle to its boundary

Give the connecting morphism in the long exact sequence of a topological
triple its chain-level formula. If a cycle in `C_n(X,A;R)` is lifted to
`C_n(X,B;R)` and its boundary is represented in `C_{n-1}(A,B;R)`, prove that
`Hatcher.Relative.tripleConnecting` sends the original homology class to the
class of that boundary.

The main artifact is `Hatcher.Relative.tripleConnecting_eq`, parallel to the
existing `pairConnecting_eq`. Include the categorical criterion that this
connecting map is an isomorphism when the two adjacent groups
`H_n(X,B;R)` and `H_{n-1}(X,B;R)` vanish.

This node is generic triple-sequence infrastructure. Example 2.23 uses it to
identify the image of the ordered identity simplex, not merely to know that
some connecting isomorphism exists.

`Hatcher.Relative.tripleConnecting_eq` states the formula with the relative
cycle, its lift, and the boundary representative as explicit chain-level data;
the resulting equality has coefficient `+1`. The companion theorem
`Hatcher.Relative.tripleConnecting_isIso` shows that the connecting morphism
is an isomorphism when the adjacent groups `H_n(X,B;R)` and
`H_{n-1}(X,B;R)` vanish.

## Depends on

- [Relative chains of a triple form a short exact sequence](../../simplicial-and-singular/relative-homology/triple-chain-short-exact-sequence.md)

## Proof depends on

- [The long exact sequence of a triple](../../simplicial-and-singular/relative-homology/triple-long-exact-sequence.md)

## Sources

- [Hatcher §2.1, boundary calculation in Example 2.23, printed page 125](../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../sources/post-excision-applications-implementation.md)
