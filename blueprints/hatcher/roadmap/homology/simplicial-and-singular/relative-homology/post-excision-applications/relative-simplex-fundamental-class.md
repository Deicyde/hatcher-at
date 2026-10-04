---
source_units: [hatcher-2-1-post-excision-applications]
declaration: theorem
origin: cited
---

# The identity simplex generates relative simplex homology

**Hatcher, Example 2.23 (printed page 125).** Regard the identity map of the
ordered topological simplex `Δ[n]` as a singular `n`-simplex. Its boundary
lies in `∂Δ[n]`, so it defines a canonical class morphism

`R ⟶ H_n(Δ[n], ∂Δ[n];R)`.

Define this morphism as
`Hatcher.Simplex.relativeSimplexFundamentalClass R n` using the actual
singular-chain inclusion, relative-chain projection, cycle lift, and homology
projection. Prove

```lean
theorem Hatcher.Simplex.relativeSimplexFundamentalClass_isIso :
    IsIso (relativeSimplexFundamentalClass R n)
```

by induction on `n`. In the successor step use the triple
`(Δ[n+1], ∂Δ[n+1], Λ⁰[n+1])`. Choose face zero as the omitted face, so the
surviving term of the alternating boundary has coefficient `+1`; no hidden
orientation sign may be absorbed into an arbitrary isomorphism. The integral
specialization says that the identity simplex represents a generator of the
infinite cyclic relative group.

## Depends on

- [The boundary and zero horn of a standard topological simplex](standard-simplex-boundary-horn.md)

## Proof depends on

- [A standard simplex strongly deformation retracts onto its zero horn](standard-simplex-zero-horn-retraction.md)
- [The zero face induces an isomorphism in relative homology](standard-simplex-zero-face-relative-homology.md)
- [The triple connecting map sends a relative cycle to its boundary](triple-connecting-cycle-formula.md)
- [The long exact sequence of a triple](../triple-long-exact-sequence.md)
- [Homology of a point](../../point-homology.md)

## Sources

- [Hatcher §2.1, Example 2.23, printed page 125](../../../../../sources/hatcher-2-1.md)
- [Post-excision applications implementation specification](../../../../../sources/post-excision-applications-implementation.md)
