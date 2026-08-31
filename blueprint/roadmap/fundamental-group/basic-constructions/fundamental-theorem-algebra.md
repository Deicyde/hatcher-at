---
declaration: theorem
origin: cited
---

# The fundamental theorem of algebra

**Hatcher, Theorem 1.8 (page 31).** Every nonconstant polynomial with complex
coefficients has a root in `ℂ`.

Suppose `p(z) = zⁿ + aₙ₋₁zⁿ⁻¹ + ⋯ + a₀` has no root. For each radius `r`,
normalize by the nonzero value `p(r)`: set
`qᵣ(s) = p(r e^{2πis}) / p(r)`, then take the based loop
`s ↦ qᵣ(s) / |qᵣ(s)|` in `S¹`. As `r` varies these loops are homotopic; at
`r = 0` the loop is constant, so every one is nullhomotopic. For `r > 1`
larger than the sum of the lower coefficients' norms, Hatcher deforms
`p(z)` to `zⁿ` through
`pₜ(z) = zⁿ + t(aₙ₋₁zⁿ⁻¹ + ⋯ + a₀)`. The required estimate says `pₜ` has no
zero on the circle `|z| = r`, so the associated loop is homotopic to
`s ↦ e^{2πins}`, whose winding number is `n`. Hence `n = 0` and `p` is
constant.

**This result is already in Mathlib**, as `Complex.exists_root` and the
`Complex.isAlgClosed` instance in
`Analysis/Complex/Polynomial/Basic.lean`, proved by Liouville's theorem. This
node formalizes Hatcher's topological proof instead. It is a source target and
a second proof, not new coverage, and the
[coverage contract](../../../coverage/README.md) records that. `mathlib: true`
is deliberately not set because this node promises Hatcher's proof rather than
an alias to the existing Mathlib theorem.

Intended artifact: `Hatcher.exists_root_of_degree_pos` in
`Hatcher/Applications/FundamentalTheoremAlgebra.lean`.

## Proof depends on

- [The fundamental group of the circle](fundamental-group-circle.md)

## Sources

- [Hatcher §1.1, Theorem 1.8, page 31](../../../sources/hatcher-1-1.md)
