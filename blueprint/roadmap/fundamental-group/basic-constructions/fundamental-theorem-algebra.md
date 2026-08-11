---
declaration: theorem
origin: cited
---

# The fundamental theorem of algebra

**Hatcher, Theorem 1.8 (page 31).** Every nonconstant polynomial with complex
coefficients has a root in `ℂ`.

Suppose `p(z) = zⁿ + aₙ₋₁zⁿ⁻¹ + ⋯ + a₀` has no root. For each radius `r`, the
loop `s ↦ p(r e^{2πis}) / |p(r e^{2πis})|` in `S¹` is defined, and as `r` varies
these loops are all homotopic to each other; at `r = 0` the loop is constant, so
every one of them is nullhomotopic. For `r` large enough that
`r > |a₀| + ⋯ + |aₙ₋₁|` and `r > 1`, the polynomial `p` is homotopic through
root-free polynomials to `zⁿ`, whose associated loop has winding number `n`. So
`n = 0` and `p` is constant.

**This result is already in Mathlib**, as `Complex.isAlgClosed` in
`Analysis/Complex/Polynomial/Basic.lean`, proved by Liouville's theorem. This
node formalizes Hatcher's topological proof instead. It is a source target and
a second proof, not new coverage, and the
[coverage contract](../../../coverage/README.md) records that. `mathlib: true`
is deliberately not set: that key marks a result upstreamed by this project,
and nothing here would be.

Intended artifact: `Hatcher.exists_root_of_degree_pos` in
`Hatcher/Applications/FundamentalTheoremAlgebra.lean`.

## Depends on

- [The fundamental group of the circle](fundamental-group-circle.md)

## Sources

- [Hatcher §1.1, Theorem 1.8, page 31](../../../sources/hatcher-1-1.md)
