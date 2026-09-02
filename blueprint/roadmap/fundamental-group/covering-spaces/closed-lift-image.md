---
declaration: proposition
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Covering.mem_range_map_iff_monodromy_fixed
---

# The induced subgroup consists of loops with closed lifts

**Hatcher, Proposition 1.31, second clause (page 61).** For a pointed covering
`p : (E,e₀) → (X,x₀)`, a class in `π₁(X,x₀)` lies in the range of the induced
map from `π₁(E,e₀)` exactly when its lift beginning at `e₀` ends at `e₀`.
Equivalently, the image subgroup is the stabilizer of `e₀` for the monodromy
action.

Formalized as `Hatcher.Covering.mem_range_map_iff_monodromy_fixed` in
`Hatcher/Covering/Monodromy.lean`. The forward implication is Mathlib's
`IsCoveringMap.monodromy_map`; the reverse implication lifts a representative
loop and uses the fixed endpoint to make that lift a loop based at `e₀`.

## Depends on

- [The fundamental group acts on a covering fiber](monodromy-action.md)

## Sources

- [Hatcher §1.3, Proposition 1.31](../../../sources/hatcher-1-3.md)
