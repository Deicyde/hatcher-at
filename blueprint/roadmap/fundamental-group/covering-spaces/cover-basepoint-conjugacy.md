---
declaration: theorem
origin: cited
---

# Changing the lifted basepoint conjugates the image subgroup

For a path-connected covering of `(X,x₀)`, changing the chosen point in the
fiber from `e₀` to `e₁` changes the induced image subgroup by conjugation with
the class of the projection of any path from `e₀` to `e₁`. Conversely, every
conjugate is realized by lifting a representative loop from `e₀`.

Intended artifact: `Hatcher.Covering.range_mapOfEq_basepointChange`.

The conjugation orientation must match Hatcher's path-composition convention;
the source writes the new subgroup as `g⁻¹ H g`.

## Depends on

- [Pointed connected covering spaces](based-connected-cover.md)

## Proof depends on

- [The fundamental group acts on a covering fiber](monodromy-action.md)
- [The induced subgroup consists of loops with closed lifts](closed-lift-image.md)

## Sources

- [Hatcher §1.3, proof of Theorem 1.38 on pages 67–68](../../../sources/hatcher-1-3.md)
