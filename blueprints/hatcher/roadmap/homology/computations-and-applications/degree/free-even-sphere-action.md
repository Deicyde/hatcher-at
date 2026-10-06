---
article_id: af_abbd1071b7feae6c88eb97da
source_units: [hatcher-2-2-degree-foundations]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Sphere.exists_freeSphereAction_iff_mulEquiv_zmodTwo
---

# Only the antipodal group acts freely on an even sphere

Let `G` be a nontrivial group, `0 < n`, and `Even n`. Prove Hatcher's
Proposition 2.29 in the exact classification form

```lean
theorem Hatcher.Sphere.exists_freeSphereAction_iff_mulEquiv_zmodTwo ... :
  (∃ ρ : SphereAction G n, ρ.IsFree) ↔
    Nonempty (G ≃* Multiplicative (ZMod 2))
```

For the forward implication, use freeness and the fixed-point-free degree
formula to prove that the action's degree character is injective, then identify
its image with the two integer units. For the reverse implication, transport
the explicit free antipodal `ℤ/2` action across the group equivalence. Include
that action and its freeness as supporting declarations. Do not assume `G` is
finite.

The supporting theorem
`Hatcher.Sphere.sphereActionDegreeHom_injective_of_free_even` proves the
character injective directly from freeness. The implementation also publishes
`Hatcher.Sphere.antipodalZModTwoAction` and
`Hatcher.Sphere.antipodalZModTwoAction_isFree`; the reverse implication of the
main theorem transports this literal action through the supplied group
equivalence.

## Depends on

- [Coordinate sign changes on the sphere](sphere-coordinate-sign-changes.md)
- [Degree gives a character of a sphere action](sphere-action-degree-character.md)

## Proof depends on

- [A fixed-point-free sphere map has antipodal degree](fixed-point-free-degree.md)

## Sources

- [Hatcher §2.2, Proposition 2.29, printed page 135](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
