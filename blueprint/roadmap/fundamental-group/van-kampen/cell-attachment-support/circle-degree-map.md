---
article_id: af_51e0760947368340fe1d5c5f
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Circle.mapOfEq_degreeMap_degreeLoopClass_one
---

# The degree-n circle map sends the generator to the degree-n loop

For a natural number `n`, let `dₙ : S¹ → S¹` be the map `z ↦ zⁿ`. The
induced homomorphism on fundamental groups sends the chosen degree-one loop
class to the degree-`n` loop class.

Formalized as `Hatcher.Circle.mapOfEq_degreeMap_degreeLoopClass_one` in
`Hatcher/VanKampen/CyclicPresentationAlgebra.lean`. The stronger path-level
formula `degreeMap_map_loopOfInt` shows that `dₙ` sends every degree-`m` loop
to the degree-`n m` loop. The sign is positive for the project's
counterclockwise generator.

This is the attaching-map compatibility needed by the cyclic presentation
complex. It does not construct that cell attachment.

## Depends on

- [The fundamental group of the circle](../../basic-constructions/fundamental-group-circle.md)

## Sources

- [Hatcher §1.2, Example 1.29, page 52](../../../../sources/hatcher-1-2.md)
