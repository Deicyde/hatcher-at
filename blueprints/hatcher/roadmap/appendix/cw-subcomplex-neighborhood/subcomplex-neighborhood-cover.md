---
source_units: [appendix-proposition-a-5]
declaration: theorem
origin: bridged
---

# Subcomplex decompositions admit compatible neighborhoods

Let `A` and `B` be subcomplexes whose carriers cover a classical CW complex
`C`. Package their regular neighborhoods `U = N A` and `V = N B` with

- `A ⊆ interior U` and `B ⊆ interior V`;
- strong deformation retractions `U ↘ A` and `V ↘ B`;
- `U ∩ V = N (A ∩ B)`; and
- the induced strong deformation retraction `U ∩ V ↘ A ∩ B`.

The main artifact is
`Hatcher.ClassicalCW.subcomplexNeighborhoodCover`. Keep this structure in a
topology-neutral module so Corollary 2.24 can consume it without depending on
the later Mayer–Vietoris development.

The statement includes the empty-intersection case. When `A ∩ B` is empty,
the common neighborhood and its deformation data are empty as well.

## Depends on

- [Intersections of CW subcomplexes](subcomplex-intersection.md)
- [A common regular-neighborhood system for subcomplexes](regular-neighborhood-system.md)
- [A regular neighborhood strongly deformation retracts onto its subcomplex](regular-neighborhood-strong-deformation-retract.md)

## Sources

- [Hatcher, Appendix Proposition A.5 and the following intersection observation, printed page 523](../../../sources/hatcher.md)
- [CW-subcomplex neighborhood implementation specification](../../../sources/cw-subcomplex-neighborhood-implementation.md)
