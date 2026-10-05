---
article_id: af_1d16b68f4d8e27f80da30d75
source_units: [hatcher-2-2-degree-foundations]
declaration: def
origin: bridged
---

# Degree gives a character of a sphere action

For a group `G`, define

```lean
abbrev Hatcher.Sphere.SphereAction (G : Type*) [Group G] (n : ℕ) :=
  G →* (((TopCat.sphere.{0} n : TopCat) : Type) ≃ₜ
    ((TopCat.sphere.{0} n : TopCat) : Type))
```

and define freeness to mean that every nonidentity group element acts without
a fixed point. For `0 < n`, package the degrees of the acting homeomorphisms
as the multiplicative character

```lean
noncomputable def Hatcher.Sphere.sphereActionDegreeHom ... : G →* ℤˣ
```

Prove that its underlying integer at `g` is the degree of `ρ g`. Also record
an explicit multiplicative equivalence `ℤˣ ≃* Multiplicative (ZMod 2)`.

## Depends on

- [The formal properties of degree](basic-degree-properties.md)

## Sources

- [Hatcher §2.2, degree character in Proposition 2.29, printed page 135](../../../../sources/hatcher-2-2-degree.md)
- [Degree-foundations implementation specification](../../../../sources/degree-theory-implementation.md)
