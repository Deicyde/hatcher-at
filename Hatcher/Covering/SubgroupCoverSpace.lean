import Hatcher.Covering.UniversalCoverPathSpace

noncomputable section

open CategoryTheory

namespace Hatcher

universe u

variable {X : Type u} [TopologicalSpace X] {x₀ : X}

/-- Two path classes from `x₀` are equivalent modulo `H` when they have the same endpoint
and their concatenation is a loop class in `H`. -/
def subgroupCoverRel (H : Subgroup (FundamentalGroup X x₀))
    (a b : UniversalCover X x₀) : Prop :=
  ∃ h : a.1 = b.1,
    FundamentalGroup.fromPath (a.2.trans ((b.2.cast rfl h).symm)) ∈ H

private theorem subgroupCoverRel_refl (H : Subgroup (FundamentalGroup X x₀))
    (a : UniversalCover X x₀) : subgroupCoverRel H a a := by
  rcases a with ⟨x, γ⟩
  refine ⟨rfl, ?_⟩
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]
  change (FundamentalGroupoid.fromPath γ ≫
    Groupoid.inv (FundamentalGroupoid.fromPath γ) : FundamentalGroup X x₀) ∈ H
  rw [Groupoid.comp_inv]
  exact H.one_mem

private theorem subgroupCoverRel_symm (H : Subgroup (FundamentalGroup X x₀))
    {a b : UniversalCover X x₀} : subgroupCoverRel H a b → subgroupCoverRel H b a := by
  rcases a with ⟨x, γ⟩
  rcases b with ⟨y, δ⟩
  rintro ⟨h, hm⟩
  change x = y at h
  subst y
  refine ⟨rfl, ?_⟩
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl] at hm ⊢
  let γ' : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x := γ
  let δ' : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x := δ
  change (δ' ≫ Groupoid.inv γ') ∈ H
  change (γ' ≫ Groupoid.inv δ') ∈ H at hm
  have hinv := H.inv_mem hm
  change Groupoid.inv (γ' ≫ Groupoid.inv δ') ∈ H at hinv
  have heq : Groupoid.inv (γ' ≫ Groupoid.inv δ') =
      δ' ≫ Groupoid.inv γ' := by
    rw [Groupoid.inv_eq_inv]
    apply IsIso.inv_eq_of_hom_inv_id
    simp [Category.assoc]
  rwa [heq] at hinv

private theorem subgroupCoverRel_trans (H : Subgroup (FundamentalGroup X x₀))
    {a b c : UniversalCover X x₀} :
    subgroupCoverRel H a b → subgroupCoverRel H b c → subgroupCoverRel H a c := by
  rcases a with ⟨x, γ⟩
  rcases b with ⟨y, δ⟩
  rcases c with ⟨z, ε⟩
  rintro ⟨hxy, hγδ⟩ ⟨hyz, hδε⟩
  change x = y at hxy
  subst y
  change x = z at hyz
  subst z
  refine ⟨rfl, ?_⟩
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl] at hγδ hδε ⊢
  change (FundamentalGroupoid.fromPath γ ≫
    Groupoid.inv (FundamentalGroupoid.fromPath δ)) ∈ H at hγδ
  change (FundamentalGroupoid.fromPath δ ≫
    Groupoid.inv (FundamentalGroupoid.fromPath ε)) ∈ H at hδε
  have hmul := H.mul_mem hδε hγδ
  change (FundamentalGroupoid.fromPath γ ≫
    Groupoid.inv (FundamentalGroupoid.fromPath ε)) ∈ H
  change ((FundamentalGroupoid.fromPath γ ≫
    Groupoid.inv (FundamentalGroupoid.fromPath δ)) ≫
      (FundamentalGroupoid.fromPath δ ≫
        Groupoid.inv (FundamentalGroupoid.fromPath ε))) ∈ H at hmul
  simpa [Category.assoc] using hmul

/-- The equivalence relation defining the covering associated to `H`. -/
def subgroupCoverSetoid (H : Subgroup (FundamentalGroup X x₀)) :
    Setoid (UniversalCover X x₀) where
  r := subgroupCoverRel H
  iseqv := ⟨subgroupCoverRel_refl H, subgroupCoverRel_symm H,
    subgroupCoverRel_trans H⟩

/-- The path-class covering space associated to a subgroup of the fundamental group. -/
def SubgroupCover (H : Subgroup (FundamentalGroup X x₀)) :=
  Quotient (subgroupCoverSetoid H)

namespace SubgroupCover

variable (H : Subgroup (FundamentalGroup X x₀))

/-- The quotient topology inherited from the path-class universal cover. -/
instance instTopologicalSpace : TopologicalSpace (SubgroupCover H) :=
  inferInstanceAs (TopologicalSpace (Quotient (subgroupCoverSetoid H)))

/-- Endpoint projection from the subgroup cover. -/
def proj : SubgroupCover H → X :=
  Quotient.lift UniversalCover.proj fun _ _ h ↦ h.choose

/-- The class of the constant path is the basepoint of the subgroup cover. -/
def basepoint : SubgroupCover H :=
  Quotient.mk (subgroupCoverSetoid H) (UniversalCover.basepoint (X := X) (x₀ := x₀))

@[simp]
theorem proj_basepoint : proj H (basepoint H) = x₀ := rfl

end SubgroupCover

end Hatcher
