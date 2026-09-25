import Hatcher.VanKampen.PointedWedge

namespace Hatcher.PointedWedge

universe u v w

variable {ι : Type u} {X : ι → Type v} (x₀ : ∀ i, X i)

private def descPre {Y : Type w} (y₀ : Y) (f : ∀ i, X i → Y) :
    Option (Σ i, X i) → Y
  | none => y₀
  | some ⟨i, x⟩ => f i x

private theorem descPre_eq_of_rel {Y : Type w} (y₀ : Y) (f : ∀ i, X i → Y)
    (hf : ∀ i, f i (x₀ i) = y₀) {a b : Option (Σ i, X i)}
    (h : PointedWedge.setoid X x₀ a b) : descPre y₀ f a = descPre y₀ f b := by
  change Relation.EqvGen (PointedWedge.Rel X x₀) a b at h
  induction h with
  | rel a b h =>
      cases h with
      | base i => exact (hf i).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The map out of a pointed wedge induced by a compatible family of maps. -/
def desc {Y : Type w} [∀ i, TopologicalSpace (X i)] [TopologicalSpace Y]
    (y₀ : Y) (f : ∀ i, C(X i, Y)) (hf : ∀ i, f i (x₀ i) = y₀) :
    C(Hatcher.PointedWedge X x₀, Y) where
  toFun := Quotient.lift (descPre y₀ fun i => f i)
    (fun _ _ h => descPre_eq_of_rel x₀ y₀ (fun i => f i) hf h)
  continuous_toFun := by
    change @Continuous (Quotient (PointedWedge.setoid X x₀)) Y
      (TopologicalSpace.coinduced
        (Quotient.mk (PointedWedge.setoid X x₀) :
          Option (Σ i, X i) → Quotient (PointedWedge.setoid X x₀))
        (prequotientTopology (X := X))) _
      (Quotient.lift (descPre y₀ fun i => f i)
        (fun _ _ h => descPre_eq_of_rel x₀ y₀ (fun i => f i) hf h))
    rw [continuous_coinduced_dom]
    change @Continuous (Option (Σ i, X i)) Y
      (prequotientTopology (X := X)) _ (descPre y₀ fun i => f i)
    rw [prequotientTopology, continuous_sup_dom]
    constructor
    · rw [continuous_coinduced_dom]
      exact continuous_sigma fun i => (f i).continuous
    · rw [continuous_coinduced_dom]
      exact continuous_const

@[simp]
theorem desc_basepoint {Y : Type w} [∀ i, TopologicalSpace (X i)] [TopologicalSpace Y]
    (y₀ : Y) (f : ∀ i, C(X i, Y)) (hf : ∀ i, f i (x₀ i) = y₀) :
    desc x₀ y₀ f hf (basepoint x₀) = y₀ := rfl

@[simp]
theorem desc_inclusion {Y : Type w} [∀ i, TopologicalSpace (X i)] [TopologicalSpace Y]
    (y₀ : Y) (f : ∀ i, C(X i, Y)) (hf : ∀ i, f i (x₀ i) = y₀)
    (i : ι) (x : X i) : desc x₀ y₀ f hf (inclusion x₀ i x) = f i x := rfl

/-- Maps out of a pointed wedge agree if they agree at the extra wedge point
and on every summand. The wedge-point hypothesis is essential for an empty
index type. -/
@[ext]
theorem continuousMap_ext {Y : Type w} [∀ i, TopologicalSpace (X i)] [TopologicalSpace Y]
    {F G : C(Hatcher.PointedWedge X x₀, Y)}
    (hbase : F (basepoint x₀) = G (basepoint x₀))
    (hinclusion : ∀ i x, F (inclusion x₀ i x) = G (inclusion x₀ i x)) : F = G := by
  apply ContinuousMap.ext
  intro z
  induction z using Quotient.inductionOn with
  | _ z =>
      cases z with
      | none => exact hbase
      | some z => exact hinclusion z.1 z.2

/-- The universal property of the pointed wedge, including its adjoined point
when the family is empty. -/
def continuousMapEquiv {Y : Type w} [∀ i, TopologicalSpace (X i)] [TopologicalSpace Y] :
    C(Hatcher.PointedWedge X x₀, Y) ≃
      Σ y₀ : Y, {f : ∀ i, C(X i, Y) // ∀ i, f i (x₀ i) = y₀} where
  toFun F :=
    ⟨F (basepoint x₀),
      ⟨fun i => F.comp ⟨inclusion x₀ i, continuous_inclusion x₀ i⟩,
        fun i => by
          change F (inclusion x₀ i (x₀ i)) = F (basepoint x₀)
          rw [inclusion_basepoint]⟩⟩
  invFun data := desc x₀ data.1 data.2.1 data.2.2
  left_inv F := by
    apply continuousMap_ext x₀
    · rfl
    · intro i x
      rfl
  right_inv data := by
    rcases data with ⟨y₀, ⟨f, hf⟩⟩
    apply Sigma.ext rfl
    rfl

private def mapCongr {Z : ι → Type w}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Z i)]
    (z₀ : ∀ i, Z i) (e : ∀ i, X i ≃ₜ Z i) (he : ∀ i, e i (x₀ i) = z₀ i) :
    C(Hatcher.PointedWedge X x₀, Hatcher.PointedWedge Z z₀) :=
  desc x₀ (basepoint z₀)
    (fun i => (⟨inclusion z₀ i, continuous_inclusion z₀ i⟩ :
      C(Z i, Hatcher.PointedWedge Z z₀)).comp
        (⟨e i, (e i).continuous⟩ : C(X i, Z i)))
    (fun i => by
      change inclusion z₀ i (e i (x₀ i)) = basepoint z₀
      rw [he i, inclusion_basepoint])

@[simp]
private theorem mapCongr_basepoint {Z : ι → Type w}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Z i)]
    (z₀ : ∀ i, Z i) (e : ∀ i, X i ≃ₜ Z i) (he : ∀ i, e i (x₀ i) = z₀ i) :
    mapCongr x₀ z₀ e he (basepoint x₀) = basepoint z₀ := rfl

@[simp]
private theorem mapCongr_inclusion {Z : ι → Type w}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Z i)]
    (z₀ : ∀ i, Z i) (e : ∀ i, X i ≃ₜ Z i) (he : ∀ i, e i (x₀ i) = z₀ i)
    (i : ι) (x : X i) :
    mapCongr x₀ z₀ e he (inclusion x₀ i x) = inclusion z₀ i (e i x) := rfl

/-- Basepoint-preserving homeomorphisms on every summand induce a
homeomorphism of pointed wedges. This also handles an empty family. -/
def homeomorphCongr {Z : ι → Type w}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Z i)]
    (z₀ : ∀ i, Z i) (e : ∀ i, X i ≃ₜ Z i) (he : ∀ i, e i (x₀ i) = z₀ i) :
    Hatcher.PointedWedge X x₀ ≃ₜ Hatcher.PointedWedge Z z₀ := by
  have he_symm : ∀ i, (e i).symm (z₀ i) = x₀ i := by
    intro i
    rw [← he i]
    exact (e i).symm_apply_apply (x₀ i)
  exact
    { toEquiv :=
        { toFun := mapCongr x₀ z₀ e he
          invFun := mapCongr z₀ x₀ (fun i => (e i).symm) he_symm
          left_inv := by
            intro q
            induction q using Quotient.inductionOn with
            | _ q =>
                cases q with
                | none => rfl
                | some q =>
                    rcases q with ⟨i, x⟩
                    change mapCongr z₀ x₀ (fun i => (e i).symm) he_symm
                      (mapCongr x₀ z₀ e he (inclusion x₀ i x)) = inclusion x₀ i x
                    rw [mapCongr_inclusion, mapCongr_inclusion,
                      (e i).symm_apply_apply]
          right_inv := by
            intro q
            induction q using Quotient.inductionOn with
            | _ q =>
                cases q with
                | none => rfl
                | some q =>
                    rcases q with ⟨i, x⟩
                    change mapCongr x₀ z₀ e he
                      (mapCongr z₀ x₀ (fun i => (e i).symm) he_symm
                        (inclusion z₀ i x)) = inclusion z₀ i x
                    rw [mapCongr_inclusion, mapCongr_inclusion,
                      (e i).apply_symm_apply] }
      continuous_toFun := (mapCongr x₀ z₀ e he).continuous
      continuous_invFun := (mapCongr z₀ x₀ (fun i => (e i).symm) he_symm).continuous }

end Hatcher.PointedWedge
