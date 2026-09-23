import Mathlib.Data.Setoid.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Constructions

namespace Hatcher

universe u v

namespace PointedWedge

/-- The generating relation that identifies the extra point with every chosen
basepoint. -/
inductive Rel {ι : Type u} (X : ι → Type v) (x₀ : ∀ i, X i) :
    Option (Σ i, X i) → Option (Σ i, X i) → Prop where
  | base (i : ι) : Rel X x₀ none (some ⟨i, x₀ i⟩)

/-- The smallest equivalence relation identifying all chosen basepoints with
the extra point. -/
def setoid {ι : Type u} (X : ι → Type v) (x₀ : ∀ i, X i) :
    Setoid (Option (Σ i, X i)) :=
  Relation.EqvGen.setoid (Rel X x₀)

end PointedWedge

/-- The pointed wedge of a family, represented as the quotient of an optional
dependent sum by identification of all chosen basepoints with `none`. -/
def PointedWedge {ι : Type u} (X : ι → Type v) (x₀ : ∀ i, X i) :
    Type (max u v) :=
  Quotient (PointedWedge.setoid X x₀)

namespace PointedWedge

variable {ι : Type u} {X : ι → Type v} (x₀ : ∀ i, X i)

/-- The coproduct topology on the prequotient `Option (Σ i, X i)`. -/
@[reducible]
def prequotientTopology [∀ i, TopologicalSpace (X i)] :
    TopologicalSpace (Option (Σ i, X i)) :=
  TopologicalSpace.coinduced (fun z : Σ i, X i => some z) inferInstance ⊔
    TopologicalSpace.coinduced (fun _ : Unit => (none : Option (Σ i, X i))) inferInstance

/-- The quotient topology on the pointed wedge. -/
instance instTopologicalSpace [∀ i, TopologicalSpace (X i)] :
    TopologicalSpace (Hatcher.PointedWedge X x₀) :=
  TopologicalSpace.coinduced
    (Quotient.mk (PointedWedge.setoid X x₀) :
      Option (Σ i, X i) → Hatcher.PointedWedge X x₀)
    (prequotientTopology (X := X))

/-- The common basepoint of the pointed wedge. -/
def basepoint : Hatcher.PointedWedge X x₀ :=
  Quotient.mk (PointedWedge.setoid X x₀) none

/-- The canonical inclusion of one summand into the pointed wedge. -/
def inclusion (i : ι) : X i → Hatcher.PointedWedge X x₀ :=
  fun x => Quotient.mk (PointedWedge.setoid X x₀) (some ⟨i, x⟩)

private theorem continuous_some_sigma [∀ i, TopologicalSpace (X i)] (i : ι) :
    @Continuous (X i) (Option (Σ i, X i)) _ (prequotientTopology (X := X))
      (fun x => some ⟨i, x⟩) := by
  letI : TopologicalSpace (Option (Σ i, X i)) :=
    TopologicalSpace.coinduced (fun z : Σ i, X i => some z) inferInstance
  have h : Continuous (fun x : X i => some (Sigma.mk i x)) :=
    continuous_coinduced_rng.comp continuous_sigmaMk
  exact continuous_sup_rng_left h

private theorem continuous_mk [∀ i, TopologicalSpace (X i)] :
    @Continuous (Option (Σ i, X i)) (Hatcher.PointedWedge X x₀)
      (prequotientTopology (X := X)) (instTopologicalSpace x₀)
      (Quotient.mk (PointedWedge.setoid X x₀)) :=
  continuous_coinduced_rng

/-- Each canonical summand inclusion is continuous. -/
theorem continuous_inclusion [∀ i, TopologicalSpace (X i)] (i : ι) :
    Continuous (inclusion x₀ i) := by
  letI : TopologicalSpace (Option (Σ i, X i)) := prequotientTopology (X := X)
  change Continuous (fun x : X i =>
    Quotient.mk (PointedWedge.setoid X x₀) (some ⟨i, x⟩))
  exact (continuous_mk (X := X) x₀).comp (continuous_some_sigma (X := X) i)

/-- Every chosen summand basepoint maps to the wedge basepoint. -/
@[simp]
theorem inclusion_basepoint (i : ι) :
    inclusion x₀ i (x₀ i) = basepoint x₀ := by
  change Quotient.mk (PointedWedge.setoid X x₀) (some ⟨i, x₀ i⟩) =
    Quotient.mk (PointedWedge.setoid X x₀) none
  exact Quotient.sound <| Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _ (Rel.base (X := X) (x₀ := x₀) i))

/-- A pointed wedge of path-connected spaces is path-connected, including
the empty wedge, which is represented by its extra basepoint. -/
instance instPathConnectedSpace [∀ i, TopologicalSpace (X i)]
    [∀ i, PathConnectedSpace (X i)] :
    PathConnectedSpace (Hatcher.PointedWedge X x₀) := by
  constructor
  · exact ⟨basepoint x₀⟩
  · intro p q
    have hbase : ∀ z : Hatcher.PointedWedge X x₀, Joined z (basepoint x₀) := by
      intro z
      induction z using Quotient.inductionOn with
      | _ z =>
        cases z with
        | none => exact Joined.refl _
        | some z =>
          rcases z with ⟨i, x⟩
          rcases PathConnectedSpace.joined x (x₀ i) with ⟨γ⟩
          exact ⟨(γ.map (continuous_inclusion x₀ i)).cast rfl
            (inclusion_basepoint x₀ i).symm⟩
    exact (hbase p).trans (hbase q).symm

end PointedWedge

end Hatcher
