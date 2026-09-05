import Hatcher.VanKampen.ConeAttachment
import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# The pushout universal property of a single cone attachment

This module exhibits `ConeAttachment f` as the pushout in `TopCat` of the
attaching map `f : S → X` and the retained-boundary inclusion of `S` into
the explicit cone `ConeAttachment id`. It also packages this pushout as a
one-cell `HomotopicalAlgebra.AttachCells` structure.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Set Topology
open scoped unitInterval

namespace Hatcher.VanKampen.ConeAttachment

universe u

theorem continuous_base {X S : Type u} [TopologicalSpace X]
    [TopologicalSpace S] (f : S → X) :
    Continuous (base f) := by
  change Continuous (fun x : X ↦ quotientMk f (Sum.inl x))
  exact (isQuotientMap_quotientMk f).continuous.comp continuous_inl

theorem continuous_cylinder {X S : Type u} [TopologicalSpace X]
    [TopologicalSpace S] (f : S → X) :
    Continuous (fun p : S × I ↦ cylinder f p.1 p.2) := by
  change Continuous (fun p : S × I ↦ quotientMk f (Sum.inr (Sum.inr p)))
  have hinner : Continuous (fun p : S × I ↦ (Sum.inr p : Unit ⊕ (S × I))) :=
    continuous_inr
  have houter : Continuous
      (fun p : Unit ⊕ (S × I) ↦ (Sum.inr p : Prequotient X S)) :=
    continuous_inr
  exact (isQuotientMap_quotientMk f).continuous.comp (houter.comp hinner)

private def coneRaw {X S : Type u} (f : S → X) :
    Prequotient S S → Hatcher.VanKampen.ConeAttachment f
  | Sum.inl s => base f (f s)
  | Sum.inr (Sum.inl _) => apex f
  | Sum.inr (Sum.inr (s, t)) => cylinder f s t

private theorem coneRaw_normalForm {X S : Type u} (f : S → X)
    (z : Prequotient S S) :
    coneRaw f (normalForm (id : S → S) z) = coneRaw f z := by
  rcases z with s | z
  · rfl
  · rcases z with u₀ | ⟨s, t⟩
    · rcases u₀ with ⟨⟩
      rfl
    · by_cases h0 : t = 0
      · subst t
        simp [normalForm, coneRaw]
      · by_cases h1 : t = 1
        · subst t
          simp [normalForm, coneRaw]
        · simp [normalForm, coneRaw, h0, h1]

/-- The canonical map from the retained cone to the cone attachment. -/
def coneMap {X S : Type u} (f : S → X) :
    Hatcher.VanKampen.ConeAttachment (id : S → S) →
      Hatcher.VanKampen.ConeAttachment f :=
  Quotient.lift (coneRaw f) (by
    intro a b hab
    change normalForm (id : S → S) a = normalForm id b at hab
    rw [← coneRaw_normalForm f a, ← coneRaw_normalForm f b, hab])

@[simp]
theorem coneMap_base {X S : Type u} (f : S → X) (s : S) :
    coneMap f (base id s) = base f (f s) := rfl

@[simp]
theorem coneMap_apex {X S : Type u} (f : S → X) :
    coneMap f (apex id) = apex f := rfl

@[simp]
theorem coneMap_cylinder {X S : Type u} (f : S → X) (s : S) (t : I) :
    coneMap f (cylinder id s t) = cylinder f s t := rfl

theorem continuous_coneMap {X S : Type u} [TopologicalSpace X]
    [TopologicalSpace S] (f : S → X) (hf : Continuous f) :
    Continuous (coneMap f) := by
  apply (isQuotientMap_quotientMk (id : S → S)).continuous_iff.mpr
  rw [continuous_sum_dom]
  constructor
  · simpa [coneMap, coneRaw, quotientMk, Function.comp_def] using
      (continuous_base f).comp hf
  · rw [continuous_sum_dom]
    constructor
    · simpa [coneMap, coneRaw, quotientMk, Function.comp_def] using
        (continuous_const : Continuous (fun _ : Unit ↦ apex f))
    · simpa [coneMap, coneRaw, quotientMk, Function.comp_def] using
        continuous_cylinder f

private def descRaw {X S Z : Type u} (h : X → Z)
    (k : Hatcher.VanKampen.ConeAttachment (id : S → S) → Z) :
    Prequotient X S → Z
  | Sum.inl x => h x
  | Sum.inr (Sum.inl _) => k (apex id)
  | Sum.inr (Sum.inr (s, t)) => k (cylinder id s t)

private theorem descRaw_normalForm {X S Z : Type u} (f : S → X)
    (h : X → Z)
    (k : Hatcher.VanKampen.ConeAttachment (id : S → S) → Z)
    (w : ∀ s, h (f s) = k (base id s)) (z : Prequotient X S) :
    descRaw h k (normalForm f z) = descRaw h k z := by
  rcases z with x | z
  · rfl
  · rcases z with u₀ | ⟨s, t⟩
    · rcases u₀ with ⟨⟩
      rfl
    · by_cases h0 : t = 0
      · subst t
        simp [normalForm, descRaw]
      · by_cases h1 : t = 1
        · subst t
          simpa [normalForm, descRaw] using w s
        · simp [normalForm, descRaw, h0, h1]

/-- The map out of a cone attachment induced by compatible maps out of its
base and retained cone. -/
def desc {X S Z : Type u} (f : S → X)
    (h : X → Z)
    (k : Hatcher.VanKampen.ConeAttachment (id : S → S) → Z)
    (w : ∀ s, h (f s) = k (base id s)) :
    Hatcher.VanKampen.ConeAttachment f → Z :=
  Quotient.lift (descRaw h k) (by
    intro a b hab
    change normalForm f a = normalForm f b at hab
    rw [← descRaw_normalForm f h k w a, ← descRaw_normalForm f h k w b, hab])

@[simp]
theorem desc_base {X S Z : Type u} (f : S → X)
    (h : X → Z)
    (k : Hatcher.VanKampen.ConeAttachment (id : S → S) → Z)
    (w : ∀ s, h (f s) = k (base id s)) (x : X) :
    desc f h k w (base f x) = h x := rfl

@[simp]
theorem desc_apex {X S Z : Type u} (f : S → X)
    (h : X → Z)
    (k : Hatcher.VanKampen.ConeAttachment (id : S → S) → Z)
    (w : ∀ s, h (f s) = k (base id s)) :
    desc f h k w (apex f) = k (apex id) := rfl

@[simp]
theorem desc_cylinder {X S Z : Type u} (f : S → X)
    (h : X → Z)
    (k : Hatcher.VanKampen.ConeAttachment (id : S → S) → Z)
    (w : ∀ s, h (f s) = k (base id s)) (s : S) (t : I) :
    desc f h k w (cylinder f s t) = k (cylinder id s t) := rfl

theorem continuous_desc {X S Z : Type u} [TopologicalSpace X]
    [TopologicalSpace S] [TopologicalSpace Z] (f : S → X)
    (h : X → Z)
    (k : Hatcher.VanKampen.ConeAttachment (id : S → S) → Z)
    (w : ∀ s, h (f s) = k (base id s)) (hh : Continuous h)
    (hk : Continuous k) :
    Continuous (desc f h k w) := by
  apply (isQuotientMap_quotientMk f).continuous_iff.mpr
  rw [continuous_sum_dom]
  constructor
  · simpa [desc, descRaw, quotientMk, Function.comp_def] using hh
  · rw [continuous_sum_dom]
    constructor
    · simpa [desc, descRaw, quotientMk, Function.comp_def] using
        (continuous_const : Continuous (fun _ : Unit ↦ k (apex id)))
    · simpa [desc, descRaw, quotientMk, Function.comp_def] using
        hk.comp (continuous_cylinder (id : S → S))

/-- The attaching map as a morphism of topological spaces. -/
def attachingHom {X S : Type u} [TopologicalSpace X] [TopologicalSpace S]
    (f : S → X) (hf : Continuous f) : TopCat.of S ⟶ TopCat.of X :=
  TopCat.ofHom ⟨f, hf⟩

/-- The retained boundary of the explicit cone. -/
def coneBoundaryHom (S : Type u) [TopologicalSpace S] :
    TopCat.of S ⟶
      TopCat.of (Hatcher.VanKampen.ConeAttachment (id : S → S)) :=
  TopCat.ofHom ⟨base id, continuous_base id⟩

/-- The original space inside its cone attachment. -/
def baseHom {X S : Type u} [TopologicalSpace X] [TopologicalSpace S]
    (f : S → X) :
    TopCat.of X ⟶ TopCat.of (Hatcher.VanKampen.ConeAttachment f) :=
  TopCat.ofHom ⟨base f, continuous_base f⟩

/-- The explicit cone inside a cone attachment. -/
def coneHom {X S : Type u} [TopologicalSpace X] [TopologicalSpace S]
    (f : S → X) (hf : Continuous f) :
    TopCat.of (Hatcher.VanKampen.ConeAttachment (id : S → S)) ⟶
      TopCat.of (Hatcher.VanKampen.ConeAttachment f) :=
  TopCat.ofHom ⟨coneMap f, continuous_coneMap f hf⟩

/-- The explicit single-cone attachment is the pushout of its attaching map
and the retained-boundary inclusion into the explicit cone. -/
theorem isPushout_coneAttachment {X S : Type u}
    [TopologicalSpace X] [TopologicalSpace S]
    (f : S → X) (hf : Continuous f) :
    IsPushout (attachingHom f hf) (coneBoundaryHom S)
      (baseHom f) (coneHom f hf) := by
  have comm : attachingHom f hf ≫ baseHom f =
      coneBoundaryHom S ≫ coneHom f hf := by
    ext s
    rfl
  let d (c : PushoutCocone (attachingHom f hf) (coneBoundaryHom S)) :
      TopCat.of (Hatcher.VanKampen.ConeAttachment f) ⟶ c.pt :=
    let w : ∀ s : S, c.inl (f s) = c.inr (base id s) := fun s ↦
      ConcreteCategory.congr_hom c.condition s
    TopCat.ofHom ⟨desc f c.inl c.inr w,
      continuous_desc f c.inl c.inr w
        c.inl.hom.continuous c.inr.hom.continuous⟩
  refine { w := comm, isColimit' := ⟨?_⟩ }
  refine PushoutCocone.IsColimit.mk comm d ?_ ?_ ?_
  · intro c
    ext x
    rfl
  · intro c
    let w : ∀ s : S, c.inl (f s) = c.inr (base id s) := fun s ↦
      ConcreteCategory.congr_hom c.condition s
    ext q
    refine Quotient.inductionOn q ?_
    intro z
    rcases z with s | z
    · exact w s
    · rcases z with u₀ | ⟨s, t⟩
      · rfl
      · rfl
  · intro c m hmBase hmCone
    ext q
    refine Quotient.inductionOn q ?_
    intro z
    rcases z with x | z
    · exact ConcreteCategory.congr_hom hmBase x
    · rcases z with u₀ | ⟨s, t⟩
      · exact ConcreteCategory.congr_hom hmCone (apex id)
      · exact ConcreteCategory.congr_hom hmCone (cylinder id s t)

private def unitCofan (Y : TopCat.{u}) : Cofan (fun _ : Unit ↦ Y) :=
  Cofan.mk Y (fun _ ↦ 𝟙 Y)

private def unitCofanIsColimit (Y : TopCat.{u}) :
    IsColimit (unitCofan Y) :=
  Cofan.isColimitMkOfUnique (Iso.refl Y) Unit

/-- The pushout theorem supplies the one-cell `AttachCells` structure whose
cell type is the retained-boundary inclusion into the explicit cone. -/
def attachCells_coneAttachment {X S : Type u}
    [TopologicalSpace X] [TopologicalSpace S]
    (f : S → X) (hf : Continuous f) :
    HomotopicalAlgebra.AttachCells.{0}
      (A := fun _ : Unit ↦ TopCat.of S)
      (B := fun _ : Unit ↦
        TopCat.of (Hatcher.VanKampen.ConeAttachment (id : S → S)))
      (fun _ ↦ coneBoundaryHom S) (baseHom f) where
  ι := Unit
  π := id
  cofan₁ := unitCofan (TopCat.of S)
  cofan₂ := unitCofan
    (TopCat.of (Hatcher.VanKampen.ConeAttachment (id : S → S)))
  isColimit₁ := unitCofanIsColimit _
  isColimit₂ := unitCofanIsColimit _
  m := coneBoundaryHom S
  hm i := by
    rcases i with ⟨⟩
    change 𝟙 (TopCat.of S) ≫ coneBoundaryHom S =
      coneBoundaryHom S ≫
        𝟙 (TopCat.of (Hatcher.VanKampen.ConeAttachment (id : S → S)))
    simp
  g₁ := attachingHom f hf
  g₂ := coneHom f hf
  isPushout := isPushout_coneAttachment f hf

end Hatcher.VanKampen.ConeAttachment
