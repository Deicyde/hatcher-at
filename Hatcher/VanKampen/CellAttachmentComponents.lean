import Hatcher.VanKampen.AuxiliaryCellAttachmentDeformation
import Hatcher.VanKampen.CellAttachmentEmpty
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Subpath

/-!
# Path components after attaching higher-dimensional cells

This file proves that attaching cells of dimension greater than one neither
merges path components of the source nor creates target components disjoint
from the source.
-/

noncomputable section

open CategoryTheory HomotopicalAlgebra Set Topology
open scoped ContinuousMap TopCat unitInterval

namespace Hatcher

universe u

namespace VanKampen.CellAttachmentComponent

variable {X J : Type u} {S : J → Type u}
variable [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]

private def componentLabelRaw (f : ∀ j, S j → X) (s₀ : ∀ j, S j) :
    IndexedConeAttachment.Prequotient X S → ZerothHomotopy X
  | Sum.inl x => ZerothHomotopy.mk x
  | Sum.inr ⟨j, _⟩ => ZerothHomotopy.mk (f j (s₀ j))

private theorem componentLabelRaw_normalForm
    (f : ∀ j, S j → X) (hf : ∀ j, Continuous (f j))
    (s₀ : ∀ j, S j) [∀ j, PathConnectedSpace (S j)]
    (z : IndexedConeAttachment.Prequotient X S) :
    componentLabelRaw f s₀ (IndexedConeAttachment.normalForm f z) =
      componentLabelRaw f s₀ z := by
  rcases z with x | ⟨j, z⟩
  · rfl
  · rcases z with u | ⟨s, t⟩
    · rfl
    · by_cases h0 : t = 0
      · subst t
        simp [IndexedConeAttachment.normalForm, componentLabelRaw]
      · by_cases h1 : t = 1
        · subst t
          simp only [IndexedConeAttachment.normalForm, one_ne_zero, if_false,
            if_pos, componentLabelRaw]
          exact ZerothHomotopy.sound
            ((PathConnectedSpace.somePath s (s₀ j)).map (hf j))
        · simp [IndexedConeAttachment.normalForm, componentLabelRaw, h0, h1]

private def componentLabel (f : ∀ j, S j → X)
    (hf : ∀ j, Continuous (f j)) (s₀ : ∀ j, S j)
    [∀ j, PathConnectedSpace (S j)] :
    IndexedConeAttachment f → ZerothHomotopy X :=
  Quotient.lift (componentLabelRaw f s₀) (by
    intro a b hab
    change IndexedConeAttachment.normalForm f a =
      IndexedConeAttachment.normalForm f b at hab
    rw [← componentLabelRaw_normalForm f hf s₀ a,
      ← componentLabelRaw_normalForm f hf s₀ b, hab])

@[simp] private theorem componentLabel_base
    (f : ∀ j, S j → X) (hf : ∀ j, Continuous (f j))
    (s₀ : ∀ j, S j) [∀ j, PathConnectedSpace (S j)] (x : X) :
    componentLabel f hf s₀ (IndexedConeAttachment.base f x) =
      ZerothHomotopy.mk x := rfl

@[simp] private theorem componentLabel_cylinder
    (f : ∀ j, S j → X) (hf : ∀ j, Continuous (f j))
    (s₀ : ∀ j, S j) [∀ j, PathConnectedSpace (S j)]
    (j : J) (s : S j) (t : I) :
    componentLabel f hf s₀ (IndexedConeAttachment.cylinder f j s t) =
      ZerothHomotopy.mk (f j (s₀ j)) := rfl

private def upperLabelRaw (f : ∀ j, S j → X) (s₀ : ∀ j, S j)
    (j₀ : J) : IndexedConeAttachment.Prequotient X S →
      WithDiscreteTopology (ZerothHomotopy X)
  | Sum.inl _ => WithTopology.toTopology ⊥
      (ZerothHomotopy.mk (f j₀ (s₀ j₀)))
  | Sum.inr ⟨j, _⟩ => WithTopology.toTopology ⊥
      (ZerothHomotopy.mk (f j (s₀ j)))

private theorem continuous_upperLabelRaw
    (f : ∀ j, S j → X) (s₀ : ∀ j, S j) (j₀ : J) :
    Continuous (upperLabelRaw f s₀ j₀) := by
  rw [continuous_sum_dom]
  constructor
  · exact continuous_const
  · rw [continuous_sigma_iff]
    intro j
    exact continuous_const

omit [∀ j, TopologicalSpace (S j)] in
private theorem upperLabelRaw_normalForm
    (f : ∀ j, S j → X) (s₀ : ∀ j, S j) (j₀ : J)
    (z : IndexedConeAttachment.Prequotient X S)
    (hz : IndexedConeAttachment.quotientMk f z ∈
      IndexedConeAttachment.upperCover f) :
    upperLabelRaw f s₀ j₀ (IndexedConeAttachment.normalForm f z) =
      upperLabelRaw f s₀ j₀ z := by
  rcases z with x | ⟨j, z⟩
  · exact False.elim (IndexedConeAttachment.base_not_mem_upperCover f x hz)
  · rcases z with u | ⟨s, t⟩
    · rfl
    · have ht : t < 1 :=
        (IndexedConeAttachment.cylinder_mem_upperCover_iff f j s t).mp hz
      by_cases h0 : t = 0
      · subst t
        simp [IndexedConeAttachment.normalForm, upperLabelRaw]
      · by_cases h1 : t = 1
        · subst t
          exact False.elim (lt_irrefl (1 : I) ht)
        · simp [IndexedConeAttachment.normalForm, upperLabelRaw, h0, h1]

private theorem indexedUpperQuotientMap (f : ∀ j, S j → X) :
    IsQuotientMap ((IndexedConeAttachment.upperCover f).restrictPreimage
      (IndexedConeAttachment.quotientMk f)) := by
  exact (isQuotientMap_quot_mk : IsQuotientMap
    (IndexedConeAttachment.quotientMk f)).restrictPreimage_isOpen
      (IndexedConeAttachment.isOpenCover_lower_upper f).2.1

private def upperLabelPre (f : ∀ j, S j → X) (s₀ : ∀ j, S j)
    (j₀ : J) :
    (IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.upperCover f) →
      WithDiscreteTopology (ZerothHomotopy X) :=
  fun z => upperLabelRaw f s₀ j₀ z.1

private theorem continuous_upperLabelPre
    (f : ∀ j, S j → X) (s₀ : ∀ j, S j) (j₀ : J) :
    Continuous (upperLabelPre f s₀ j₀) :=
  (continuous_upperLabelRaw f s₀ j₀).comp continuous_subtype_val

omit [∀ j, TopologicalSpace (S j)] in
private theorem upperLabelPre_eq_of_quotient_eq
    (f : ∀ j, S j → X) (s₀ : ∀ j, S j) (j₀ : J)
    {a b : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.upperCover f}
    (h : (IndexedConeAttachment.upperCover f).restrictPreimage
        (IndexedConeAttachment.quotientMk f) a =
      (IndexedConeAttachment.upperCover f).restrictPreimage
        (IndexedConeAttachment.quotientMk f) b) :
    upperLabelPre f s₀ j₀ a = upperLabelPre f s₀ j₀ b := by
  have hrel := Quotient.exact (congrArg Subtype.val h)
  change IndexedConeAttachment.normalForm f a.1 =
    IndexedConeAttachment.normalForm f b.1 at hrel
  change upperLabelRaw f s₀ j₀ a.1 = upperLabelRaw f s₀ j₀ b.1
  rw [← upperLabelRaw_normalForm f s₀ j₀ a.1 a.2,
    ← upperLabelRaw_normalForm f s₀ j₀ b.1 b.2, hrel]

private noncomputable def upperLabel (f : ∀ j, S j → X)
    (s₀ : ∀ j, S j) (j₀ : J) :
    IndexedConeAttachment.upperCover f →
      WithDiscreteTopology (ZerothHomotopy X) := fun z =>
  upperLabelPre f s₀ j₀
    (Function.surjInv (indexedUpperQuotientMap f).surjective z)

private theorem upperLabel_quotientMap
    (f : ∀ j, S j → X) (s₀ : ∀ j, S j) (j₀ : J)
    (z : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.upperCover f) :
    upperLabel f s₀ j₀
        ((IndexedConeAttachment.upperCover f).restrictPreimage
          (IndexedConeAttachment.quotientMk f) z) =
      upperLabelPre f s₀ j₀ z := by
  apply upperLabelPre_eq_of_quotient_eq f s₀ j₀
  exact Function.surjInv_eq (indexedUpperQuotientMap f).surjective _

private theorem continuous_upperLabel
    (f : ∀ j, S j → X) (s₀ : ∀ j, S j) (j₀ : J) :
    Continuous (upperLabel f s₀ j₀) := by
  apply (indexedUpperQuotientMap f).continuous_iff.mpr
  apply (continuous_upperLabelPre f s₀ j₀).congr
  intro z
  exact (upperLabel_quotientMap f s₀ j₀ z).symm

private theorem upperLabel_eq_componentLabel
    (f : ∀ j, S j → X) (hf : ∀ j, Continuous (f j))
    (s₀ : ∀ j, S j) [∀ j, PathConnectedSpace (S j)] (j₀ : J)
    (z : IndexedConeAttachment.upperCover f) :
    (upperLabel f s₀ j₀ z).ofTopology = componentLabel f hf s₀ z.1 := by
  obtain ⟨a, rfl⟩ := (indexedUpperQuotientMap f).surjective z
  rw [upperLabel_quotientMap]
  rcases a with ⟨x | ⟨j, (_ | ⟨s, t⟩)⟩, ha⟩
  · exact False.elim (IndexedConeAttachment.base_not_mem_upperCover f x ha)
  · rfl
  · rfl

private theorem componentLabel_eq_mk_lower
    (f : ∀ j, S j → X) (hf : ∀ j, Continuous (f j))
    (s₀ : ∀ j, S j) [∀ j, PathConnectedSpace (S j)]
    (z : IndexedConeAttachment.lowerCover f) :
    componentLabel f hf s₀ z.1 = ZerothHomotopy.mk
      (AuxiliaryCellAttachment.indexedLowerCoverRetraction f hf z) := by
  obtain ⟨a, rfl⟩ :=
    (IndexedConeAttachment.isQuotientMap_restrictPreimage_lowerCover f).surjective z
  rcases a with ⟨x | ⟨j, (_ | ⟨s, t⟩)⟩, ha⟩
  · change componentLabel f hf s₀ (IndexedConeAttachment.base f x) =
      ZerothHomotopy.mk
        (AuxiliaryCellAttachment.indexedLowerCoverRetraction f hf
          ⟨IndexedConeAttachment.base f x, ha⟩)
    rw [componentLabel_base,
      AuxiliaryCellAttachment.indexedLowerCoverRetraction_base]
  · exact False.elim (IndexedConeAttachment.apex_not_mem_lowerCover f j ha)
  · have ht : 0 < t :=
      (IndexedConeAttachment.cylinder_mem_lowerCover_iff f j s t).mp ha
    change componentLabel f hf s₀
        (IndexedConeAttachment.cylinder f j s t) =
      ZerothHomotopy.mk
        (AuxiliaryCellAttachment.indexedLowerCoverRetraction f hf
          ⟨IndexedConeAttachment.cylinder f j s t, ha⟩)
    rw [componentLabel_cylinder,
      AuxiliaryCellAttachment.indexedLowerCoverRetraction_cylinder
        f hf j s t ht]
    exact ZerothHomotopy.sound
      ((PathConnectedSpace.somePath (s₀ j) s).map (hf j))

private theorem componentLabel_eq_of_joinedIn_lower
    (f : ∀ j, S j → X) (hf : ∀ j, Continuous (f j))
    (s₀ : ∀ j, S j) [∀ j, PathConnectedSpace (S j)]
    {a b : IndexedConeAttachment f}
    (h : JoinedIn (IndexedConeAttachment.lowerCover f) a b) :
    componentLabel f hf s₀ a = componentLabel f hf s₀ b := by
  let r := AuxiliaryCellAttachment.indexedLowerCoverRetraction f hf
  have hp : ZerothHomotopy.mk (r ⟨a, h.source_mem⟩) =
      ZerothHomotopy.mk (r ⟨b, h.target_mem⟩) :=
    ZerothHomotopy.sound (h.joined_subtype.somePath.map r.continuous)
  rw [componentLabel_eq_mk_lower f hf s₀ ⟨a, h.source_mem⟩,
    componentLabel_eq_mk_lower f hf s₀ ⟨b, h.target_mem⟩]
  exact hp

private theorem componentLabel_eq_of_joinedIn_upper
    (f : ∀ j, S j → X) (hf : ∀ j, Continuous (f j))
    (s₀ : ∀ j, S j) [∀ j, PathConnectedSpace (S j)]
    (j₀ : J) {a b : IndexedConeAttachment f}
    (h : JoinedIn (IndexedConeAttachment.upperCover f) a b) :
    componentLabel f hf s₀ a = componentLabel f hf s₀ b := by
  let p := h.joined_subtype.somePath.map (continuous_upperLabel f s₀ j₀)
  have hpconn : IsPreconnected (Set.range p) := isPreconnected_range p.continuous
  have hp : p 0 = p 1 := hpconn.subsingleton ⟨0, rfl⟩ ⟨1, rfl⟩
  have hp' := congrArg WithTopology.ofTopology hp
  simpa [p, upperLabel_eq_componentLabel f hf s₀ j₀] using hp'

private theorem exists_partition_path_of_open_cover
    {ι A : Type*} [TopologicalSpace A] {c : ι → Set A} {a b : A}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : Set.univ ⊆ ⋃ i, c i)
    (γ : Path a b) : ∃ (n : ℕ) (t : Fin (n + 2) → I),
    t 0 = 0 ∧ t (Fin.last (n + 1)) = 1 ∧
      ∀ k : Fin (n + 1), ∃ i,
        γ '' Set.uIcc (t k.castSucc) (t k.succ) ⊆ c i := by
  have ⟨t, ht₀, ht_mono, ⟨n, ht₁⟩, ht_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => IsOpen.preimage γ.continuous (hc₁ i))
      (fun _ _ => (preimage_iUnion ▸ hc₂ (Set.mem_univ _)))
  use n, t ∘ Fin.toNat
  suffices ∀ k : Fin (n + 1), ∃ i,
      Set.uIcc (t ↑k) (t (↑k + 1)) ⊆ γ ⁻¹' c i by
    simpa [ht₀, ht₁]
  intro k
  obtain ⟨i, hi⟩ := ht_sub k
  use i
  rwa [Set.uIcc_of_le (ht_mono (Nat.le_add_right _ _))]

private def binaryConeCover (f : ∀ j, S j → X) :
    Fin 2 → Set (IndexedConeAttachment f) :=
  Fin.cases (IndexedConeAttachment.lowerCover f)
    (fun _ => IndexedConeAttachment.upperCover f)

private theorem binaryConeCover_open (f : ∀ j, S j → X) (i : Fin 2) :
    IsOpen (binaryConeCover f i) := by
  fin_cases i
  · exact (IndexedConeAttachment.isOpenCover_lower_upper f).1
  · exact (IndexedConeAttachment.isOpenCover_lower_upper f).2.1

private theorem binaryConeCover_covers (f : ∀ j, S j → X) :
    Set.univ ⊆ ⋃ i, binaryConeCover f i := by
  intro z _
  have hz : z ∈ IndexedConeAttachment.lowerCover f ∪
      IndexedConeAttachment.upperCover f := by
    rw [(IndexedConeAttachment.isOpenCover_lower_upper f).2.2]
    trivial
  rcases hz with hz | hz
  · exact Set.mem_iUnion.mpr ⟨0, hz⟩
  · exact Set.mem_iUnion.mpr ⟨1, hz⟩

private theorem componentLabel_eq_of_joined
    (f : ∀ j, S j → X) (hf : ∀ j, Continuous (f j))
    (s₀ : ∀ j, S j) [∀ j, PathConnectedSpace (S j)] (j₀ : J)
    {a b : IndexedConeAttachment f} (h : Joined a b) :
    componentLabel f hf s₀ a = componentLabel f hf s₀ b := by
  let γ := h.somePath
  obtain ⟨n, t, ht0, ht1, hsub⟩ :=
    exists_partition_path_of_open_cover (binaryConeCover_open f)
      (binaryConeCover_covers f) γ
  have hstep : ∀ k : Fin (n + 1),
      componentLabel f hf s₀ (γ (t k.castSucc)) =
        componentLabel f hf s₀ (γ (t k.succ)) := by
    intro k
    obtain ⟨i, hi⟩ := hsub k
    have hjoined : JoinedIn (binaryConeCover f i)
        (γ (t k.castSucc)) (γ (t k.succ)) := by
      refine ⟨γ.subpath (t k.castSucc) (t k.succ), ?_⟩
      intro v
      apply hi
      rw [← Path.range_subpath]
      exact Set.mem_range_self v
    fin_cases i
    · exact componentLabel_eq_of_joinedIn_lower f hf s₀ hjoined
    · exact componentLabel_eq_of_joinedIn_upper f hf s₀ j₀ hjoined
  have hchain : ∀ k : Fin (n + 2),
      componentLabel f hf s₀ (γ (t 0)) =
        componentLabel f hf s₀ (γ (t k)) := by
    intro k
    induction k using Fin.induction with
    | zero => rfl
    | succ k ih => exact ih.trans (hstep k)
  have hend := hchain (Fin.last (n + 1))
  simpa [ht0, ht1, γ.source, γ.target] using hend

private theorem joined_base_iff
    (f : ∀ j, S j → X) (hf : ∀ j, Continuous (f j))
    (s₀ : ∀ j, S j) [∀ j, PathConnectedSpace (S j)] (j₀ : J)
    (x y : X) :
    Joined (IndexedConeAttachment.base f x)
        (IndexedConeAttachment.base f y) ↔ Joined x y := by
  constructor
  · intro h
    have hlabel := componentLabel_eq_of_joined f hf s₀ j₀ h
    rw [componentLabel_base, componentLabel_base] at hlabel
    exact Quotient.exact hlabel
  · intro h
    exact ⟨h.somePath.map (IndexedConeAttachment.continuous_base f)⟩

private theorem exists_joined_base (f : ∀ j, S j → X) (s₀ : ∀ j, S j)
    (z : IndexedConeAttachment f) :
    ∃ x : X, Joined z (IndexedConeAttachment.base f x) := by
  induction z using Quotient.inductionOn with
  | _ z =>
    rcases z with x | ⟨j, z⟩
    · exact ⟨x, Joined.refl _⟩
    · rcases z with u | ⟨s, t⟩
      · refine ⟨f j (s₀ j), ?_⟩
        let p : Path (IndexedConeAttachment.apex f j)
            (IndexedConeAttachment.base f (f j (s₀ j))) :=
          { toFun := fun t => IndexedConeAttachment.cylinder f j (s₀ j) t
            continuous_toFun := (IndexedConeAttachment.continuous_cylinder f j).comp
              (continuous_const.prodMk continuous_id)
            source' := IndexedConeAttachment.cylinder_zero f j (s₀ j)
            target' := IndexedConeAttachment.cylinder_one f j (s₀ j) }
        exact ⟨p⟩
      · refine ⟨f j s, ?_⟩
        let p : Path (IndexedConeAttachment.cylinder f j s t)
            (IndexedConeAttachment.base f (f j s)) :=
          { toFun := fun v => IndexedConeAttachment.cylinder f j s
              (Set.Icc.convexComb t 1 v)
            continuous_toFun := (IndexedConeAttachment.continuous_cylinder f j).comp
              (continuous_const.prodMk (Set.Icc.continuous_convexComb t 1))
            source' := by simp
            target' := by simp }
        exact ⟨p⟩

private theorem boundary_pathConnectedSpace {n : ℕ} (hn : 1 < n) :
    PathConnectedSpace
      (((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u)) := by
  letI : PathConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [← isPathConnected_iff_pathConnectedSpace]
    apply isPathConnected_sphere
    · rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      exact_mod_cast hn
    · exact zero_le_one
  change PathConnectedSpace
    (ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
  exact ULift.up_surjective.pathConnectedSpace continuous_uliftUp

end VanKampen.CellAttachmentComponent

open VanKampen

/-- Attaching cells of dimension greater than one does not merge path
components of the source. -/
theorem joined_iff_of_attachCells_of_one_lt
    {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (hn : 1 < n) (x y : X) : Joined (f x) (f y) ↔ Joined x y := by
  classical
  by_cases hι : Nonempty c.ι
  · letI := hι
    letI : PathConnectedSpace
        (((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u)) :=
      CellAttachmentComponent.boundary_pathConnectedSpace hn
    let s₀ : ∀ _ : c.ι,
        ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u) :=
      fun _ => Classical.arbitrary _
    let j₀ : c.ι := Classical.arbitrary _
    constructor
    · intro h
      have h' : Joined
          ((CellAttachment.modelIso c).hom (f x))
          ((CellAttachment.modelIso c).hom (f y)) :=
        ⟨h.somePath.map (CellAttachment.modelIso c).hom.hom.continuous⟩
      have hx : (CellAttachment.modelIso c).hom (f x) =
          IndexedConeAttachment.base (CellAttachment.attachingMap c) x :=
        ConcreteCategory.congr_hom (CellAttachment.f_modelIso_hom c) x
      have hy : (CellAttachment.modelIso c).hom (f y) =
          IndexedConeAttachment.base (CellAttachment.attachingMap c) y :=
        ConcreteCategory.congr_hom (CellAttachment.f_modelIso_hom c) y
      rw [hx, hy] at h'
      exact (CellAttachmentComponent.joined_base_iff
        (CellAttachment.attachingMap c)
        (CellAttachment.continuous_attachingMap c) s₀ j₀ x y).mp h'
    · intro h
      exact ⟨h.somePath.map f.hom.continuous⟩
  · letI : IsEmpty c.ι := ⟨fun i => hι ⟨i⟩⟩
    constructor
    · intro h
      let e := CellAttachment.targetIsoOfIsEmpty c
      have h' : Joined (e.hom (f x)) (e.hom (f y)) :=
        ⟨h.somePath.map e.hom.hom.continuous⟩
      have hx : e.hom (f x) = x :=
        ConcreteCategory.congr_hom
          (CellAttachment.f_targetIsoOfIsEmpty_hom c) x
      have hy : e.hom (f y) = y :=
        ConcreteCategory.congr_hom
          (CellAttachment.f_targetIsoOfIsEmpty_hom c) y
      rwa [hx, hy] at h'
    · intro h
      exact ⟨h.somePath.map f.hom.continuous⟩

/-- Attaching cells of dimension greater than two to a path-connected space
produces a path-connected target. -/
theorem pathConnectedSpace_of_attachCells_of_two_lt
    {n : ℕ} {X Y : TopCat.{u}} {f : X ⟶ Y} [PathConnectedSpace X]
    (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell.{u} n) f)
    (hn : 2 < n) : PathConnectedSpace Y := by
  letI : PathConnectedSpace
      (((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u)) :=
    CellAttachmentComponent.boundary_pathConnectedSpace (by omega)
  let s₀ : ∀ _ : c.ι,
      ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u) :=
    fun _ => Classical.arbitrary _
  constructor
  · exact ⟨f (Classical.arbitrary X)⟩
  · intro y₁ y₂
    let e := CellAttachment.modelIso c
    obtain ⟨x₁, h₁⟩ := CellAttachmentComponent.exists_joined_base
      (CellAttachment.attachingMap c) s₀ (e.hom y₁)
    obtain ⟨x₂, h₂⟩ := CellAttachmentComponent.exists_joined_base
      (CellAttachment.attachingMap c) s₀ (e.hom y₂)
    have hbase : Joined
        (IndexedConeAttachment.base (CellAttachment.attachingMap c) x₁)
        (IndexedConeAttachment.base (CellAttachment.attachingMap c) x₂) :=
      ⟨(PathConnectedSpace.somePath x₁ x₂).map
        (IndexedConeAttachment.continuous_base
          (CellAttachment.attachingMap c))⟩
    have hmodel : Joined (e.hom y₁) (e.hom y₂) :=
      h₁.trans (hbase.trans h₂.symm)
    have htarget : Joined (e.inv (e.hom y₁)) (e.inv (e.hom y₂)) :=
      ⟨hmodel.somePath.map e.inv.hom.continuous⟩
    simpa using htarget

end Hatcher
