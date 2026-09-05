import Hatcher.VanKampen.VanKampenKernel
import Mathlib.GroupTheory.PushoutI

noncomputable section

open Set

namespace Hatcher.VanKampen

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The two maps from the fundamental group of the binary intersection to
the fundamental groups of the two cover members. -/
def binaryOverlapMaps (U : Fin 2 → Set X) (x₀ : X)
    (hx₀ : ∀ i, x₀ ∈ U i) :
    ∀ i : Fin 2, OverlapGroup U x₀ hx₀ 0 1 →* CoverGroup U x₀ hx₀ i :=
  Fin.cases (overlapToLeft U x₀ hx₀ 0 1) fun i ↦ by
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact overlapToRight U x₀ hx₀ 0 1

@[simp]
theorem binaryOverlapMaps_zero
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i) :
    binaryOverlapMaps U x₀ hx₀ 0 = overlapToLeft U x₀ hx₀ 0 1 :=
  rfl

@[simp]
theorem binaryOverlapMaps_one
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i) :
    binaryOverlapMaps U x₀ hx₀ 1 = overlapToRight U x₀ hx₀ 0 1 := by
  rfl

/-- Inclusion of a binary cover member into the ambient fundamental group. -/
def binaryCoverInclusion (U : Fin 2 → Set X) (x₀ : X)
    (hx₀ : ∀ i, x₀ ∈ U i) (i : Fin 2) :
    CoverGroup U x₀ hx₀ i →* FundamentalGroup X x₀ :=
  FundamentalGroup.map
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X))
    (⟨x₀, hx₀ i⟩ : U i)

/-- Inclusion of the binary intersection into the ambient fundamental group. -/
def binaryIntersectionInclusion (U : Fin 2 → Set X) (x₀ : X)
    (hx₀ : ∀ i, x₀ ∈ U i) :
    OverlapGroup U x₀ hx₀ 0 1 →* FundamentalGroup X x₀ :=
  FundamentalGroup.map
    (⟨Subtype.val, continuous_subtype_val⟩ : C((U 0 ∩ U 1 : Set X), X))
    (⟨x₀, ⟨hx₀ 0, hx₀ 1⟩⟩ : (U 0 ∩ U 1 : Set X))

theorem binaryCoverInclusion_comp_overlap
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i)
    (i : Fin 2) :
    (binaryCoverInclusion U x₀ hx₀ i).comp
        (binaryOverlapMaps U x₀ hx₀ i) =
      binaryIntersectionInclusion U x₀ hx₀ := by
  apply MonoidHom.ext
  intro ω
  induction i using Fin.cases with
  | zero =>
      induction ω using Path.Homotopic.Quotient.ind with
      | mk p => rfl
  | succ i =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      induction ω using Path.Homotopic.Quotient.ind with
      | mk p => rfl

/-- The canonical map from the binary group pushout to the ambient
fundamental group. -/
def binaryPushoutMap (U : Fin 2 → Set X) (x₀ : X)
    (hx₀ : ∀ i, x₀ ∈ U i) :
    Monoid.PushoutI (binaryOverlapMaps U x₀ hx₀) →*
      FundamentalGroup X x₀ :=
  Monoid.PushoutI.lift (binaryCoverInclusion U x₀ hx₀)
    (binaryIntersectionInclusion U x₀ hx₀)
    (binaryCoverInclusion_comp_overlap U x₀ hx₀)

private theorem binary_pairwise_pathConnected
    (U : Fin 2 → Set X)
    (hone : ∀ i, IsPathConnected (U i))
    (hinter : IsPathConnected (U 0 ∩ U 1)) :
    ∀ i j, IsPathConnected (U i ∩ U j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using hone 0
  · exact hinter
  · simpa [inter_comm] using hinter
  · simpa using hone 1

private theorem binary_triple_pathConnected
    (U : Fin 2 → Set X)
    (hone : ∀ i, IsPathConnected (U i))
    (hinter : IsPathConnected (U 0 ∩ U 1)) :
    ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k) := by
  intro i j k
  fin_cases i
  · fin_cases j
    · fin_cases k
      · simpa using hone 0
      · convert hinter using 1
        ext x
        simp
    · fin_cases k
      · convert hinter using 1
        ext x
        simp [and_comm]
      · convert hinter using 1
        ext x
        simp
  · fin_cases j
    · fin_cases k
      · convert hinter using 1
        ext x
        simp [and_comm]
      · convert hinter using 1
        ext x
        simp [and_comm]
    · fin_cases k
      · convert hinter using 1
        ext x
        simp [and_comm]
      · simpa using hone 1

theorem binaryPushoutMap_comp_ofCoprodI
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i) :
    (binaryPushoutMap U x₀ hx₀).comp Monoid.PushoutI.ofCoprodI =
      coverMap U x₀ hx₀ := by
  apply Monoid.CoprodI.ext_hom
  intro i
  ext g
  simp [binaryPushoutMap, binaryCoverInclusion, coverMap]

theorem binaryPushoutMap_surjective
    (U : Fin 2 → Set X) (x₀ : X)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (hinter : IsPathConnected (U 0 ∩ U 1))
    (hx₀ : ∀ i, x₀ ∈ U i) :
    Function.Surjective (binaryPushoutMap U x₀ hx₀) := by
  intro g
  obtain ⟨w, hw⟩ := coverMap_surjective U x₀ hU hcover
    (binary_pairwise_pathConnected U hone hinter) hx₀ g
  refine ⟨Monoid.PushoutI.ofCoprodI w, ?_⟩
  rw [← MonoidHom.comp_apply, binaryPushoutMap_comp_ofCoprodI]
  exact hw

/-- Swap the two coordinates of a pairwise overlap. -/
private def overlapSwap (U : Fin 2 → Set X) (x₀ : X)
    (hx₀ : ∀ i, x₀ ∈ U i) (i j : Fin 2) :
    OverlapGroup U x₀ hx₀ i j →* OverlapGroup U x₀ hx₀ j i :=
  FundamentalGroup.map
    (⟨fun x ↦ ⟨x.1, x.2.2, x.2.1⟩,
      continuous_subtype_val.subtype_mk _⟩ :
      C((U i ∩ U j : Set X), (U j ∩ U i : Set X)))
    (⟨x₀, ⟨hx₀ i, hx₀ j⟩⟩ : (U i ∩ U j : Set X))

private theorem overlapToLeft_swap
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i)
    (i j : Fin 2) (ω : OverlapGroup U x₀ hx₀ i j) :
    overlapToLeft U x₀ hx₀ j i (overlapSwap U x₀ hx₀ i j ω) =
      overlapToRight U x₀ hx₀ i j ω := by
  induction ω using Path.Homotopic.Quotient.ind with
  | mk p => rfl

private theorem overlapToRight_swap
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i)
    (i j : Fin 2) (ω : OverlapGroup U x₀ hx₀ i j) :
    overlapToRight U x₀ hx₀ j i (overlapSwap U x₀ hx₀ i j ω) =
      overlapToLeft U x₀ hx₀ i j ω := by
  induction ω using Path.Homotopic.Quotient.ind with
  | mk p => rfl

private theorem binaryPushout_overlap_images_eq
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i)
    (i j : Fin 2) (ω : OverlapGroup U x₀ hx₀ i j) :
    Monoid.PushoutI.of (φ := binaryOverlapMaps U x₀ hx₀) i
        (overlapToLeft U x₀ hx₀ i j ω) =
      Monoid.PushoutI.of (φ := binaryOverlapMaps U x₀ hx₀) j
        (overlapToRight U x₀ hx₀ i j ω) := by
  fin_cases i <;> fin_cases j
  · induction ω using Path.Homotopic.Quotient.ind with
    | mk p => rfl
  · calc
      Monoid.PushoutI.of 0 (overlapToLeft U x₀ hx₀ 0 1 ω) =
          Monoid.PushoutI.base (binaryOverlapMaps U x₀ hx₀) ω := by
        simpa [binaryOverlapMaps] using
          Monoid.PushoutI.of_apply_eq_base
            (binaryOverlapMaps U x₀ hx₀) 0 ω
      _ = Monoid.PushoutI.of 1
          (binaryOverlapMaps U x₀ hx₀ 1 ω) := by
        exact (Monoid.PushoutI.of_apply_eq_base
          (binaryOverlapMaps U x₀ hx₀) 1 ω).symm
      _ = Monoid.PushoutI.of 1 (overlapToRight U x₀ hx₀ 0 1 ω) := by
        rw [binaryOverlapMaps_one]
  · let η := overlapSwap U x₀ hx₀ 1 0 ω
    calc
      Monoid.PushoutI.of 1 (overlapToLeft U x₀ hx₀ 1 0 ω) =
          Monoid.PushoutI.of 1 (overlapToRight U x₀ hx₀ 0 1 η) := by
        rw [overlapToRight_swap]
      _ = Monoid.PushoutI.of 1
          (binaryOverlapMaps U x₀ hx₀ 1 η) := by
        rw [binaryOverlapMaps_one]
      _ = Monoid.PushoutI.base (binaryOverlapMaps U x₀ hx₀) η := by
        exact Monoid.PushoutI.of_apply_eq_base
          (binaryOverlapMaps U x₀ hx₀) 1 η
      _ = Monoid.PushoutI.of 0 (overlapToLeft U x₀ hx₀ 0 1 η) := by
        simpa [binaryOverlapMaps] using
          (Monoid.PushoutI.of_apply_eq_base
            (binaryOverlapMaps U x₀ hx₀) 0 η).symm
      _ = Monoid.PushoutI.of 0 (overlapToRight U x₀ hx₀ 1 0 ω) := by
        rw [overlapToLeft_swap]
  · induction ω using Path.Homotopic.Quotient.ind with
    | mk p => rfl

/-- The binary pushout kills every overlap relator in the indexed free product. -/
private theorem relationSubgroup_le_binaryPushout_ker
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i) :
    relationSubgroup U x₀ hx₀ ≤
      MonoidHom.ker
        (Monoid.PushoutI.ofCoprodI :
          CoverFreeProduct U x₀ hx₀ →*
            Monoid.PushoutI (binaryOverlapMaps U x₀ hx₀)) := by
  apply Subgroup.normalClosure_le_normal
  rintro r ⟨i, j, ω, rfl⟩
  apply MonoidHom.mem_ker.mpr
  simp only [overlapRelation, map_mul, map_inv,
    Monoid.PushoutI.ofCoprodI_of]
  rw [binaryPushout_overlap_images_eq, mul_inv_cancel]

/-- The map from the overlap-relation quotient to the binary pushout. -/
private def binaryQuotientToPushout
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i) :
    CoverFreeProduct U x₀ hx₀ ⧸ relationSubgroup U x₀ hx₀ →*
      Monoid.PushoutI (binaryOverlapMaps U x₀ hx₀) :=
  QuotientGroup.lift (relationSubgroup U x₀ hx₀)
    Monoid.PushoutI.ofCoprodI
    (relationSubgroup_le_binaryPushout_ker U x₀ hx₀)

/-- The inclusion of one binary cover factor into the overlap-relation quotient. -/
private def binaryQuotientOf
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i)
    (i : Fin 2) :
    CoverGroup U x₀ hx₀ i →*
      CoverFreeProduct U x₀ hx₀ ⧸ relationSubgroup U x₀ hx₀ :=
  (QuotientGroup.mk' (relationSubgroup U x₀ hx₀)).comp
    (Monoid.CoprodI.of :
      CoverGroup U x₀ hx₀ i →* CoverFreeProduct U x₀ hx₀)

private theorem binaryQuotient_overlap_images_eq
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i)
    (i j : Fin 2) (ω : OverlapGroup U x₀ hx₀ i j) :
    binaryQuotientOf U x₀ hx₀ i (overlapToLeft U x₀ hx₀ i j ω) =
      binaryQuotientOf U x₀ hx₀ j
        (overlapToRight U x₀ hx₀ i j ω) := by
  apply QuotientGroup.eq_iff_div_mem.mpr
  change overlapRelation U x₀ hx₀ i j ω ∈ relationSubgroup U x₀ hx₀
  apply Subgroup.subset_normalClosure
  exact ⟨i, j, ω, rfl⟩

private theorem binaryQuotientOf_comp_overlap
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i)
    (i : Fin 2) :
    (binaryQuotientOf U x₀ hx₀ i).comp
        (binaryOverlapMaps U x₀ hx₀ i) =
      (binaryQuotientOf U x₀ hx₀ 0).comp
        (binaryOverlapMaps U x₀ hx₀ 0) := by
  fin_cases i
  · rfl
  · apply MonoidHom.ext
    intro ω
    simp only [MonoidHom.comp_apply, binaryOverlapMaps_zero]
    exact (binaryQuotient_overlap_images_eq U x₀ hx₀ 0 1 ω).symm

/-- The map from the binary pushout to the overlap-relation quotient. -/
private def binaryPushoutToQuotient
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i) :
    Monoid.PushoutI (binaryOverlapMaps U x₀ hx₀) →*
      CoverFreeProduct U x₀ hx₀ ⧸ relationSubgroup U x₀ hx₀ :=
  Monoid.PushoutI.lift (binaryQuotientOf U x₀ hx₀)
    ((binaryQuotientOf U x₀ hx₀ 0).comp
      (binaryOverlapMaps U x₀ hx₀ 0))
    (binaryQuotientOf_comp_overlap U x₀ hx₀)

private theorem binaryQuotientToPushout_comp_binaryPushoutToQuotient
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i) :
    (binaryQuotientToPushout U x₀ hx₀).comp
        (binaryPushoutToQuotient U x₀ hx₀) =
      MonoidHom.id (Monoid.PushoutI (binaryOverlapMaps U x₀ hx₀)) := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  apply MonoidHom.ext
  intro g
  simp [binaryPushoutToQuotient, binaryQuotientToPushout,
    binaryQuotientOf]

private theorem binaryPushoutToQuotient_comp_binaryQuotientToPushout
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i) :
    (binaryPushoutToQuotient U x₀ hx₀).comp
        (binaryQuotientToPushout U x₀ hx₀) =
      MonoidHom.id
        (CoverFreeProduct U x₀ hx₀ ⧸ relationSubgroup U x₀ hx₀) := by
  apply QuotientGroup.monoidHom_ext
  apply Monoid.CoprodI.ext_hom
  intro i
  apply MonoidHom.ext
  intro g
  simp [binaryPushoutToQuotient, binaryQuotientToPushout,
    binaryQuotientOf]

/-- Mathlib's indexed binary pushout is the free-product quotient by all
pairwise-overlap relations. -/
def binaryPushoutEquivQuotient
    (U : Fin 2 → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i) :
    Monoid.PushoutI (binaryOverlapMaps U x₀ hx₀) ≃*
      CoverFreeProduct U x₀ hx₀ ⧸ relationSubgroup U x₀ hx₀ where
  toFun := binaryPushoutToQuotient U x₀ hx₀
  invFun := binaryQuotientToPushout U x₀ hx₀
  left_inv g := by
    have h := DFunLike.congr_fun
      (binaryQuotientToPushout_comp_binaryPushoutToQuotient U x₀ hx₀) g
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h
  right_inv q := by
    have h := DFunLike.congr_fun
      (binaryPushoutToQuotient_comp_binaryQuotientToPushout U x₀ hx₀) q
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h
  map_mul' g h := map_mul (binaryPushoutToQuotient U x₀ hx₀) g h

/-- **Binary van Kampen theorem.** For a path-connected open binary cover
with path-connected intersection, the two inclusion maps from the
intersection fundamental group exhibit the ambient fundamental group as their
group pushout. -/
noncomputable def pushoutEquivFundamentalGroup
    (U : Fin 2 → Set X) (x₀ : X)
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (hinter : IsPathConnected (U 0 ∩ U 1))
    (hx₀ : ∀ i, x₀ ∈ U i) :
    Monoid.PushoutI (binaryOverlapMaps U x₀ hx₀) ≃*
      FundamentalGroup X x₀ :=
  (binaryPushoutEquivQuotient U x₀ hx₀).trans
    (quotientEquivFundamentalGroup U x₀ hUopen hUcover hone
      (binary_pairwise_pathConnected U hone hinter)
      (binary_triple_pathConnected U hone hinter) hx₀)

@[simp]
theorem pushoutEquivFundamentalGroup_of
    (U : Fin 2 → Set X) (x₀ : X)
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (hinter : IsPathConnected (U 0 ∩ U 1))
    (hx₀ : ∀ i, x₀ ∈ U i) (i : Fin 2)
    (g : CoverGroup U x₀ hx₀ i) :
    pushoutEquivFundamentalGroup U x₀ hUopen hUcover hone hinter hx₀
        (Monoid.PushoutI.of i g) =
      binaryCoverInclusion U x₀ hx₀ i g := by
  change quotientEquivFundamentalGroup U x₀ hUopen hUcover hone
      (binary_pairwise_pathConnected U hone hinter)
      (binary_triple_pathConnected U hone hinter) hx₀
        (QuotientGroup.mk' (relationSubgroup U x₀ hx₀)
          (Monoid.CoprodI.of g)) =
    binaryCoverInclusion U x₀ hx₀ i g
  change coverMap U x₀ hx₀ (Monoid.CoprodI.of g) =
    binaryCoverInclusion U x₀ hx₀ i g
  rfl

/-- The binary van Kampen equivalence has the canonical pushout map as its
underlying homomorphism. -/
theorem pushoutEquivFundamentalGroup_toMonoidHom
    (U : Fin 2 → Set X) (x₀ : X)
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (hinter : IsPathConnected (U 0 ∩ U 1))
    (hx₀ : ∀ i, x₀ ∈ U i) :
    (pushoutEquivFundamentalGroup U x₀ hUopen hUcover hone hinter hx₀).toMonoidHom =
      binaryPushoutMap U x₀ hx₀ := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  apply MonoidHom.ext
  intro g
  simp [pushoutEquivFundamentalGroup_of, binaryPushoutMap]

end Hatcher.VanKampen
