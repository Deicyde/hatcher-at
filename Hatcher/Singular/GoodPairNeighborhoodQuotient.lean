/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.GoodPair
import Hatcher.Singular.PointQuotientTopology

/-!
# Point quotients of good-pair neighborhoods

For chosen good-pair data, this file restricts the point-quotient projection
to the chosen neighborhood.  The chosen neighborhood is not assumed open.
Its image nevertheless has the quotient topology, since the neighborhood is
saturated and contains the collapsed subspace in its interior.
-/

noncomputable section

open CategoryTheory Set Topology

namespace Hatcher.Relative

universe w

namespace GoodPairData

variable {P : TopPair.{w}}

/-- The image `V/A` of the chosen good-pair neighborhood in the point
quotient. -/
def pointQuotientNeighborhood (h : GoodPairData P) :
    Set (pointQuotient P) :=
  pointQuotientProjection P '' h.V

private lemma projection_eq_point_of_mem_range {x : P.fst}
    (hx : x ∈ Set.range P.map) :
    pointQuotientProjection P x = pointQuotientPoint P := by
  have hx' : x ∈ pointQuotientProjection P ⁻¹'
      ({pointQuotientPoint P} : Set (pointQuotient P)) := by
    rw [pointQuotientProjection_preimage_point]
    exact hx
  simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx'

private lemma projection_mem_range_of_eq_point {x : P.fst}
    (hx : pointQuotientProjection P x = pointQuotientPoint P) :
    x ∈ Set.range P.map := by
  rw [← pointQuotientProjection_preimage_point]
  simpa only [Set.mem_preimage, Set.mem_singleton_iff]

private lemma projection_injOn_compl_range (h : GoodPairData P) :
    Set.InjOn (pointQuotientProjection P) (Set.range P.map)ᶜ := by
  let _ : Nonempty P.snd := h.nonempty
  intro x hx y hy hxy
  let e := pointQuotientComplementHomeomorph P h.isClosed_range
  have he : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
    apply Subtype.ext
    change
      (pointQuotientComplementHomeomorph P h.isClosed_range ⟨x, hx⟩).1 =
        (pointQuotientComplementHomeomorph P h.isClosed_range ⟨y, hy⟩).1
    rw [pointQuotientComplementHomeomorph_apply,
      pointQuotientComplementHomeomorph_apply]
    exact hxy
  exact congrArg Subtype.val (e.injective he)

private lemma projection_preimage_image_eq
    (h : GoodPairData P) (S : Set P.fst)
    (hS : Set.range P.map ⊆ S ∨ Disjoint S (Set.range P.map)) :
    pointQuotientProjection P ⁻¹' (pointQuotientProjection P '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, hyS, hyx⟩
    by_cases hyA : y ∈ Set.range P.map
    · rcases hS with hsub | hdisj
      · apply hsub
        apply projection_mem_range_of_eq_point
        exact hyx.symm.trans (projection_eq_point_of_mem_range hyA)
      · exact (Set.disjoint_left.1 hdisj hyS hyA).elim
    · have hxA : x ∉ Set.range P.map := by
        intro hxA
        apply hyA
        apply projection_mem_range_of_eq_point
        exact hyx.trans (projection_eq_point_of_mem_range hxA)
      have hxy : x = y :=
        projection_injOn_compl_range h hxA hyA hyx.symm
      simpa [hxy] using hyS
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The chosen neighborhood is saturated for the point-quotient projection. -/
theorem pointQuotientProjection_preimage_neighborhood (h : GoodPairData P) :
    pointQuotientProjection P ⁻¹' h.pointQuotientNeighborhood = h.V := by
  apply projection_preimage_image_eq h
  exact Or.inl (h.range_subset_interior.trans interior_subset)

/-- The point-quotient projection restricted from `V` to its image `V/A`. -/
def pointQuotientNeighborhoodProjection (h : GoodPairData P) :
    C(h.V, h.pointQuotientNeighborhood) where
  toFun x := ⟨pointQuotientProjection P x.1, ⟨x.1, x.2, rfl⟩⟩
  continuous_toFun :=
    (pointQuotientProjection P).hom.continuous.comp continuous_subtype_val |>.subtype_mk _

@[simp]
lemma pointQuotientNeighborhoodProjection_apply (h : GoodPairData P)
    (x : h.V) :
    (h.pointQuotientNeighborhoodProjection x).1 =
      pointQuotientProjection P x.1 := rfl

/-- The restricted point-quotient projection is onto `V/A`. -/
lemma pointQuotientNeighborhoodProjection_surjective (h : GoodPairData P) :
    Function.Surjective h.pointQuotientNeighborhoodProjection := by
  rintro ⟨y, x, hxV, hxy⟩
  refine ⟨⟨x, hxV⟩, ?_⟩
  apply Subtype.ext
  exact hxy

/-- Restricting the point quotient to the chosen neighborhood is still a
quotient map, without assuming that the chosen neighborhood is open. -/
theorem pointQuotientNeighborhoodProjection_isQuotientMap
    (h : GoodPairData P) :
    Topology.IsQuotientMap h.pointQuotientNeighborhoodProjection := by
  let _ : Nonempty P.snd := h.nonempty
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen fun s ↦ ?_,
    h.pointQuotientNeighborhoodProjection_surjective⟩
  constructor
  · intro hs
    obtain ⟨O, hO, hOs⟩ := hs.image_val
    let pV : h.pointQuotientNeighborhood :=
      ⟨pointQuotientPoint P, by
        let a : P.snd := Classical.choice h.nonempty
        exact ⟨P.map a,
          h.range_subset_interior (Set.mem_range_self a) |>
            interior_subset,
          projection_eq_point_of_mem_range (Set.mem_range_self a)⟩⟩
    have hO_sat : Set.range P.map ⊆ O ∨ Disjoint O (Set.range P.map) := by
      by_cases hp : pV ∈ s
      · left
        intro x hxA
        have hxV : x ∈ h.V :=
          h.range_subset_interior hxA |> interior_subset
        have hxp : h.pointQuotientNeighborhoodProjection ⟨x, hxV⟩ = pV := by
          apply Subtype.ext
          exact projection_eq_point_of_mem_range hxA
        have hxpre : (⟨x, hxV⟩ : h.V) ∈
            h.pointQuotientNeighborhoodProjection ⁻¹' s := by
          change h.pointQuotientNeighborhoodProjection ⟨x, hxV⟩ ∈ s
          simpa [hxp] using hp
        have hximage : x ∈ Subtype.val ''
            (h.pointQuotientNeighborhoodProjection ⁻¹' s) :=
          ⟨⟨x, hxV⟩, hxpre, rfl⟩
        rw [hOs] at hximage
        exact hximage.1
      · right
        rw [Set.disjoint_left]
        intro x hxO hxA
        have hxV : x ∈ h.V :=
          h.range_subset_interior hxA |> interior_subset
        have hximage : x ∈ O ∩ h.V := ⟨hxO, hxV⟩
        rw [← hOs] at hximage
        obtain ⟨xV, hxpre, hxval⟩ := hximage
        have hxp : h.pointQuotientNeighborhoodProjection xV = pV := by
          apply Subtype.ext
          change pointQuotientProjection P xV.1 = pointQuotientPoint P
          rw [hxval]
          exact projection_eq_point_of_mem_range hxA
        apply hp
        rw [← hxp]
        exact hxpre
    have hpreO : pointQuotientProjection P ⁻¹'
        (pointQuotientProjection P '' O) = O :=
      projection_preimage_image_eq h O hO_sat
    have hqO : IsOpen (pointQuotientProjection P '' O) := by
      rw [← (pointQuotientProjection_isQuotientMap P).isCoinducing.isOpen_preimage,
        hpreO]
      exact hO
    have hs_eq : s = Subtype.val ⁻¹' (pointQuotientProjection P '' O) := by
      ext z
      constructor
      · intro hz
        obtain ⟨x, hx⟩ := h.pointQuotientNeighborhoodProjection_surjective z
        have hxpre : x ∈ h.pointQuotientNeighborhoodProjection ⁻¹' s := by
          change h.pointQuotientNeighborhoodProjection x ∈ s
          simpa [hx] using hz
        have hximage : x.1 ∈ Subtype.val ''
            (h.pointQuotientNeighborhoodProjection ⁻¹' s) :=
          ⟨x, hxpre, rfl⟩
        rw [hOs] at hximage
        exact ⟨x.1, hximage.1, by
          simpa only [pointQuotientNeighborhoodProjection_apply] using
            congrArg Subtype.val hx⟩
      · intro hz
        obtain ⟨y, hyO, hyz⟩ := hz
        obtain ⟨x, hx⟩ := h.pointQuotientNeighborhoodProjection_surjective z
        have hxO : x.1 ∈ O := by
          rw [← hpreO]
          exact ⟨y, hyO, hyz.trans (by
            simpa only [pointQuotientNeighborhoodProjection_apply] using
              (congrArg Subtype.val hx).symm)⟩
        have hximage : x.1 ∈ O ∩ h.V := ⟨hxO, x.2⟩
        rw [← hOs] at hximage
        obtain ⟨x', hxpre, hxval⟩ := hximage
        have hxx' : x = x' := Subtype.ext hxval.symm
        rw [hxx'] at hx
        change z ∈ s
        rw [← hx]
        exact hxpre
    rw [hs_eq]
    exact hqO.preimage continuous_subtype_val
  · intro hs
    exact hs.preimage h.pointQuotientNeighborhoodProjection.continuous

/-- The collapsed point is an interior point of `V/A`. -/
theorem pointQuotientPoint_mem_interior_neighborhood (h : GoodPairData P) :
    pointQuotientPoint P ∈ interior h.pointQuotientNeighborhood := by
  let _ : Nonempty P.snd := h.nonempty
  let U : Set P.fst := interior h.V
  have hpre : pointQuotientProjection P ⁻¹'
      (pointQuotientProjection P '' U) = U :=
    projection_preimage_image_eq h U (Or.inl h.range_subset_interior)
  have hqU : IsOpen (pointQuotientProjection P '' U) := by
    rw [← (pointQuotientProjection_isQuotientMap P).isCoinducing.isOpen_preimage,
      hpre]
    exact isOpen_interior
  have hqUqV : pointQuotientProjection P '' U ⊆
      h.pointQuotientNeighborhood :=
    Set.image_mono interior_subset
  apply (interior_maximal hqUqV hqU)
  let a : P.snd := Classical.choice h.nonempty
  exact ⟨P.map a, h.range_subset_interior (Set.mem_range_self a),
    projection_eq_point_of_mem_range (Set.mem_range_self a)⟩

/-- The deleted-subset excision hypothesis for the original neighborhood
pair `(X,V)`: the closure of the collapsed subspace lies in `interior V`. -/
theorem closure_range_subset_interior_neighborhood (h : GoodPairData P) :
    closure (Set.range P.map) ⊆ interior h.V := by
  rw [h.isClosed_range.closure_eq]
  exact h.range_subset_interior

/-- The deleted-subset excision hypothesis for the quotient neighborhood pair
`(X/A,V/A)`: the closure of the collapsed point lies in `interior (V/A)`. -/
theorem closure_point_subset_interior_pointQuotientNeighborhood
    (h : GoodPairData P) :
    closure ({pointQuotientPoint P} : Set (pointQuotient P)) ⊆
      interior h.pointQuotientNeighborhood := by
  let _ : Nonempty P.snd := h.nonempty
  rw [(pointQuotientPoint_isClosed P h.isClosed_range).closure_eq]
  exact Set.singleton_subset_iff.mpr
    h.pointQuotientPoint_mem_interior_neighborhood

/-- The quotient neighborhood `V/A`, packaged as a subspace pair of `X/A`. -/
def pointQuotientNeighborhoodPair (h : GoodPairData P) : TopPair.{w} :=
  TopPair.ofSubset h.pointQuotientNeighborhood

/-- The collapsed point, regarded as a map into the quotient neighborhood. -/
def pointQuotientNeighborhoodInclusion (h : GoodPairData P) :
    TopCat.of PUnit ⟶ TopCat.of h.pointQuotientNeighborhood :=
  TopCat.ofHom
    { toFun := fun _ ↦
        ⟨pointQuotientPoint P,
          interior_subset h.pointQuotientPoint_mem_interior_neighborhood⟩
      continuous_toFun := continuous_const }

@[simp]
lemma pointQuotientNeighborhoodInclusion_apply (h : GoodPairData P)
    (u : PUnit) :
    (h.pointQuotientNeighborhoodInclusion u).1 = pointQuotientPoint P := rfl

/-- The canonical map of pairs `(X/A,A/A) ⟶ (X/A,V/A)`. -/
def pointQuotientPairToNeighborhoodPair (h : GoodPairData P) :
    pointQuotientPair P ⟶ h.pointQuotientNeighborhoodPair :=
  TopPair.ofHom
    (𝟙 (pointQuotient P))
    h.pointQuotientNeighborhoodInclusion
    (by
      ext u
      cases u
      rfl)

@[simp]
lemma pointQuotientPairToNeighborhoodPair_fst (h : GoodPairData P) :
    TopPair.Hom.fst h.pointQuotientPairToNeighborhoodPair =
      𝟙 (pointQuotient P) := rfl

@[simp]
lemma pointQuotientPairToNeighborhoodPair_snd (h : GoodPairData P) :
    TopPair.Hom.snd h.pointQuotientPairToNeighborhoodPair =
      h.pointQuotientNeighborhoodInclusion := rfl

/-- The quotient projection as a map of neighborhood pairs
`(X,V) ⟶ (X/A,V/A)`. Its source is definitionally the existing
`h.neighborhoodPair`; spelling it as `TopPair.ofSubset h.V` here avoids an
unrelated homology-module dependency. -/
def neighborhoodPairToPointQuotientNeighborhoodPair (h : GoodPairData P) :
    TopPair.ofSubset h.V ⟶ h.pointQuotientNeighborhoodPair :=
  TopPair.ofHom
    (pointQuotientProjection P)
    (TopCat.ofHom h.pointQuotientNeighborhoodProjection)
    (by ext; rfl)

@[simp]
lemma neighborhoodPairToPointQuotientNeighborhoodPair_fst
    (h : GoodPairData P) :
    TopPair.Hom.fst h.neighborhoodPairToPointQuotientNeighborhoodPair =
      pointQuotientProjection P := rfl

@[simp]
lemma neighborhoodPairToPointQuotientNeighborhoodPair_snd
    (h : GoodPairData P) :
    TopPair.Hom.snd h.neighborhoodPairToPointQuotientNeighborhoodPair =
      TopCat.ofHom h.pointQuotientNeighborhoodProjection := rfl

end GoodPairData

end Hatcher.Relative
