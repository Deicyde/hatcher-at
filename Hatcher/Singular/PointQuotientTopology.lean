/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Jack McCarthy
-/
import Hatcher.Singular.PointQuotient
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topology of point quotients

For a nonempty topological pair `(X, A)`, the canonical map from `X` to the
pushout `X ⊔_A PUnit` is a quotient map.  Its fibre over the pushout point is
the range of `A → X`.  If that range is closed, the quotient map restricts to
a homeomorphism away from the collapsed subspace.
-/

noncomputable section

open CategoryTheory Limits

namespace Hatcher.Relative

universe w

private theorem pointQuotientTypesIsPushout (P : TopPair.{w}) :
    IsPushout
      ((forget TopCat).map P.map)
      ((forget TopCat).map (pointQuotientCollapse P))
      ((forget TopCat).map (pointQuotientProjection P))
      ((forget TopCat).map (pointQuotientPointInclusion P)) :=
  (IsPushout.of_hasPushout P.map (pointQuotientCollapse P)).map (forget TopCat)

/-- If the collapsed subspace is nonempty, every point of the pushout has a
representative in the ambient space. -/
lemma pointQuotientProjection_surjective (P : TopPair.{w}) [Nonempty P.snd] :
    Function.Surjective (pointQuotientProjection P) := by
  intro y
  let h := pointQuotientTypesIsPushout P
  obtain (⟨x, hx⟩ | ⟨u, hu⟩) :=
    Limits.Types.eq_or_eq_of_isPushout h y
  · exact ⟨x, hx⟩
  · let a : P.snd := Classical.choice (inferInstance : Nonempty P.snd)
    refine ⟨P.map a, ?_⟩
    rw [← hu]
    cases u
    simpa [pointQuotientCollapse] using
      ConcreteCategory.congr_hom h.w a

/-- The canonical map `X → X/A` is a quotient map when `A` is nonempty. -/
theorem pointQuotientProjection_isQuotientMap (P : TopPair.{w}) [Nonempty P.snd] :
    Topology.IsQuotientMap (pointQuotientProjection P) := by
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen fun s ↦ ?_,
    pointQuotientProjection_surjective P⟩
  constructor
  · intro hs
    unfold pointQuotient at s hs ⊢
    rw [TopCat.colimit_isOpen_iff]
    intro j
    obtain (_ | _ | _) := j
    · have hs' := hs.preimage (TopPair.isEmbedding_map P).continuous
      rw [← colimit.w (span P.map (pointQuotientCollapse P)) WalkingSpan.Hom.fst]
      change IsOpen (P.map ⁻¹' (pointQuotientProjection P ⁻¹' s))
      exact hs'
    · simpa [pointQuotientProjection, pointQuotient] using hs
    · by_cases hmem :
          colimit.ι (span P.map (pointQuotientCollapse P)) WalkingSpan.right PUnit.unit ∈ s
      · have heq :
            colimit.ι (span P.map (pointQuotientCollapse P)) WalkingSpan.right ⁻¹' s =
              Set.univ := by
          ext u
          cases u
          simp only [Set.mem_preimage, Set.mem_univ, iff_true]
          exact hmem
        rw [heq]
        exact isOpen_univ
      · have heq :
            colimit.ι (span P.map (pointQuotientCollapse P)) WalkingSpan.right ⁻¹' s =
              ∅ := by
          ext u
          cases u
          simpa using hmem
        rw [heq]
        exact isOpen_empty
  · intro hs
    exact hs.preimage (pointQuotientProjection P).hom.continuous

/-- The fibre of the canonical projection over the collapsed point is exactly
the image of the subspace. -/
theorem pointQuotientProjection_preimage_point (P : TopPair.{w}) :
    pointQuotientProjection P ⁻¹' {pointQuotientPoint P} = Set.range P.map := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
  let h := pointQuotientTypesIsPushout P
  constructor
  · intro hx
    have hx' : pointQuotientProjection P x =
        pointQuotientPointInclusion P PUnit.unit := by
      simpa [pointQuotientPoint] using hx
    obtain ⟨a, ha, -⟩ :=
      (Limits.Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
        h.isColimit (TopPair.isEmbedding_map P).injective x PUnit.unit).1 hx'
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    simpa [pointQuotientPoint, pointQuotientCollapse] using
      ConcreteCategory.congr_hom h.w a

/-- Collapsing a nonempty closed subspace produces a closed distinguished
point in the quotient. -/
theorem pointQuotientPoint_isClosed (P : TopPair.{w}) [Nonempty P.snd]
    (hP : IsClosed (Set.range P.map)) :
    IsClosed ({pointQuotientPoint P} : Set (pointQuotient P)) := by
  rw [← (pointQuotientProjection_isQuotientMap P).isCoinducing.isClosed_preimage]
  rwa [pointQuotientProjection_preimage_point]

private lemma pointQuotientProjection_injective_of_not_mem (P : TopPair.{w})
    {x y : P.fst} (hx : x ∉ Set.range P.map)
    (hxy : pointQuotientProjection P x = pointQuotientProjection P y) : x = y := by
  let h := pointQuotientTypesIsPushout P
  let φX : (forget TopCat).obj P.fst ⟶ ULift.{w} Prop :=
    ↾fun z ↦ ULift.up (z = x)
  let φpt : (forget TopCat).obj (TopCat.of PUnit) ⟶ ULift.{w} Prop :=
    ↾fun _ ↦ ULift.up False
  have hw : ((forget TopCat).map P.map) ≫ φX =
      ((forget TopCat).map (pointQuotientCollapse P)) ≫ φpt := by
    ext a
    change P.map a = x ↔ False
    constructor
    · intro ha
      exact (hx ⟨a, ha⟩).elim
    · intro ha
      exact ha.elim
  let d := h.desc φX φpt hw
  have hd (z : P.fst) : d (pointQuotientProjection P z) = φX z := by
    have hd' := ConcreteCategory.congr_hom (h.inl_desc φX φpt hw) z
    change d (pointQuotientProjection P z) = φX z at hd'
    exact hd'
  have hφ : φX x = φX y := by
    exact (hd x).symm.trans ((congrArg d hxy).trans (hd y))
  have hp : (x = x) = (y = x) := congrArg ULift.down hφ
  exact (Eq.mp hp rfl).symm

/-- Away from a closed collapsed subspace, the point-quotient projection is a
homeomorphism onto the complement of the collapsed point. -/
noncomputable def pointQuotientComplementHomeomorph (P : TopPair.{w})
    [Nonempty P.snd] (hP : IsClosed (Set.range P.map)) :
    ((Set.range P.map)ᶜ : Set P.fst) ≃ₜ
      (({pointQuotientPoint P} : Set (pointQuotient P))ᶜ :
        Set (pointQuotient P)) := by
  let t : Set (pointQuotient P) :=
    ({pointQuotientPoint P} : Set (pointQuotient P))ᶜ
  let f := t.restrictPreimage (pointQuotientProjection P)
  have ht : IsOpen t := (pointQuotientPoint_isClosed P hP).isOpen_compl
  have hf : Topology.IsQuotientMap f :=
    (pointQuotientProjection_isQuotientMap P).restrictPreimage_isOpen ht
  have hfi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply pointQuotientProjection_injective_of_not_mem P
    · intro hx
      exact x.property (by
        change x.1 ∈ pointQuotientProjection P ⁻¹'
          ({pointQuotientPoint P} : Set (pointQuotient P))
        rw [pointQuotientProjection_preimage_point]
        exact hx)
    · exact congrArg Subtype.val hxy
  let e : (pointQuotientProjection P ⁻¹' t) ≃ t :=
    Equiv.ofBijective f ⟨hfi, hf.surjective⟩
  let he : (pointQuotientProjection P ⁻¹' t) ≃ₜ t :=
    e.toHomeomorphOfContinuousOpen hf.continuous
      (hf.isCoinducing.isOpenMap_of_injective hfi)
  have hpre : (Set.range P.map)ᶜ = pointQuotientProjection P ⁻¹' t := by
    dsimp [t]
    ext x
    simp only [Set.mem_compl_iff, Set.mem_preimage]
    exact not_congr ((Set.ext_iff.mp
      (pointQuotientProjection_preimage_point P) x).symm)
  exact (Homeomorph.setCongr hpre).trans he

@[simp]
lemma pointQuotientComplementHomeomorph_apply (P : TopPair.{w})
    [Nonempty P.snd] (hP : IsClosed (Set.range P.map))
    (x : ((Set.range P.map)ᶜ : Set P.fst)) :
    (pointQuotientComplementHomeomorph P hP x).1 =
      pointQuotientProjection P x.1 := rfl

end Hatcher.Relative
