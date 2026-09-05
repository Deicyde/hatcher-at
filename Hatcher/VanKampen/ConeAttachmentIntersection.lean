import Hatcher.VanKampen.ConeAttachment
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The intersection in the standard cone-attachment cover

The lower and upper members of the standard cover intersect in the open
interior cylinder on the attaching space. Consequently, their intersection is
homotopy equivalent to the attaching space.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Hatcher.VanKampen.ConeAttachment

universe u v

variable {X : Type u} {S : Type v}

private def interiorRaw (_f : S → X) :
    S × Set.Ioo (0 : I) 1 → Prequotient X S :=
  (Sum.inr : Unit ⊕ (S × I) → Prequotient X S) ∘
    (Sum.inr : S × I → Unit ⊕ (S × I)) ∘
      Prod.map id Subtype.val

private theorem quotientMk_preimage_coverIntersection (f : S → X) :
    quotientMk f ⁻¹' (lowerCover f ∩ upperCover f) =
      Set.range (interiorRaw f) := by
  ext z
  constructor
  · intro hz
    rw [preimage_inter, quotientMk_preimage_lowerCover,
      quotientMk_preimage_upperCover] at hz
    rcases z with x | (_ | ⟨s, t⟩)
    · exact False.elim hz.2
    · exact False.elim hz.1
    · exact ⟨⟨s, ⟨t, hz.1, hz.2⟩⟩, rfl⟩
  · rintro ⟨⟨s, t, ht⟩, rfl⟩
    rw [preimage_inter, quotientMk_preimage_lowerCover,
      quotientMk_preimage_upperCover]
    exact ht

variable [TopologicalSpace X] [TopologicalSpace S]

private theorem isEmbedding_interiorRaw (f : S → X) :
    IsEmbedding (interiorRaw f) := by
  exact IsEmbedding.inr.comp
    (IsEmbedding.inr.comp (IsEmbedding.id.prodMap IsEmbedding.subtypeVal))

private noncomputable def interiorPreimageHomeomorph (f : S → X) :
    S × Set.Ioo (0 : I) 1 ≃ₜ
      quotientMk f ⁻¹' (lowerCover f ∩ upperCover f) :=
  (isEmbedding_interiorRaw f).toHomeomorph.trans
    (Homeomorph.setCongr (quotientMk_preimage_coverIntersection f).symm)

private theorem isOpen_coverIntersection (f : S → X) :
    IsOpen (lowerCover f ∩ upperCover f) :=
  (isOpen_lowerCover f).inter (isOpen_upperCover f)

private theorem isQuotientMap_restrictPreimage_coverIntersection
    (f : S → X) :
    IsQuotientMap
      ((lowerCover f ∩ upperCover f).restrictPreimage (quotientMk f)) :=
  (isQuotientMap_quotientMk f).restrictPreimage_isOpen
    (isOpen_coverIntersection f)

omit [TopologicalSpace X] [TopologicalSpace S] in
private theorem injective_restrictPreimage_coverIntersection (f : S → X) :
    Function.Injective
      ((lowerCover f ∩ upperCover f).restrictPreimage (quotientMk f)) := by
  intro a b h
  have ha : a.1 ∈ Set.range (interiorRaw f) := by
    rw [← quotientMk_preimage_coverIntersection f]
    exact a.2
  have hb : b.1 ∈ Set.range (interiorRaw f) := by
    rw [← quotientMk_preimage_coverIntersection f]
    exact b.2
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  apply Subtype.ext
  rw [← hp, ← hq]
  have hrel := Quotient.exact (congrArg Subtype.val h)
  change normalForm f a.1 = normalForm f b.1 at hrel
  rw [← hp, ← hq] at hrel
  have hpq : p.1 = q.1 ∧ (p.2 : I) = q.2 := by
    simpa [interiorRaw, normalForm, ne_of_gt p.2.2.1,
      ne_of_lt p.2.2.2, ne_of_gt q.2.2.1,
      ne_of_lt q.2.2.2] using hrel
  change Sum.inr (Sum.inr (p.1, (p.2 : I))) =
    Sum.inr (Sum.inr (q.1, (q.2 : I)))
  exact congrArg (fun r : S × I ↦ Sum.inr (Sum.inr r))
    (Prod.ext hpq.1 hpq.2)

private noncomputable def homeomorphOfQuotientInjective
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {g : A → B} (hg : IsQuotientMap g) (hinj : Function.Injective g) :
    A ≃ₜ B := by
  let e : A ≃ B := Equiv.ofBijective g ⟨hinj, hg.surjective⟩
  exact
    { toEquiv := e
      continuous_toFun := hg.continuous
      continuous_invFun := hg.continuous_iff.mpr <| by
        convert continuous_id using 1
        funext a
        exact e.symm_apply_apply a }

private noncomputable def preimageHomeomorphCoverIntersection (f : S → X) :
    (quotientMk f ⁻¹' (lowerCover f ∩ upperCover f)) ≃ₜ
      ↥(lowerCover f ∩ upperCover f) :=
  homeomorphOfQuotientInjective
    (isQuotientMap_restrictPreimage_coverIntersection f)
    (injective_restrictPreimage_coverIntersection f)

/-- The intersection of the standard lower and upper cone-cover members is
homeomorphic to the open interior cylinder on the attaching space. -/
noncomputable def interiorCylinderHomeomorphCoverIntersection (f : S → X) :
    S × Set.Ioo (0 : I) 1 ≃ₜ ↥(lowerCover f ∩ upperCover f) :=
  (interiorPreimageHomeomorph f).trans
    (preimageHomeomorphCoverIntersection f)

private def unitIntervalInteriorHomeomorphReal :
    Set.Ioo (0 : I) 1 ≃ₜ Set.Ioo (0 : ℝ) 1 where
  toFun t := ⟨t.1.1, t.2⟩
  invFun r := ⟨⟨r.1, r.2.1.le, r.2.2.le⟩, r.2⟩
  left_inv t := by ext; rfl
  right_inv r := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private noncomputable def interiorCylinderHomotopyEquivBase (S : Type v)
    [TopologicalSpace S] :
    ContinuousMap.HomotopyEquiv (S × Set.Ioo (0 : I) 1) S := by
  letI : ContractibleSpace (Set.Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).contractibleSpace ⟨1 / 2, by norm_num⟩
  letI : ContractibleSpace (Set.Ioo (0 : I) 1) :=
    unitIntervalInteriorHomeomorphReal.contractibleSpace
  exact ((ContinuousMap.HomotopyEquiv.refl S).prodCongr
      (ContractibleSpace.hequiv (Set.Ioo (0 : I) 1) Unit).some).trans
    (Homeomorph.prodUnique S Unit).toHomotopyEquiv

/-- The intersection of the standard lower and upper cone-cover members is
homotopy equivalent to the attaching space. -/
noncomputable def coverIntersectionHomotopyEquivBase (f : S → X) :
    ContinuousMap.HomotopyEquiv ↥(lowerCover f ∩ upperCover f) S :=
  (interiorCylinderHomeomorphCoverIntersection f).symm.toHomotopyEquiv.trans
    (interiorCylinderHomotopyEquivBase S)

end Hatcher.VanKampen.ConeAttachment
