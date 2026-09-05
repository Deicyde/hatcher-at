import Hatcher.VanKampen.WellPointedWedgeCover
import Mathlib.Topology.CompactOpen

noncomputable section

open Set Topology
open scoped unitInterval

namespace Hatcher.PointedWedge

universe u v w

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
  (x₀ : ∀ i, X i)

local instance : DecidableEq ι := Classical.decEq ι
local instance (p : Prop) : Decidable p := Classical.propDecidable p


private theorem continuous_quotientLift_prod
    {Y : Type w} [TopologicalSpace Y]
    (F : I × Option (Σ i, X i) → Y)
    (hrel : ∀ t a b, (setoid X x₀).r a b → F (t, a) = F (t, b))
    (hsummand : ∀ i, Continuous fun p : I × X i =>
      F (p.1, some ⟨i, p.2⟩))
    (hnone : Continuous fun t : I => F (t, none)) :
    Continuous fun p : I × Hatcher.PointedWedge X x₀ =>
      Quotient.lift (fun z => F (p.1, z)) (hrel p.1) p.2 := by
  let paths : Option (Σ i, X i) → C(I, Y) := fun z =>
    ⟨fun t => F (t, z), by
      cases z with
      | none => exact hnone
      | some p =>
          exact (hsummand p.1).comp
            (continuous_id.prodMk continuous_const)⟩
  have hpaths_rel : ∀ a b, (setoid X x₀).r a b →
      paths a = paths b := by
    intro a b hab
    ext t
    exact hrel t a b hab
  have hpaths_summand : ∀ i,
      Continuous fun x : X i => paths (some ⟨i, x⟩) := by
    intro i
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous fun p : X i × I => F (p.2, some ⟨i, p.1⟩)
    exact (hsummand i).comp continuous_swap
  have hpaths_pre : @Continuous (Option (Σ i, X i)) C(I, Y)
      (prequotientTopology (X := X)) _ paths := by
    unfold prequotientTopology
    rw [continuous_sup_dom]
    constructor
    · rw [continuous_coinduced_dom, continuous_sigma_iff]
      exact hpaths_summand
    · rw [continuous_coinduced_dom]
      fun_prop
  have hpaths : @Continuous (Hatcher.PointedWedge X x₀) C(I, Y)
      (instTopologicalSpace x₀) _ (Quotient.lift paths hpaths_rel) := by
    letI : TopologicalSpace (Option (Σ i, X i)) :=
      prequotientTopology (X := X)
    apply (isQuotientMap_quotientMk x₀).continuous_iff.mpr
    simpa [Function.comp_def] using hpaths_pre
  have huncurry : Continuous fun p : Hatcher.PointedWedge X x₀ × I =>
      Quotient.lift paths hpaths_rel p.1 p.2 :=
    ContinuousMap.continuous_uncurry_of_continuous ⟨_, hpaths⟩
  apply (huncurry.comp continuous_swap).congr
  rintro ⟨t, z⟩
  induction z using Quotient.inductionOn with
  | _ z => rfl

/-- On the prequotient, fix the selected summand and contract all other
summands whenever their points lie in the chosen neck. -/
private def memberDeformationPre
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) (t : I) :
    Option (Σ j, X j) → Option (Σ j, X j)
  | none => none
  | some ⟨j, x⟩ =>
      if _hji : j = i then some ⟨j, x⟩
      else if hx : x ∈ (hwell j).neighborhood then
        some ⟨j, ((hwell j).contraction (t, ⟨x, hx⟩) : X j)⟩
      else none

private theorem memberDeformationPre_respects
    (hwell : ∀ i, WellPointedAt (x₀ i))
    (i : ι) (t : I) {a b : Option (Σ j, X j)}
    (h : Relation.EqvGen (Rel X x₀) a b) :
    Relation.EqvGen (Rel X x₀)
      (memberDeformationPre x₀ hwell i t a)
      (memberDeformationPre x₀ hwell i t b) := by
  induction h with
  | rel a b h =>
      cases h with
      | base j =>
          by_cases hji : j = i
          · subst j
            simpa [memberDeformationPre] using
              Relation.EqvGen.rel _ _ (Rel.base (X := X) (x₀ := x₀) i)
          · have hx : x₀ j ∈ (hwell j).neighborhood :=
              (hwell j).mem_neighborhood
            simp only [memberDeformationPre, hji, hx, ↓reduceDIte]
            have hp : (⟨x₀ j, hx⟩ : (hwell j).neighborhood) =
                (hwell j).neighborhoodBasepoint := by
              rfl
            rw [hp, (hwell j).contraction_basepoint]
            exact Relation.EqvGen.rel _ _
              (Rel.base (X := X) (x₀ := x₀) j)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The induced set-theoretic deformation of the wedge. -/
private def memberDeformationPoint
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) (t : I) :
    Hatcher.PointedWedge X x₀ → Hatcher.PointedWedge X x₀ :=
  Quotient.map (memberDeformationPre x₀ hwell i t)
    (fun _ _ h ↦ memberDeformationPre_respects x₀ hwell i t h)

private theorem memberDeformationPoint_mem
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) (t : I)
    {z : Hatcher.PointedWedge X x₀}
    (hz : z ∈ vanKampenCover x₀ hwell i) :
    memberDeformationPoint x₀ hwell i t z ∈
      vanKampenCover x₀ hwell i := by
  induction z using Quotient.inductionOn with
  | _ a =>
      have hza : coverPreimage (fun j ↦ (hwell j).neighborhood) i a := by
        have hza' : a ∈
            (Quotient.mk (setoid X x₀)) ⁻¹'
              vanKampenCover x₀ hwell i := hz
        rw [vanKampenCover, quotientMk_preimage_coverSet] at hza'
        exact hza'
      have hout : coverPreimage (fun j ↦ (hwell j).neighborhood) i
          (memberDeformationPre x₀ hwell i t a) := by
        clear hz
        cases a with
        | none => trivial
        | some p =>
            rcases p with ⟨j, x⟩
            by_cases hji : j = i
            · simp only [memberDeformationPre, hji, ↓reduceDIte, coverPreimage]
              exact Or.inl trivial
            · have hx : x ∈ (hwell j).neighborhood := hza.resolve_left hji
              simp only [memberDeformationPre, hji, hx, ↓reduceDIte,
                coverPreimage]
              exact Or.inr ((hwell j).contraction (t, ⟨x, hx⟩)).property
      change Quotient.mk (setoid X x₀)
          (memberDeformationPre x₀ hwell i t a) ∈
        vanKampenCover x₀ hwell i
      change memberDeformationPre x₀ hwell i t a ∈
        (Quotient.mk (setoid X x₀)) ⁻¹' vanKampenCover x₀ hwell i
      rw [vanKampenCover, quotientMk_preimage_coverSet]
      exact hout

/-- The deformation restricted to the selected member of the wedge cover. -/
private def memberDeformationMap
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) (t : I) :
    vanKampenCover x₀ hwell i → vanKampenCover x₀ hwell i :=
  fun z ↦ ⟨memberDeformationPoint x₀ hwell i t z,
    memberDeformationPoint_mem x₀ hwell i t z.2⟩

private theorem memberDeformationMap_zero
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι)
    (z : vanKampenCover x₀ hwell i) :
    memberDeformationMap x₀ hwell i 0 z = z := by
  apply Subtype.ext
  rcases z with ⟨z, hz⟩
  induction z using Quotient.inductionOn with
  | _ a =>
      have hza : coverPreimage (fun j ↦ (hwell j).neighborhood) i a := by
        have hza' : a ∈
            (Quotient.mk (setoid X x₀)) ⁻¹'
              vanKampenCover x₀ hwell i := hz
        rw [vanKampenCover, quotientMk_preimage_coverSet] at hza'
        exact hza'
      cases a with
      | none => rfl
      | some p =>
          rcases p with ⟨j, x⟩
          by_cases hji : j = i
          · simp [memberDeformationMap, memberDeformationPoint,
              memberDeformationPre, hji]
          · have hx : x ∈ (hwell j).neighborhood := hza.resolve_left hji
            simp [memberDeformationMap, memberDeformationPoint,
              memberDeformationPre, hji, hx]

private theorem memberDeformationMap_fixed
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) (t : I) (x : X i) :
    memberDeformationMap x₀ hwell i t
        (vanKampenCoverInclusion x₀ hwell i x) =
      vanKampenCoverInclusion x₀ hwell i x := by
  apply Subtype.ext
  simp [memberDeformationMap, memberDeformationPoint,
    memberDeformationPre, vanKampenCoverInclusion,
    inclusionToSubset, inclusion]

private theorem memberDeformationMap_one
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι)
    (z : vanKampenCover x₀ hwell i) :
    memberDeformationMap x₀ hwell i 1 z =
      vanKampenCoverInclusion x₀ hwell i
        (vanKampenCoverRetraction x₀ hwell i z) := by
  rcases z with ⟨z, hz⟩
  apply Subtype.ext
  induction z using Quotient.inductionOn with
  | _ a =>
      have hza : coverPreimage (fun j ↦ (hwell j).neighborhood) i a := by
        have hza' : a ∈
            (Quotient.mk (setoid X x₀)) ⁻¹'
              vanKampenCover x₀ hwell i := hz
        rw [vanKampenCover, quotientMk_preimage_coverSet] at hza'
        exact hza'
      cases a with
      | none =>
          simp [memberDeformationMap, memberDeformationPoint,
            memberDeformationPre, vanKampenCoverInclusion,
            inclusionToSubset, vanKampenCoverRetraction,
            inclusion]
          exact (inclusion_basepoint x₀ i).symm
      | some p =>
          rcases p with ⟨j, x⟩
          by_cases hji : j = i
          · subst j
            simp [memberDeformationMap, memberDeformationPoint,
              memberDeformationPre, vanKampenCoverInclusion,
              inclusionToSubset, vanKampenCoverRetraction,
              inclusion]
            change inclusion x₀ i x =
              inclusion x₀ i (memberProjection x₀ i (inclusion x₀ i x))
            rw [memberProjection_inclusion_self]
          · have hx : x ∈ (hwell j).neighborhood := hza.resolve_left hji
            simp [memberDeformationMap, memberDeformationPoint,
              memberDeformationPre, hji, hx,
              vanKampenCoverInclusion, inclusionToSubset,
              vanKampenCoverRetraction, inclusion]
            change inclusion x₀ j (x₀ j) =
              inclusion x₀ i (memberProjection x₀ i (inclusion x₀ j x))
            rw [memberProjection_inclusion_of_ne x₀ hji]
            exact (inclusion_basepoint x₀ j).trans
              (inclusion_basepoint x₀ i).symm

/-- The fiber over `j` in the prequotient model of the `i`th cover member. -/
@[reducible]
private def coverFiber (hwell : ∀ i, WellPointedAt (x₀ i)) (i j : ι) :=
  {x : X j // j = i ∨ x ∈ (hwell j).neighborhood}

private theorem isOpen_coverFiber
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i j : ι) :
    IsOpen {x : X j | j = i ∨ x ∈ (hwell j).neighborhood} := by
  by_cases hji : j = i
  · simp [hji]
  · simpa [hji] using (hwell j).isOpen_neighborhood

/-- The prequotient model maps bijectively to the saturated cover preimage. -/
private def coverFiberPreimageEquiv
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    Option (Σ j, coverFiber x₀ hwell i j) ≃
      coverPreimage (fun j ↦ (hwell j).neighborhood) i where
  toFun
    | none => ⟨none, trivial⟩
    | some p => ⟨some ⟨p.1, p.2.1⟩, p.2.2⟩
  invFun z := by
    rcases z with ⟨z, hz⟩
    cases z with
    | none => exact none
    | some p =>
        have hp : p.1 = i ∨ p.2 ∈ (hwell p.1).neighborhood := hz
        exact some ⟨p.1, ⟨p.2, hp⟩⟩
  left_inv z := by
    cases z with
    | none => rfl
    | some p =>
        cases p
        rfl
  right_inv z := by
    rcases z with ⟨z, hz⟩
    cases z with
    | none => rfl
    | some p =>
        cases p
        rfl

section CoverFiberTopology

local instance : TopologicalSpace (Option (Σ j, X j)) :=
  prequotientTopology (X := X)

local instance (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    TopologicalSpace (Option (Σ j, coverFiber x₀ hwell i j)) :=
  prequotientTopology (X := fun j => coverFiber x₀ hwell i j)

/-- Forget the fiber membership proof. -/
private def coverFiberPreimageInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    Option (Σ j, coverFiber x₀ hwell i j) → Option (Σ j, X j)
  | none => none
  | some p => some ⟨p.1, p.2.1⟩

private theorem continuous_coverFiberPreimageInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    Continuous (coverFiberPreimageInclusion x₀ hwell i) := by
  change @Continuous (Option (Σ j, coverFiber x₀ hwell i j))
    (Option (Σ j, X j))
    (prequotientTopology (X := fun j => coverFiber x₀ hwell i j))
    (prequotientTopology (X := X)) _
  unfold prequotientTopology
  refine (continuous_sup_dom
    (f := coverFiberPreimageInclusion x₀ hwell i)
    (t₁ := TopologicalSpace.coinduced
      (fun z : Σ j, coverFiber x₀ hwell i j => some z) inferInstance)
    (t₂ := TopologicalSpace.coinduced
      (fun _ : Unit =>
        (none : Option (Σ j, coverFiber x₀ hwell i j))) inferInstance)).2 ?_
  constructor
  · rw [continuous_coinduced_dom, continuous_sigma_iff]
    intro j
    change Continuous fun x : coverFiber x₀ hwell i j =>
      (some ⟨j, (x : X j)⟩ : Option (Σ j, X j))
    have hsigma : Continuous fun x : coverFiber x₀ hwell i j =>
        (⟨j, (x : X j)⟩ : Σ j, X j) :=
      continuous_sigmaMk.comp continuous_subtype_val
    have hsome : @Continuous (Σ j, X j) (Option (Σ j, X j)) _
        (prequotientTopology (X := X)) some := by
      letI : TopologicalSpace (Option (Σ j, X j)) :=
        TopologicalSpace.coinduced (fun z : Σ j, X j => some z) inferInstance
      have h : Continuous (fun z : Σ j, X j => some z) :=
        continuous_coinduced_rng
      exact continuous_sup_rng_left h
    exact hsome.comp hsigma
  · rw [continuous_coinduced_dom]
    exact continuous_const

private theorem injective_coverFiberPreimageInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    Function.Injective (coverFiberPreimageInclusion x₀ hwell i) := by
  intro a b hab
  apply (coverFiberPreimageEquiv x₀ hwell i).injective
  apply Subtype.ext
  have hval : ∀ z,
      ((coverFiberPreimageEquiv x₀ hwell i z :
        coverPreimage (fun j ↦ (hwell j).neighborhood) i) :
          Option (Σ j, X j)) =
        coverFiberPreimageInclusion x₀ hwell i z := by
    intro z
    cases z with
    | none => rfl
    | some p => rfl
  rw [hval a, hval b]
  exact hab

private def coverFiberSigmaInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    (Σ j, coverFiber x₀ hwell i j) → Σ j, X j :=
  Sigma.map id fun _ x => x.1

private theorem isOpenEmbedding_coverFiberSigmaInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    IsOpenEmbedding (coverFiberSigmaInclusion x₀ hwell i) := by
  apply (Topology.isOpenEmbedding_sigmaMap Function.injective_id).2
  intro j
  exact (isOpen_coverFiber x₀ hwell i j).isOpenEmbedding_subtypeVal

private theorem isOpenMap_coverFiberPreimageInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    IsOpenMap (coverFiberPreimageInclusion x₀ hwell i) := by
  intro s hs
  change @IsOpen (Option (Σ j, X j))
    (prequotientTopology (X := X))
    (coverFiberPreimageInclusion x₀ hwell i '' s)
  change @IsOpen (Option (Σ j, coverFiber x₀ hwell i j))
    (prequotientTopology (X := fun j => coverFiber x₀ hwell i j)) s at hs
  unfold prequotientTopology at hs ⊢
  have hs' := (isOpen_sup
    (t₁ := TopologicalSpace.coinduced
      (fun z : Σ j, coverFiber x₀ hwell i j => some z) inferInstance)
    (t₂ := TopologicalSpace.coinduced
      (fun _ : Unit =>
        (none : Option (Σ j, coverFiber x₀ hwell i j))) inferInstance)).1 hs
  apply (isOpen_sup
    (t₁ := TopologicalSpace.coinduced
      (fun z : Σ j, X j => some z) inferInstance)
    (t₂ := TopologicalSpace.coinduced
      (fun _ : Unit => (none : Option (Σ j, X j))) inferInstance)).2
  constructor
  · rw [isOpen_coinduced] at hs' ⊢
    have hopen :=
      (isOpenEmbedding_coverFiberSigmaInclusion x₀ hwell i).isOpenMap
        _ hs'.1
    convert hopen using 1
    ext p
    constructor
    · rintro ⟨z, hzs, hz⟩
      cases z with
      | none => simp [coverFiberPreimageInclusion] at hz
      | some q =>
          refine ⟨q, hzs, ?_⟩
          exact Option.some.inj hz
    · rintro ⟨q, hqs, hq⟩
      refine ⟨some q, hqs, ?_⟩
      exact congrArg some hq
  · rw [isOpen_coinduced] at hs' ⊢
    simp [coverFiberPreimageInclusion]

private theorem isOpenEmbedding_coverFiberPreimageInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    IsOpenEmbedding (coverFiberPreimageInclusion x₀ hwell i) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_coverFiberPreimageInclusion x₀ hwell i)
    (injective_coverFiberPreimageInclusion x₀ hwell i)
    (isOpenMap_coverFiberPreimageInclusion x₀ hwell i)

@[simp]
private theorem coe_coverFiberPreimageEquiv
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι)
    (z : Option (Σ j, coverFiber x₀ hwell i j)) :
    ((coverFiberPreimageEquiv x₀ hwell i z :
      coverPreimage (fun j ↦ (hwell j).neighborhood) i) :
        Option (Σ j, X j)) =
      coverFiberPreimageInclusion x₀ hwell i z := by
  cases z with
  | none => rfl
  | some p => rfl

private theorem range_coverFiberPreimageInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    Set.range (coverFiberPreimageInclusion x₀ hwell i) =
      coverPreimage (fun j ↦ (hwell j).neighborhood) i := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    rw [← coe_coverFiberPreimageEquiv x₀ hwell i]
    exact (coverFiberPreimageEquiv x₀ hwell i a).property
  · intro hz
    let q : coverPreimage (fun j ↦ (hwell j).neighborhood) i := ⟨z, hz⟩
    refine ⟨(coverFiberPreimageEquiv x₀ hwell i).symm q, ?_⟩
    rw [← coe_coverFiberPreimageEquiv x₀ hwell i]
    exact congrArg Subtype.val
      ((coverFiberPreimageEquiv x₀ hwell i).apply_symm_apply q)

private noncomputable def coverFiberPreimageHomeomorph
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    Option (Σ j, coverFiber x₀ hwell i j) ≃ₜ
      coverPreimage (fun j ↦ (hwell j).neighborhood) i :=
  (isOpenEmbedding_coverFiberPreimageInclusion x₀ hwell i).toIsEmbedding
    |>.toHomeomorph |>.trans
      (Homeomorph.setCongr
        (range_coverFiberPreimageInclusion x₀ hwell i))

@[simp]
private theorem coe_coverFiberPreimageHomeomorph
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι)
    (z : Option (Σ j, coverFiber x₀ hwell i j)) :
    ((coverFiberPreimageHomeomorph x₀ hwell i z :
      coverPreimage (fun j ↦ (hwell j).neighborhood) i) :
        Option (Σ j, X j)) =
      coverFiberPreimageInclusion x₀ hwell i z := by
  rfl

private def coverFiberQuotientMap
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    Option (Σ j, coverFiber x₀ hwell i j) →
      vanKampenCover x₀ hwell i :=
  coverQuotientMap x₀ (fun j => (hwell j).neighborhood)
      (fun j => (hwell j).mem_neighborhood) i ∘
    coverFiberPreimageHomeomorph x₀ hwell i

@[simp]
private theorem coe_coverFiberQuotientMap
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι)
    (z : Option (Σ j, coverFiber x₀ hwell i j)) :
    ((coverFiberQuotientMap x₀ hwell i z :
      vanKampenCover x₀ hwell i) : Hatcher.PointedWedge X x₀) =
      Quotient.mk (setoid X x₀)
        (coverFiberPreimageInclusion x₀ hwell i z) := by
  rfl

private theorem isQuotientMap_coverFiberQuotientMap
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    IsQuotientMap (coverFiberQuotientMap x₀ hwell i) := by
  exact (isQuotientMap_coverQuotientMap x₀
    (fun j => (hwell j).neighborhood)
    (fun j => (hwell j).mem_neighborhood)
    (fun j => (hwell j).isOpen_neighborhood) i).comp
      (coverFiberPreimageHomeomorph x₀ hwell i).isQuotientMap

/-- The basepoint in each fiber of the cover-member prequotient model. -/
private def coverFiberBasepoint
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i j : ι) :
    coverFiber x₀ hwell i j :=
  ⟨x₀ j, Or.inr (hwell j).mem_neighborhood⟩

/-- The wedge point as a point of the selected cover member. -/
private def coverMemberBasepoint
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    vanKampenCover x₀ hwell i :=
  ⟨basepoint x₀, basepoint_mem_vanKampenCover x₀ hwell i⟩

/-- The member deformation on the fiber-valued prequotient model. -/
private def coverFiberDeformationPre
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    I × Option (Σ j, coverFiber x₀ hwell i j) →
      vanKampenCover x₀ hwell i
  | (_, none) => coverMemberBasepoint x₀ hwell i
  | (t, some p) =>
      if hji : p.1 = i then
        ⟨inclusion x₀ p.1 p.2.1, by
          change coverPreimage (fun j => (hwell j).neighborhood) i
            (some ⟨p.1, p.2.1⟩)
          exact p.2.2⟩
      else
        let hx : p.2.1 ∈ (hwell p.1).neighborhood :=
          p.2.2.resolve_left hji
        ⟨inclusion x₀ p.1
            ((hwell p.1).contraction (t, ⟨p.2.1, hx⟩)), by
          change coverPreimage (fun j => (hwell j).neighborhood) i
            (some ⟨p.1,
              ((hwell p.1).contraction (t, ⟨p.2.1, hx⟩) : X p.1)⟩)
          exact Or.inr ((hwell p.1).contraction
            (t, ⟨p.2.1, hx⟩)).property⟩

private theorem coverFiberDeformationPre_eq_of_eqvGen
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) (t : I)
    {a b : Option (Σ j, coverFiber x₀ hwell i j)}
    (h : Relation.EqvGen
      (Rel (fun j => coverFiber x₀ hwell i j)
        (coverFiberBasepoint x₀ hwell i)) a b) :
    coverFiberDeformationPre x₀ hwell i (t, a) =
      coverFiberDeformationPre x₀ hwell i (t, b) := by
  induction h with
  | rel a b h =>
      cases h with
      | base j =>
          by_cases hji : j = i
          · subst j
            simp [coverFiberDeformationPre, coverFiberBasepoint,
              coverMemberBasepoint]
          · simp only [coverFiberDeformationPre, coverFiberBasepoint,
              hji, ↓reduceDIte]
            apply Subtype.ext
            change basepoint x₀ = inclusion x₀ j
              (((hwell j).contraction
                (t, ⟨x₀ j, (hwell j).mem_neighborhood⟩) :
                  (hwell j).neighborhood) : X j)
            have hbase :
                (⟨x₀ j, (hwell j).mem_neighborhood⟩ :
                  (hwell j).neighborhood) =
                  (hwell j).neighborhoodBasepoint := by
              rfl
            rw [hbase, WellPointedAt.contraction_basepoint]
            exact (inclusion_basepoint x₀ j).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem continuous_coverFiberDeformationPre
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    Continuous (coverFiberDeformationPre x₀ hwell i) := by
  let hrel : ∀ t a b,
      (setoid (fun j => coverFiber x₀ hwell i j)
        (coverFiberBasepoint x₀ hwell i)).r a b →
      coverFiberDeformationPre x₀ hwell i (t, a) =
        coverFiberDeformationPre x₀ hwell i (t, b) :=
    fun t _ _ hab =>
      coverFiberDeformationPre_eq_of_eqvGen x₀ hwell i t hab
  have hquot : Continuous fun p : I × Hatcher.PointedWedge
      (fun j => coverFiber x₀ hwell i j)
      (coverFiberBasepoint x₀ hwell i) =>
      Quotient.lift
        (fun z => coverFiberDeformationPre x₀ hwell i (p.1, z))
        (hrel p.1) p.2 := by
    apply continuous_quotientLift_prod
      (x₀ := coverFiberBasepoint x₀ hwell i)
    · intro j
      by_cases hji : j = i
      · simp only [coverFiberDeformationPre, hji, ↓reduceDIte]
        apply Continuous.subtype_mk
        change Continuous fun p : I × coverFiber x₀ hwell i j =>
          inclusion x₀ j (p.2 : X j)
        exact (continuous_inclusion x₀ j).comp
          (continuous_subtype_val.comp continuous_snd)
      · simp only [coverFiberDeformationPre, hji, ↓reduceDIte]
        apply Continuous.subtype_mk
        change Continuous fun p : I × coverFiber x₀ hwell i j =>
          inclusion x₀ j
            ((hwell j).contraction
              (p.1, ⟨p.2.1, p.2.2.resolve_left hji⟩))
        have htoNeighborhood : Continuous fun x :
            coverFiber x₀ hwell i j =>
            (⟨x.1, x.2.resolve_left hji⟩ : (hwell j).neighborhood) :=
          Continuous.subtype_mk continuous_subtype_val _
        have hpair : Continuous fun p :
            I × coverFiber x₀ hwell i j =>
            (p.1, (⟨p.2.1, p.2.2.resolve_left hji⟩ :
              (hwell j).neighborhood)) :=
          continuous_fst.prodMk (htoNeighborhood.comp continuous_snd)
        exact (continuous_inclusion x₀ j).comp
          (continuous_subtype_val.comp
            ((hwell j).contraction.continuous.comp hpair))
    · exact continuous_const
  have hmk : Continuous fun p :
      I × Option (Σ j, coverFiber x₀ hwell i j) =>
      (p.1, Quotient.mk
        (setoid (fun j => coverFiber x₀ hwell i j)
          (coverFiberBasepoint x₀ hwell i)) p.2) := by
    exact continuous_fst.prodMk
      ((isQuotientMap_quotientMk
        (coverFiberBasepoint x₀ hwell i)).continuous.comp continuous_snd)
  apply (hquot.comp hmk).congr
  rintro ⟨t, z⟩
  rfl

private theorem memberDeformationMap_coverFiberQuotientMap
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) (t : I)
    (z : Option (Σ j, coverFiber x₀ hwell i j)) :
    memberDeformationMap x₀ hwell i t
        (coverFiberQuotientMap x₀ hwell i z) =
      coverFiberDeformationPre x₀ hwell i (t, z) := by
  cases z with
  | none => rfl
  | some p =>
      apply Subtype.ext
      by_cases hji : p.1 = i
      · simp [memberDeformationMap, memberDeformationPoint,
          coe_coverFiberQuotientMap, coverFiberPreimageInclusion,
          memberDeformationPre, coverFiberDeformationPre, hji]
        rfl
      · have hx : p.2.1 ∈ (hwell p.1).neighborhood :=
          p.2.2.resolve_left hji
        simp [memberDeformationMap, memberDeformationPoint,
          coe_coverFiberQuotientMap, coverFiberPreimageInclusion,
          memberDeformationPre, coverFiberDeformationPre, hji, hx]
        rfl

private theorem continuous_memberDeformationMap
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    Continuous fun p : I × vanKampenCover x₀ hwell i =>
      memberDeformationMap x₀ hwell i p.1 p.2 := by
  apply (isQuotientMap_coverFiberQuotientMap x₀ hwell i).continuous_lift_prod_right
  apply (continuous_coverFiberDeformationPre x₀ hwell i).congr
  rintro ⟨t, z⟩
  exact (memberDeformationMap_coverFiberQuotientMap
    x₀ hwell i t z).symm

private def memberDeformation
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    (ContinuousMap.id (vanKampenCover x₀ hwell i)).HomotopyRel
      ((vanKampenCoverInclusion x₀ hwell i).comp
        (vanKampenCoverRetraction x₀ hwell i))
      (Set.range (vanKampenCoverInclusion x₀ hwell i)) where
  toFun := fun p ↦ memberDeformationMap x₀ hwell i p.1 p.2
  continuous_toFun := continuous_memberDeformationMap x₀ hwell i
  map_zero_left := memberDeformationMap_zero x₀ hwell i
  map_one_left := memberDeformationMap_one x₀ hwell i
  prop' t z hz := by
    obtain ⟨x, rfl⟩ := hz
    exact memberDeformationMap_fixed x₀ hwell i t x

/-- Each standard wedge-cover member strongly deformation-retracts onto its
distinguished summand. -/
def vanKampenCoverStrongDeformationRetract
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    StrongDeformationRetract (vanKampenCoverInclusion x₀ hwell i) where
  retract := vanKampenCoverRetraction x₀ hwell i
  retract_inclusion := vanKampenCoverRetraction_comp_inclusion x₀ hwell i
  deformation := memberDeformation x₀ hwell i

/-- Path-connected summands give path-connected standard cover members. -/
theorem isPathConnected_vanKampenCover
    (hwell : ∀ i, WellPointedAt (x₀ i))
    [∀ i, PathConnectedSpace (X i)] (i : ι) :
    IsPathConnected (vanKampenCover x₀ hwell i) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  exact (vanKampenCoverStrongDeformationRetract x₀ hwell i).pathConnectedSpace

end CoverFiberTopology


end Hatcher.PointedWedge

