import Hatcher.VanKampen.WellPointedWedgeCover
import Mathlib.Topology.CompactOpen

noncomputable section

open Set
open scoped unitInterval

namespace Hatcher.PointedWedge

universe u v w

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
  (x₀ : ∀ i, X i)

/-- The common neck, modeled as the wedge of the chosen neighborhoods. -/
private abbrev commonNeckModel (hwell : ∀ i, WellPointedAt (x₀ i)) :=
  Hatcher.PointedWedge (fun i => (hwell i).neighborhood)
    (fun i => (hwell i).neighborhoodBasepoint)

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
  have hpaths : @Continuous (Hatcher.PointedWedge X x₀) C(I, Y)
      (instTopologicalSpace x₀) _ (Quotient.lift paths hpaths_rel) := by
    change @Continuous (Hatcher.PointedWedge X x₀) C(I, Y)
      (TopologicalSpace.coinduced
        (Quotient.mk (setoid X x₀) :
          Option (Σ i, X i) → Hatcher.PointedWedge X x₀)
        (TopologicalSpace.coinduced
            (fun z : Σ i, X i => some z) inferInstance ⊔
          TopologicalSpace.coinduced
            (fun _ : Unit => (none : Option (Σ i, X i))) inferInstance))
      _ (Quotient.lift paths hpaths_rel)
    rw [continuous_coinduced_dom]
    change @Continuous (Option (Σ i, X i)) C(I, Y)
      (TopologicalSpace.coinduced
          (fun z : Σ i, X i => some z) inferInstance ⊔
        TopologicalSpace.coinduced
          (fun _ : Unit => (none : Option (Σ i, X i))) inferInstance)
      _ paths
    rw [continuous_sup_dom]
    constructor
    · rw [continuous_coinduced_dom, continuous_sigma_iff]
      exact hpaths_summand
    · rw [continuous_coinduced_dom]
      fun_prop
  have huncurry : Continuous fun p : Hatcher.PointedWedge X x₀ × I =>
      Quotient.lift paths hpaths_rel p.1 p.2 :=
    ContinuousMap.continuous_uncurry_of_continuous ⟨_, hpaths⟩
  apply (huncurry.comp continuous_swap).congr
  rintro ⟨t, z⟩
  induction z using Quotient.inductionOn with
  | _ z => rfl


/-- The wedge point, regarded as a point of the actual common neck. -/
def vanKampenNeckBasepoint (hwell : ∀ i, WellPointedAt (x₀ i)) :
    vanKampenNeck x₀ hwell :=
  ⟨basepoint x₀, by
    change neckPreimage (fun i ↦ (hwell i).neighborhood) none
    trivial⟩

/-- Apply the chosen contraction on representatives in the neck, and send
representatives outside the neck to the wedge point. -/
private def vanKampenNeckPreContraction
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    I × Option (Σ i, X i) → vanKampenNeck x₀ hwell := by
  classical
  rintro ⟨t, a⟩
  cases a with
  | none => exact vanKampenNeckBasepoint x₀ hwell
  | some p =>
      by_cases hp : p.2 ∈ (hwell p.1).neighborhood
      · exact ⟨inclusion x₀ p.1
            ((hwell p.1).contraction (t, ⟨p.2, hp⟩)), by
          change ((hwell p.1).contraction (t, ⟨p.2, hp⟩) : X p.1) ∈
            (hwell p.1).neighborhood
          exact ((hwell p.1).contraction (t, ⟨p.2, hp⟩)).property⟩
      · exact vanKampenNeckBasepoint x₀ hwell

private theorem vanKampenNeckPreContraction_eq_of_eqvGen
    (hwell : ∀ i, WellPointedAt (x₀ i)) (t : I)
    {a b : Option (Σ i, X i)}
    (h : Relation.EqvGen (Rel X x₀) a b) :
    vanKampenNeckPreContraction x₀ hwell (t, a) =
    vanKampenNeckPreContraction x₀ hwell (t, b) := by
  classical
  induction h with
  | rel a b h =>
      cases h with
      | base i =>
          simp only [vanKampenNeckPreContraction]
          rw [dif_pos (hwell i).mem_neighborhood]
          apply Subtype.ext
          change basepoint x₀ = inclusion x₀ i
            ((hwell i).contraction
              (t, ⟨x₀ i, (hwell i).mem_neighborhood⟩))
          have hbase :
              (⟨x₀ i, (hwell i).mem_neighborhood⟩ :
                (hwell i).neighborhood) =
                (hwell i).neighborhoodBasepoint := by
            apply Subtype.ext
            rfl
          rw [hbase, WellPointedAt.contraction_basepoint]
          exact (inclusion_basepoint x₀ i).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The set-theoretic simultaneous contraction on the actual common neck. -/
private def vanKampenNeckContractionMap
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    I × vanKampenNeck x₀ hwell → vanKampenNeck x₀ hwell :=
  fun p => Quotient.lift
    (fun a => vanKampenNeckPreContraction x₀ hwell (p.1, a))
    (fun _ _ h => vanKampenNeckPreContraction_eq_of_eqvGen
      x₀ hwell p.1 h) p.2.1

/-- Representatives of the actual common neck are the optional dependent sum
of the chosen neighborhoods. -/
private def commonNeckPreimageEquiv
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    Option (Σ i, (hwell i).neighborhood) ≃
      vanKampenNeckPreimage x₀ hwell where
  toFun
    | none => ⟨none, trivial⟩
    | some p => ⟨some ⟨p.1, p.2.1⟩, p.2.2⟩
  invFun z := by
    rcases z with ⟨z, hz⟩
    cases z with
    | none => exact none
    | some p =>
        have hp : p.2 ∈ (hwell p.1).neighborhood := by
          exact hz
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

section PrequotientTopology

local instance neckAmbientPrequotientTopologyInstance :
    TopologicalSpace (Option (Σ i, X i)) :=
  prequotientTopology (X := X)

local instance neckModelPrequotientTopologyInstance
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    TopologicalSpace (Option (Σ i, (hwell i).neighborhood)) :=
  prequotientTopology (X := fun i => (hwell i).neighborhood)

private theorem continuous_commonNeckPreimageEquiv
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    Continuous (commonNeckPreimageEquiv x₀ hwell) := by
  change @Continuous (Option (Σ i, (hwell i).neighborhood))
    (vanKampenNeckPreimage x₀ hwell)
    (prequotientTopology (X := fun i => (hwell i).neighborhood)) _ _
  unfold prequotientTopology
  refine (continuous_sup_dom
    (f := fun z => commonNeckPreimageEquiv x₀ hwell z)
    (t₁ := TopologicalSpace.coinduced
      (fun z : Σ i, (hwell i).neighborhood => some z) inferInstance)
    (t₂ := TopologicalSpace.coinduced
      (fun _ : Unit =>
        (none : Option (Σ i, (hwell i).neighborhood))) inferInstance)).2 ?_
  constructor
  · rw [continuous_coinduced_dom, continuous_sigma_iff]
    intro i
    apply Continuous.subtype_mk
    change Continuous fun x : (hwell i).neighborhood =>
      (some ⟨i, (x : X i)⟩ : Option (Σ i, X i))
    have hsigma : Continuous fun x : (hwell i).neighborhood =>
        (⟨i, (x : X i)⟩ : Σ i, X i) :=
      continuous_sigmaMk.comp continuous_subtype_val
    have hsome : @Continuous (Σ i, X i) (Option (Σ i, X i)) _
        (prequotientTopology (X := X)) some := by
      letI : TopologicalSpace (Option (Σ i, X i)) :=
        TopologicalSpace.coinduced (fun z : Σ i, X i => some z) inferInstance
      have h : Continuous (fun z : Σ i, X i => some z) :=
        continuous_coinduced_rng
      exact continuous_sup_rng_left h
    exact hsome.comp hsigma
  · rw [continuous_coinduced_dom]
    exact continuous_const

/-- Forget that a representative lies in its chosen neighborhood. -/
private def commonNeckPreimageInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    Option (Σ i, (hwell i).neighborhood) → Option (Σ i, X i)
  | none => none
  | some p => some ⟨p.1, p.2.1⟩

private theorem continuous_commonNeckPreimageInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    Continuous (commonNeckPreimageInclusion x₀ hwell) := by
  change @Continuous (Option (Σ i, (hwell i).neighborhood))
    (Option (Σ i, X i))
    (prequotientTopology (X := fun i => (hwell i).neighborhood))
    (prequotientTopology (X := X)) _
  unfold prequotientTopology
  refine (continuous_sup_dom
    (f := commonNeckPreimageInclusion x₀ hwell)
    (t₁ := TopologicalSpace.coinduced
      (fun z : Σ i, (hwell i).neighborhood => some z) inferInstance)
    (t₂ := TopologicalSpace.coinduced
      (fun _ : Unit =>
        (none : Option (Σ i, (hwell i).neighborhood))) inferInstance)).2 ?_
  constructor
  · rw [continuous_coinduced_dom, continuous_sigma_iff]
    intro i
    change Continuous fun x : (hwell i).neighborhood =>
      (some ⟨i, (x : X i)⟩ : Option (Σ i, X i))
    have hsigma : Continuous fun x : (hwell i).neighborhood =>
        (⟨i, (x : X i)⟩ : Σ i, X i) :=
      continuous_sigmaMk.comp continuous_subtype_val
    have hsome : @Continuous (Σ i, X i) (Option (Σ i, X i)) _
        (prequotientTopology (X := X)) some := by
      letI : TopologicalSpace (Option (Σ i, X i)) :=
        TopologicalSpace.coinduced (fun z : Σ i, X i => some z) inferInstance
      have h : Continuous (fun z : Σ i, X i => some z) :=
        continuous_coinduced_rng
      exact continuous_sup_rng_left h
    exact hsome.comp hsigma
  · rw [continuous_coinduced_dom]
    exact continuous_const

private theorem injective_commonNeckPreimageInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    Function.Injective (commonNeckPreimageInclusion x₀ hwell) := by
  intro a b hab
  apply (commonNeckPreimageEquiv x₀ hwell).injective
  apply Subtype.ext
  have hval : ∀ z,
      ((commonNeckPreimageEquiv x₀ hwell z :
        vanKampenNeckPreimage x₀ hwell) : Option (Σ i, X i)) =
        commonNeckPreimageInclusion x₀ hwell z := by
    intro z
    cases z with
    | none => rfl
    | some p => rfl
  rw [hval a, hval b]
  exact hab

/-- Inclusion of the dependent sum of chosen neighborhoods into the
dependent sum of the ambient summands. -/
private def commonNeckSigmaInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    (Σ i, (hwell i).neighborhood) → Σ i, X i :=
  Sigma.map id fun _ x => x.1

private theorem isOpenEmbedding_commonNeckSigmaInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    Topology.IsOpenEmbedding (commonNeckSigmaInclusion x₀ hwell) := by
  apply (Topology.isOpenEmbedding_sigmaMap Function.injective_id).2
  intro i
  exact (hwell i).isOpen_neighborhood.isOpenEmbedding_subtypeVal

private theorem isOpenMap_commonNeckPreimageInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    IsOpenMap (commonNeckPreimageInclusion x₀ hwell) := by
  intro s hs
  change @IsOpen (Option (Σ i, X i))
    (prequotientTopology (X := X))
    (commonNeckPreimageInclusion x₀ hwell '' s)
  change @IsOpen (Option (Σ i, (hwell i).neighborhood))
    (prequotientTopology (X := fun i => (hwell i).neighborhood)) s at hs
  unfold prequotientTopology at hs ⊢
  have hs' := (isOpen_sup
    (t₁ := TopologicalSpace.coinduced
      (fun z : Σ i, (hwell i).neighborhood => some z) inferInstance)
    (t₂ := TopologicalSpace.coinduced
      (fun _ : Unit =>
        (none : Option (Σ i, (hwell i).neighborhood))) inferInstance)).1 hs
  apply (isOpen_sup
    (t₁ := TopologicalSpace.coinduced
      (fun z : Σ i, X i => some z) inferInstance)
    (t₂ := TopologicalSpace.coinduced
      (fun _ : Unit => (none : Option (Σ i, X i))) inferInstance)).2
  constructor
  · rw [isOpen_coinduced] at hs' ⊢
    have hopen :=
      (isOpenEmbedding_commonNeckSigmaInclusion x₀ hwell).isOpenMap
        _ hs'.1
    convert hopen using 1
    ext p
    constructor
    · rintro ⟨z, hzs, hz⟩
      cases z with
      | none => simp [commonNeckPreimageInclusion] at hz
      | some q =>
          refine ⟨q, hzs, ?_⟩
          exact Option.some.inj hz
    · rintro ⟨q, hqs, hq⟩
      refine ⟨some q, hqs, ?_⟩
      exact congrArg some hq
  · rw [isOpen_coinduced] at hs' ⊢
    simp [commonNeckPreimageInclusion]

private theorem isOpenEmbedding_commonNeckPreimageInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    Topology.IsOpenEmbedding
      (commonNeckPreimageInclusion x₀ hwell) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_commonNeckPreimageInclusion x₀ hwell)
    (injective_commonNeckPreimageInclusion x₀ hwell)
    (isOpenMap_commonNeckPreimageInclusion x₀ hwell)

@[simp]
private theorem coe_commonNeckPreimageEquiv
    (hwell : ∀ i, WellPointedAt (x₀ i))
    (z : Option (Σ i, (hwell i).neighborhood)) :
    ((commonNeckPreimageEquiv x₀ hwell z :
      vanKampenNeckPreimage x₀ hwell) : Option (Σ i, X i)) =
      commonNeckPreimageInclusion x₀ hwell z := by
  cases z with
  | none => rfl
  | some p => rfl

private theorem range_commonNeckPreimageInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    Set.range (commonNeckPreimageInclusion x₀ hwell) =
      vanKampenNeckPreimage x₀ hwell := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    rw [← coe_commonNeckPreimageEquiv x₀ hwell]
    exact (commonNeckPreimageEquiv x₀ hwell a).property
  · intro hz
    let q : vanKampenNeckPreimage x₀ hwell := ⟨z, hz⟩
    refine ⟨(commonNeckPreimageEquiv x₀ hwell).symm q, ?_⟩
    rw [← coe_commonNeckPreimageEquiv x₀ hwell]
    exact congrArg Subtype.val
      ((commonNeckPreimageEquiv x₀ hwell).apply_symm_apply q)

/-- The prequotient of the neighborhood wedge is homeomorphic to the
saturated preimage of the actual common neck. -/
private noncomputable def commonNeckPreimageHomeomorph
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    Option (Σ i, (hwell i).neighborhood) ≃ₜ
      vanKampenNeckPreimage x₀ hwell :=
  (isOpenEmbedding_commonNeckPreimageInclusion x₀ hwell).toIsEmbedding
    |>.toHomeomorph |>.trans
      (Homeomorph.setCongr (range_commonNeckPreimageInclusion x₀ hwell))

@[simp]
private theorem coe_commonNeckPreimageHomeomorph
    (hwell : ∀ i, WellPointedAt (x₀ i))
    (z : Option (Σ i, (hwell i).neighborhood)) :
    ((commonNeckPreimageHomeomorph x₀ hwell z :
      vanKampenNeckPreimage x₀ hwell) : Option (Σ i, X i)) =
      commonNeckPreimageInclusion x₀ hwell z := by
  rfl

/-- The quotient map from neighborhood representatives directly onto the
actual common neck. -/
private def commonNeckQuotientMap
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    Option (Σ i, (hwell i).neighborhood) → vanKampenNeck x₀ hwell :=
  neckQuotientMap x₀ (fun i => (hwell i).neighborhood)
      (fun i => (hwell i).mem_neighborhood) ∘
    commonNeckPreimageHomeomorph x₀ hwell

@[simp]
private theorem coe_commonNeckQuotientMap
    (hwell : ∀ i, WellPointedAt (x₀ i))
    (z : Option (Σ i, (hwell i).neighborhood)) :
    ((commonNeckQuotientMap x₀ hwell z :
      vanKampenNeck x₀ hwell) : Hatcher.PointedWedge X x₀) =
      Quotient.mk (setoid X x₀)
        (commonNeckPreimageInclusion x₀ hwell z) := by
  rfl

private theorem isQuotientMap_commonNeckQuotientMap
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    Topology.IsQuotientMap (commonNeckQuotientMap x₀ hwell) := by
  exact (isQuotientMap_neckQuotientMap x₀
    (fun i => (hwell i).neighborhood)
    (fun i => (hwell i).mem_neighborhood)
    (fun i => (hwell i).isOpen_neighborhood)).comp
      (commonNeckPreimageHomeomorph x₀ hwell).isQuotientMap

/-- The contraction formula on neighborhood-valued representatives, now
regarded as taking values in the actual common neck. -/
private def commonNeckActualPreContraction
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    I × Option (Σ i, (hwell i).neighborhood) →
      vanKampenNeck x₀ hwell
  | (_, none) => vanKampenNeckBasepoint x₀ hwell
  | (t, some p) =>
      ⟨inclusion x₀ p.1 ((hwell p.1).contraction (t, p.2)), by
        change ((hwell p.1).contraction (t, p.2) : X p.1) ∈
          (hwell p.1).neighborhood
        exact ((hwell p.1).contraction (t, p.2)).property⟩

private theorem commonNeckActualPreContraction_eq_of_eqvGen
    (hwell : ∀ i, WellPointedAt (x₀ i)) (t : I)
    {a b : Option (Σ i, (hwell i).neighborhood)}
    (h : Relation.EqvGen
      (Rel (fun i => (hwell i).neighborhood)
        (fun i => (hwell i).neighborhoodBasepoint)) a b) :
    commonNeckActualPreContraction x₀ hwell (t, a) =
      commonNeckActualPreContraction x₀ hwell (t, b) := by
  induction h with
  | rel a b h =>
      cases h with
      | base i =>
          simp [commonNeckActualPreContraction,
            WellPointedAt.contraction_basepoint,
            vanKampenNeckBasepoint]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem continuous_commonNeckActualPreContraction
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    Continuous (commonNeckActualPreContraction x₀ hwell) := by
  let hrel : ∀ t a b,
      (setoid (fun i => (hwell i).neighborhood)
        (fun i => (hwell i).neighborhoodBasepoint)).r a b →
      commonNeckActualPreContraction x₀ hwell (t, a) =
        commonNeckActualPreContraction x₀ hwell (t, b) :=
    fun t _ _ hab =>
      commonNeckActualPreContraction_eq_of_eqvGen x₀ hwell t hab
  have hquot : Continuous fun p : I × commonNeckModel x₀ hwell =>
      Quotient.lift
        (fun z => commonNeckActualPreContraction x₀ hwell (p.1, z))
        (hrel p.1) p.2 := by
    apply continuous_quotientLift_prod
      (x₀ := fun i => (hwell i).neighborhoodBasepoint)
    · intro i
      apply Continuous.subtype_mk
      change Continuous fun p : I × (hwell i).neighborhood =>
        inclusion x₀ i ((hwell i).contraction p)
      exact (continuous_inclusion x₀ i).comp
        (continuous_subtype_val.comp (hwell i).contraction.continuous)
    · exact continuous_const
  have hmk : Continuous fun p :
      I × Option (Σ i, (hwell i).neighborhood) =>
      (p.1, Quotient.mk
        (setoid (fun i => (hwell i).neighborhood)
          (fun i => (hwell i).neighborhoodBasepoint)) p.2) := by
    exact continuous_fst.prodMk
      ((isQuotientMap_quotientMk
        (fun i => (hwell i).neighborhoodBasepoint)).continuous.comp
          continuous_snd)
  apply (hquot.comp hmk).congr
  rintro ⟨t, z⟩
  rfl

private theorem vanKampenNeckContractionMap_commonNeckQuotientMap
    (hwell : ∀ i, WellPointedAt (x₀ i)) (t : I)
    (z : Option (Σ i, (hwell i).neighborhood)) :
    vanKampenNeckContractionMap x₀ hwell
        (t, commonNeckQuotientMap x₀ hwell z) =
      commonNeckActualPreContraction x₀ hwell (t, z) := by
  cases z with
  | none => rfl
  | some p =>
      apply Subtype.ext
      simp [vanKampenNeckContractionMap, coe_commonNeckQuotientMap,
        commonNeckPreimageInclusion, vanKampenNeckPreContraction,
        commonNeckActualPreContraction]

private theorem continuous_vanKampenNeckContractionMap
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    Continuous (vanKampenNeckContractionMap x₀ hwell) := by
  apply (isQuotientMap_commonNeckQuotientMap x₀ hwell).continuous_lift_prod_right
  apply (continuous_commonNeckActualPreContraction x₀ hwell).congr
  rintro ⟨t, z⟩
  exact (vanKampenNeckContractionMap_commonNeckQuotientMap
    x₀ hwell t z).symm

@[simp]
private theorem commonNeckActualPreContraction_zero
    (hwell : ∀ i, WellPointedAt (x₀ i))
    (z : Option (Σ i, (hwell i).neighborhood)) :
    commonNeckActualPreContraction x₀ hwell (0, z) =
      commonNeckQuotientMap x₀ hwell z := by
  cases z with
  | none => rfl
  | some p =>
      apply Subtype.ext
      rw [coe_commonNeckQuotientMap]
      simp [commonNeckActualPreContraction, commonNeckPreimageInclusion]
      cases p
      rfl

@[simp]
private theorem commonNeckActualPreContraction_one
    (hwell : ∀ i, WellPointedAt (x₀ i))
    (z : Option (Σ i, (hwell i).neighborhood)) :
    commonNeckActualPreContraction x₀ hwell (1, z) =
      vanKampenNeckBasepoint x₀ hwell := by
  cases z with
  | none => rfl
  | some p =>
      apply Subtype.ext
      change inclusion x₀ p.1
          (((hwell p.1).contraction (1, p.2) :
            (hwell p.1).neighborhood) : X p.1) = basepoint x₀
      rw [WellPointedAt.contraction_one]
      exact inclusion_basepoint x₀ p.1

@[simp]
private theorem vanKampenNeckContractionMap_zero
    (hwell : ∀ i, WellPointedAt (x₀ i))
    (z : vanKampenNeck x₀ hwell) :
    vanKampenNeckContractionMap x₀ hwell (0, z) = z := by
  obtain ⟨a, rfl⟩ :=
    (isQuotientMap_commonNeckQuotientMap x₀ hwell).surjective z
  rw [vanKampenNeckContractionMap_commonNeckQuotientMap,
    commonNeckActualPreContraction_zero]

@[simp]
private theorem vanKampenNeckContractionMap_one
    (hwell : ∀ i, WellPointedAt (x₀ i))
    (z : vanKampenNeck x₀ hwell) :
    vanKampenNeckContractionMap x₀ hwell (1, z) =
      vanKampenNeckBasepoint x₀ hwell := by
  obtain ⟨a, rfl⟩ :=
    (isQuotientMap_commonNeckQuotientMap x₀ hwell).surjective z
  rw [vanKampenNeckContractionMap_commonNeckQuotientMap,
    commonNeckActualPreContraction_one]

@[simp]
private theorem vanKampenNeckContractionMap_basepoint
    (hwell : ∀ i, WellPointedAt (x₀ i)) (t : I) :
    vanKampenNeckContractionMap x₀ hwell
        (t, vanKampenNeckBasepoint x₀ hwell) =
      vanKampenNeckBasepoint x₀ hwell := by
  have hnone : commonNeckQuotientMap x₀ hwell none =
      vanKampenNeckBasepoint x₀ hwell := by
    rfl
  rw [← hnone,
    vanKampenNeckContractionMap_commonNeckQuotientMap]
  rfl

/-- The actual common neck contracts to the wedge point while fixing that
point throughout. -/
def vanKampenNeckContraction
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    (ContinuousMap.id (vanKampenNeck x₀ hwell)).HomotopyRel
      (ContinuousMap.const (vanKampenNeck x₀ hwell)
        (vanKampenNeckBasepoint x₀ hwell))
      {vanKampenNeckBasepoint x₀ hwell} where
  toFun := vanKampenNeckContractionMap x₀ hwell
  continuous_toFun := continuous_vanKampenNeckContractionMap x₀ hwell
  map_zero_left := vanKampenNeckContractionMap_zero x₀ hwell
  map_one_left := vanKampenNeckContractionMap_one x₀ hwell
  prop' t z hz := by
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact vanKampenNeckContractionMap_basepoint x₀ hwell t

/-- The common neck is contractible. -/
theorem contractibleSpace_vanKampenNeck
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    ContractibleSpace (vanKampenNeck x₀ hwell) :=
  StrongDeformationRetract.contractibleSpace_of_pointedContraction
    (vanKampenNeckBasepoint x₀ hwell)
    (vanKampenNeckContraction x₀ hwell)

/-- The common neck is path-connected. -/
theorem isPathConnected_vanKampenNeck
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    IsPathConnected (vanKampenNeck x₀ hwell) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  letI : ContractibleSpace (vanKampenNeck x₀ hwell) :=
    contractibleSpace_vanKampenNeck x₀ hwell
  infer_instance

end PrequotientTopology

end Hatcher.PointedWedge
