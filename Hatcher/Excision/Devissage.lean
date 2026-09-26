/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Joël Riou

This file adapts the relative dévissage argument from
`joelriou/excision` at commit `8b56cd0c8e5f39a7c2f36418c80b298e469596a6`
to the Mathlib version pinned by this project.
-/

import Mathlib.Algebra.Homology.HomotopyCategory.ChainComplex
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Relative-chain dévissage

This file identifies the homotopy-equivalence property of a map of relative
simplicial chain complexes with that of the corresponding union subcomplex.
It is the categorical chain-level quotient comparison used in Hatcher's proof
of excision.
-/

noncomputable section

open CategoryTheory Limits Simplicial HomologicalComplex Opposite

namespace Hatcher.Excision

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

section SigmaConst

variable (R : C) {α β : Type w} (f : α → β) (hf : Function.Injective f)

/-- The short complex associated to the standard cokernel presentation of a
map between coproducts of copies of `R`. -/
private noncomputable abbrev sigmaConstCokernelShortComplex : ShortComplex C :=
  .mk _ _ (sigmaConstCokernelCofork R f).condition

/-- The standard cokernel presentation of an injective map of coproduct bases
is split. -/
private noncomputable def splittingSigmaConstCokernelShortComplex :
    (sigmaConstCokernelShortComplex R f).Splitting := by
  classical
  have hchoose (b : β) (hb : b ∈ Set.range f) : ∃ a, f a = b := hb
  choose ρ hρ using hchoose
  have hρ' (a : α) : ρ (f a) (by simp) = a := hf (hρ _ _)
  exact
    { r := Sigma.desc (fun b ↦
        if hb : b ∈ Set.range f then Sigma.ι (fun _ ↦ R) (ρ b hb) else 0)
      s := Sigma.desc (fun ⟨c, _⟩ ↦ Sigma.ι (fun _ ↦ R) c)
      s_g := by
        dsimp
        ext ⟨c, hc⟩
        simp only [Set.mem_compl_iff, Set.mem_range, not_exists] at hc
        dsimp [sigmaConstCokernelCofork]
        aesop
      id := by
        dsimp
        ext b
        by_cases hb : b ∈ Set.range f
        · obtain ⟨a, rfl⟩ := hb
          aesop
        · dsimp [sigmaConstCokernelCofork]
          rw [Preadditive.comp_add, Sigma.ι_comp_desc_assoc, dite_eq_right hb,
            Sigma.ι_comp_desc_assoc, dite_eq_left (by simpa using hb)]
          simp }

/-- Transport the standard splitting to any chosen colimit cokernel cofork. -/
private noncomputable def splittingSigmaConstCokernelShortComplex'
    {c : CokernelCofork
      (Sigma.map' (f := fun (_ : β) ↦ R) (g := fun (_ : α) ↦ R) f (fun _ ↦ 𝟙 R))}
    (hc : IsColimit c) :
    (ShortComplex.mk _ _ c.condition).Splitting :=
  (splittingSigmaConstCokernelShortComplex R f hf).ofIso
    ((ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (IsColimit.coconePointUniqueUpToIso (isColimitSigmaConstCokernelCofork R f) hc)
      (by cat_disch) (by
      simp [dsimp% (IsColimit.comp_coconePointUniqueUpToIso_hom
        (isColimitSigmaConstCokernelCofork R f) hc) .one])))

end SigmaConst

section PairBasics

@[simp] private lemma subcomplex_pair_left {X : SSet.{w}} (A : X.Subcomplex) :
    A.pair.left = A := rfl

@[simp] private lemma subcomplex_pair_right {X : SSet.{w}} (A : X.Subcomplex) :
    A.pair.right = X := rfl

@[simp] private lemma subcomplex_pair_hom {X : SSet.{w}} (A : X.Subcomplex) :
    A.pair.hom = A.ι := rfl

@[simp] private lemma pair_of_left {X Y : SSet.{w}} (i : X ⟶ Y) [Mono i] :
    (SSetPair.of i).left = X := rfl

@[simp] private lemma pair_of_right {X Y : SSet.{w}} (i : X ⟶ Y) [Mono i] :
    (SSetPair.of i).right = Y := rfl

@[simp] private lemma pair_of_hom {X Y : SSet.{w}} (i : X ⟶ Y) [Mono i] :
    (SSetPair.of i).hom = i := rfl

/-- Constructor for isomorphisms of simplicial-set pairs. -/
private abbrev pairIsoMk {X Y : SSetPair.{w}}
    (e₁ : X.left ≅ Y.left) (e₂ : X.right ≅ Y.right)
    (h : e₁.hom ≫ Y.hom = X.hom ≫ e₂.hom := by cat_disch) : X ≅ Y :=
  MorphismProperty.Arrow.isoMk e₁ e₂ h

end PairBasics

section RelativeChainHelpers

variable {X : SSetPair.{w}}

@[reassoc (attr := simp)]
private lemma iota_chainComplex_pi_f_eq_zero
    (X : SSetPair.{w}) (R : C) {n : ℕ} (x : X.left _⦋n⦌) :
    dsimp% X.right.ιChainComplex (X.hom.app _ x) ≫
      (X.chainComplexπ R).f n = 0 := by
  simpa only [comp_zero, SSet.ι_chainComplexMap_f_assoc] using!
    X.left.ιChainComplex x ≫= X.chainComplex_condition_f R n

@[reassoc]
private lemma iota_chainComplex_pi_f_eq_zero_of_mem_range
    (X : SSetPair.{w}) (R : C) {n : ℕ} (x : X.right _⦋n⦌)
    (hx : x ∈ Set.range (X.hom.app _)) :
    X.right.ιChainComplex x ≫ (X.chainComplexπ R).f n = 0 := by
  obtain ⟨x, rfl⟩ := hx
  rw [iota_chainComplex_pi_f_eq_zero]

@[reassoc]
private lemma iota_chainComplex_pi_f_eq_zero_of_subcomplex
    {X : SSet.{w}} (A : X.Subcomplex) (R : C) {n : ℕ}
    (x : X _⦋n⦌) (hx : x ∈ A.obj _) :
    X.ιChainComplex x ≫ (A.pair.chainComplexπ R).f n = 0 :=
  iota_chainComplex_pi_f_eq_zero_of_mem_range A.pair R _ ⟨⟨x, hx⟩, rfl⟩

private lemma chainComplexX_hom_ext {X : SSetPair.{w}} {R T : C} {n : ℕ}
    {f g : (X.chainComplex R).X n ⟶ T}
    (h : ∀ (x : X.right _⦋n⦌) (_ : x ∉ Set.range (X.hom.app (op ⦋n⦌))),
      X.right.ιChainComplex x ≫ (X.chainComplexπ R).f n ≫ f =
      X.right.ιChainComplex x ≫ (X.chainComplexπ R).f n ≫ g) : f = g := by
  rw [← cancel_epi ((X.chainComplexπ R).f n)]
  ext x
  by_cases hx : x ∈ Set.range (X.hom.app (op ⦋n⦌))
  · simp [iota_chainComplex_pi_f_eq_zero_of_mem_range_assoc X R x hx]
  · exact h _ hx

section Desc

variable {R T : C} {n : ℕ}
  (f : X.right _⦋n⦌ → (R ⟶ T))
  (hf : ∀ (x : X.left _⦋n⦌), f (X.hom.app _ x) = 0)

/-- Descend maps on simplices through a relative-chain quotient. -/
private noncomputable def chainComplexXDesc :
    (X.chainComplex R).X n ⟶ T :=
  (CokernelCofork.IsColimit.desc' (X.isColimitCokernelCoforkChainComplexX R n)
    (Sigma.desc f) (by
      ext x
      simp only [Functor.id_obj, SSet.ι_chainComplexMap_f_assoc, comp_zero]
      exact (Sigma.ι_comp_desc ..).trans (hf x))).1

@[reassoc]
private lemma iota_chainComplexXDesc (x : X.right _⦋n⦌) :
    X.right.ιChainComplex x ≫ (X.chainComplexπ R).f n ≫
      chainComplexXDesc f hf = f x := by
  have hdesc : (X.chainComplexπ R).f n ≫ chainComplexXDesc f hf = Sigma.desc f :=
    (CokernelCofork.IsColimit.desc' (X.isColimitCokernelCoforkChainComplexX R n)
      (Sigma.desc f) _).2
  rw [hdesc]
  apply Sigma.ι_comp_desc

end Desc

@[reassoc]
private lemma chainComplex_pi_naturality {X Y : SSetPair.{w}}
    (f : X ⟶ Y) (R : C) :
    X.chainComplexπ R ≫ SSetPair.chainComplexMap f R =
      SSet.chainComplexMap f.right R ≫ Y.chainComplexπ R :=
  (((SSetPair.chainComplexFunctorπ C).app R).naturality f).symm

@[reassoc]
private lemma chainComplex_pi_f_naturality {X Y : SSetPair.{w}}
    (f : X ⟶ Y) (R : C) (n : ℕ) :
    (X.chainComplexπ R).f n ≫ (SSetPair.chainComplexMap f R).f n =
      (SSet.chainComplexMap f.right R).f n ≫ (Y.chainComplexπ R).f n := by
  simp only [← HomologicalComplex.comp_f, chainComplex_pi_naturality]

@[reassoc (attr := simp)]
private lemma iota_chainComplexMap_f {X Y : SSetPair.{w}}
    (f : X ⟶ Y) (R : C) {n : ℕ} (x : X.right _⦋n⦌) :
    X.right.ιChainComplex x ≫ (X.chainComplexπ R).f n ≫
      (SSetPair.chainComplexMap f R).f n =
      Y.right.ιChainComplex (f.right.app _ x) ≫
        (Y.chainComplexπ R).f n := by
  simp [chainComplex_pi_f_naturality]

end RelativeChainHelpers

section Devissage

variable (P : SSetPair.{w}) (R : C) (n : ℕ)

/-- The standard relative-chain short complex is split in each degree. -/
private noncomputable def splittingChainComplexShortComplexEval :
    ((P.chainComplexShortComplex R).map (eval C _ n)).Splitting :=
  splittingSigmaConstCokernelShortComplex' _ _ (injective_of_mono _)
    (P.isColimitCokernelCoforkChainComplexX R n)

variable {X : SSet.{w}} (A B : X.Subcomplex)

/-- The canonical morphism from `(B, A ⊓ B)` to `(X, A)`. -/
private def homOfSubcomplexes :
    SSetPair.of (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) ⟶ A.pair :=
  SSetPair.homMk (SSet.Subcomplex.homOfLE (by simp)) B.ι (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise-split short complex comparing `(B, A ⊓ B)`, `(X, A)`,
and `(X, A ⊔ B)`. -/
private noncomputable abbrev shortComplexHomOfSubcomplexes (R : C) :
    ShortComplex (ChainComplex C ℕ) where
  f := SSetPair.chainComplexMap (homOfSubcomplexes A B) R
  X₃ := (SSetPair.of (A ⊔ B).ι).chainComplex R
  g := SSetPair.chainComplexMap
    (SSetPair.homMk (SSet.Subcomplex.homOfLE (by simp)) (𝟙 X) (by simp)) R
  zero := by
    rw [← cancel_epi (SSetPair.chainComplexπ ..), ← Functor.map_comp,
      chainComplex_pi_naturality, comp_zero]
    have h : A ⊓ B ≤ A ⊔ B := inf_left_le_sup_left
    calc
      _ = SSet.chainComplexMap (SSet.Subcomplex.homOfLE (by simp)) R ≫
          SSet.chainComplexMap (SSetPair.of (A ⊔ B).ι).hom R ≫
            (SSetPair.of (A ⊔ B).ι).chainComplexπ R := by
        rw [← Functor.map_comp_assoc]
        rfl
      _ = _ := by
        simp [dsimp% (SSetPair.of (A ⊔ B).ι).chainComplex_condition R]

open Classical in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The explicit degreewise splitting of the relative union comparison. -/
private noncomputable def splittingShortComplexHomOfSubcomplexesEval
    (R : C) (n : ℕ) :
    ((shortComplexHomOfSubcomplexes A B R).map (eval _ _ n)).Splitting := by
  exact
    { r :=
        chainComplexXDesc
          (fun x ↦
            if hx : x ∈ B.obj _ then
              SSet.ιChainComplex _ (by exact ⟨x, hx⟩) ≫
                (SSetPair.chainComplexπ _ _).f n
            else 0) (fun x ↦ by
              split_ifs with hx
              · exact iota_chainComplex_pi_f_eq_zero_of_mem_range
                  (SSetPair.of (SSet.Subcomplex.homOfLE _)) _ _
                  ⟨⟨x.val, ⟨x.prop, hx⟩⟩, rfl⟩
              · simp)
      s :=
        chainComplexXDesc
          (fun x ↦
            if hx : x ∈ B.obj _ then 0 else
              A.pair.right.ιChainComplex x ≫ (A.pair.chainComplexπ R).f n)
          (fun ⟨x, hx⟩ ↦ by
            split_ifs with hx'
            · simp
            · apply iota_chainComplex_pi_f_eq_zero_of_subcomplex
              simp at hx
              tauto)
      f_r :=
        chainComplexX_hom_ext (fun x hx ↦ by
          dsimp
          simp only [chainComplex_pi_f_naturality_assoc,
            SSet.ι_chainComplexMap_f_assoc, iota_chainComplexXDesc]
          erw [Category.comp_id]
          exact dite_eq_left x.prop)
      s_g :=
        chainComplexX_hom_ext (fun x hx ↦ by
          simp only [ShortComplex.map_g, eval_map,
            iota_chainComplexXDesc_assoc]
          erw [Category.comp_id]
          rw [dite_eq_right (fun h ↦ hx ⟨⟨x, Or.inr h⟩, rfl⟩)]
          simp [chainComplex_pi_f_naturality])
      id :=
        chainComplexX_hom_ext (fun x hx ↦ by
          simp only [ShortComplex.map_f, ShortComplex.map_g, eval_map,
            Preadditive.comp_add, iota_chainComplexXDesc_assoc,
            iota_chainComplexMap_f_assoc]
          erw [iota_chainComplexXDesc]
          simp
          split_ifs with hx'
          · simp [chainComplex_pi_f_naturality]
            rfl
          · simp) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma homotopyEquivalences_chainComplexMap_homOfSubcomplexes (R : C) :
    homotopyEquivalences _ _
        (SSetPair.chainComplexMap (homOfSubcomplexes A B) R) ↔
      homotopyEquivalences _ _ (SSet.chainComplexMap (A ⊔ B).ι R) := by
  have : HasZeroObject C := Preadditive.hasZeroObject_of_hasCoproduct C
  have : HasFiniteCoproducts C := hasFiniteCoproducts_of_hasCoproducts C
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts
  rw [dsimp% ChainComplex.homotopyEquivalences_shortComplexF_iff_of_degreewiseSplit
    _ (splittingChainComplexShortComplexEval (SSetPair.of (A ⊔ B).ι) R),
    ChainComplex.homotopyEquivalences_shortComplexF_iff_of_degreewiseSplit
      _ (splittingShortComplexHomOfSubcomplexesEval A B R)]

private lemma mono_left_of_mono_right {P Q : SSetPair.{w}}
    (f : P ⟶ Q) [Mono f.right] : Mono f.left :=
  mono_of_mono_fac f.w

/-- A relative simplicial-chain map is a chain-homotopy equivalence exactly
when the inclusion of the corresponding union subcomplex is one. -/
theorem relativeChainMap_homotopyEquivalence_iff {P Q : SSetPair.{w}}
    (f : P ⟶ Q) (R : C) (Z : Q.right.Subcomplex)
    (hUnion : Z = SSet.Subcomplex.range Q.hom ⊔ SSet.Subcomplex.range f.right)
    (hRight : Mono f.right)
    (hIntersection : SSet.Subcomplex.range (f.left ≫ Q.hom) =
      SSet.Subcomplex.range Q.hom ⊓ SSet.Subcomplex.range f.right) :
    homotopyEquivalences _ _ (SSetPair.chainComplexMap f R) ↔
      homotopyEquivalences _ _ (SSet.chainComplexMap Z.ι R) := by
  subst hUnion
  rw [← homotopyEquivalences_chainComplexMap_homOfSubcomplexes]
  have := mono_left_of_mono_right f
  suffices Arrow.mk f ≅ Arrow.mk
      (homOfSubcomplexes (SSet.Subcomplex.range Q.hom)
        (SSet.Subcomplex.range f.right)) from
    MorphismProperty.arrow_mk_iso_iff _
      (((SSetPair.chainComplexFunctor C).obj R).mapArrow.mapIso this)
  refine Arrow.isoMk
    (pairIsoMk
      (asIso (SSet.Subcomplex.toRange (f.left ≫ Q.hom)) ≪≫
        SSet.Subcomplex.eqToIso hIntersection)
      (asIso (SSet.Subcomplex.toRange f.right) :) ?_)
    (pairIsoMk (asIso (SSet.Subcomplex.toRange Q.hom) :) (Iso.refl _))
  dsimp
  rw [← cancel_mono (SSet.Subcomplex.ι _)]
  simpa using f.w

end Devissage

end Hatcher.Excision
