/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Joël Riou, Jack McCarthy

This file adapts the small-chain homotopy equivalence from `joelriou/excision`
at commit `8b56cd0c8e5f39a7c2f36418c80b298e469596a6` to the Mathlib version pinned
by this project.
-/

import Hatcher.Excision.SmallSimplices
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The small-chain inclusion is a homotopy equivalence

For a cover by interiors, this file chooses the least subdivision depth of
each singular simplex and implements Hatcher's variable-depth correction
`rho = 1 - ∂D - D∂`.  It factors through the small-chain subcomplex and
packages the canonical inclusion as a chain-homotopy equivalence.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial
  Opposite

namespace Hatcher.Excision

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C]

section KernelSupport

variable (R : C) {α β : Type w} (f : α → β)
  (hf : Function.Injective f)

private noncomputable abbrev sigmaConstCokernelShortComplex :
    ShortComplex C :=
  .mk _ _ (sigmaConstCokernelCofork R f).condition

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
          rw [Preadditive.comp_add, Sigma.ι_comp_desc_assoc,
            dite_eq_right hb, Sigma.ι_comp_desc_assoc,
            dite_eq_left (by simpa using hb)]
          simp }

private noncomputable def splittingSigmaConstCokernelShortComplex'
    {c : CokernelCofork
      (Sigma.map' (f := fun (_ : β) ↦ R) (g := fun (_ : α) ↦ R)
        f (fun _ ↦ 𝟙 R))}
    (hc : IsColimit c) :
    (ShortComplex.mk _ _ c.condition).Splitting :=
  (splittingSigmaConstCokernelShortComplex R f hf).ofIso
    ((ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (IsColimit.coconePointUniqueUpToIso
        (isColimitSigmaConstCokernelCofork R f) hc)
      (by cat_disch) (by
        simp [dsimp% (IsColimit.comp_coconePointUniqueUpToIso_hom
          (isColimitSigmaConstCokernelCofork R f) hc) .one])))

variable {S : SSet.{w}} (A : S.Subcomplex)

@[simp] private lemma subcomplexPair_left : A.pair.left = A := rfl
@[simp] private lemma subcomplexPair_right : A.pair.right = S := rfl
@[simp] private lemma subcomplexPair_hom : A.pair.hom = A.ι := rfl

private noncomputable def splittingSubcomplexPairEval (R : C) (n : ℕ) :
    ((A.pair.chainComplexShortComplex R).map (eval C _ n)).Splitting :=
  splittingSigmaConstCokernelShortComplex' R _ (injective_of_mono _)
    (A.pair.isColimitCokernelCoforkChainComplexX R n)

private noncomputable def kernelForkSubcomplexPairX (R : C) (n : ℕ) :
    KernelFork ((A.pair.chainComplexπ R).f n) :=
  KernelFork.ofι _ (A.pair.chainComplex_condition_f R n)

attribute [local instance] Preadditive.hasZeroObject_of_hasCoproduct in
private noncomputable def isLimitKernelForkSubcomplexPairX
    (R : C) (n : ℕ) :
    IsLimit (kernelForkSubcomplexPairX A R n) :=
  (splittingSubcomplexPairEval A R n).fIsKernel

private noncomputable def kernelForkSubcomplexPair (R : C) :
    KernelFork (A.pair.chainComplexπ R) :=
  KernelFork.ofι _ (A.pair.chainComplex_condition R)

attribute [local instance] Preadditive.hasZeroObject_of_hasCoproduct in
private noncomputable def isLimitKernelForkSubcomplexPair (R : C) :
    IsLimit (kernelForkSubcomplexPair A R) :=
  HomologicalComplex.isLimitOfEval _ _
    (fun n ↦ (KernelFork.isLimitMapConeEquiv _ _).2
      (isLimitKernelForkSubcomplexPairX A R n))

private noncomputable instance mono_smallChainInclusion :
    Mono (SSet.chainComplexMap A.ι R) := by
  change Mono (kernelForkSubcomplexPair A R).ι
  exact Fork.IsLimit.mono (isLimitKernelForkSubcomplexPair A R)

@[reassoc (attr := simp)]
private lemma iota_subcomplexPair_pi_eq_zero
    {n : ℕ} (x : A.pair.left _⦋n⦌) :
    dsimp% A.pair.right.ιChainComplex (A.pair.hom.app _ x) ≫
      (A.pair.chainComplexπ R).f n = 0 := by
  simpa only [comp_zero, SSet.ι_chainComplexMap_f_assoc] using!
    SSet.ιChainComplex A.pair.left x ≫=
      A.pair.chainComplex_condition_f R n

@[reassoc]
private lemma iota_subcomplexPair_pi_eq_zero_of_mem
    {n : ℕ} (x : S _⦋n⦌) (hx : x ∈ A.obj _) :
    SSet.ιChainComplex S x ≫ (A.pair.chainComplexπ R).f n = 0 := by
  change dsimp% A.pair.right.ιChainComplex (A.pair.hom.app _ ⟨x, hx⟩) ≫
    (A.pair.chainComplexπ R).f n = 0
  exact iota_subcomplexPair_pi_eq_zero (A := A) R (x := ⟨x, hx⟩)

end KernelSupport

private lemma fin_sum_univ_eq_sum_of_le
    {M : Type*} [AddCommMonoid M] {n : ℕ}
    (f : Fin n → M) (k : ℕ) (hk : k ≤ n) :
    ∑ i, f i = (∑ i : Fin k, f (i.castLE hk)) +
      ∑ i : Fin n with k ≤ i.val, f i := by
  let s : Finset (Fin n) := {i | k ≤ i.val}
  have hs : sᶜ = ({i | i.val < k} : Finset (Fin n)) := by aesop
  rw [← s.sum_compl_add_sum, hs]
  congr 1
  apply Finset.sum_bij' (fun i hi ↦ ⟨i.val, by simpa using hi⟩)
    (fun i hi ↦ i.castLE hk)
  all_goals simp

section SmallChainRetraction

variable {X : TopCat.{w}} {ι : Type*} {U : ι → Set X}

private lemma nonempty_iteratedSubdivisionIsSmall
    (hU : SmallSimplicesCondition U) {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) :
    (Set.ofPred (IteratedSubdivisionIsSmall U s)).Nonempty :=
  exists_iteratedSubdivision_mem_smallSubcomplex hU s

/-- The least subdivision depth making all subsimplices of `s` small. -/
private noncomputable def smallestSubdivisionDepth
    (hU : SmallSimplicesCondition U) {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) : ℕ :=
  Nat.lt_wfRel.wf.min _ (nonempty_iteratedSubdivisionIsSmall hU s)

private lemma iteratedSubdivisionIsSmall_smallestDepth
    (hU : SmallSimplicesCondition U) {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) :
    IteratedSubdivisionIsSmall U s (smallestSubdivisionDepth hU s) :=
  Nat.lt_wfRel.wf.min_mem _ (nonempty_iteratedSubdivisionIsSmall hU s)

private lemma iteratedSubdivisionIsSmall_iff_smallestDepth_le
    (hU : SmallSimplicesCondition U) {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) (k : ℕ) :
    IteratedSubdivisionIsSmall U s k ↔
      smallestSubdivisionDepth hU s ≤ k :=
  ⟨fun h ↦ WellFoundedLT.min_le h,
    fun h ↦ (iteratedSubdivisionIsSmall_smallestDepth hU s).of_le h⟩

private lemma smallestSubdivisionDepth_eq_zero_iff
    (hU : SmallSimplicesCondition U) {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n⦌) :
    smallestSubdivisionDepth hU s = 0 ↔
      s ∈ (smallSubcomplex U).obj _ := by
  rw [← iteratedSubdivisionIsSmall_zero_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ le_antisymm ?_ (by simp)⟩
  · simpa only [← h] using
      iteratedSubdivisionIsSmall_smallestDepth hU s
  · rwa [← iteratedSubdivisionIsSmall_iff_smallestDepth_le]

private lemma smallestSubdivisionDepth_face_le
    (hU : SmallSimplicesCondition U) {n : ℕ}
    (s : TopCat.toSSet.obj X _⦋n + 1⦌) (i : Fin (n + 2)) :
    smallestSubdivisionDepth hU ((TopCat.toSSet.obj X).δ i s) ≤
      smallestSubdivisionDepth hU s := by
  rw [← iteratedSubdivisionIsSmall_iff_smallestDepth_le]
  exact (iteratedSubdivisionIsSmall_smallestDepth hU s).face i

variable (hU : SmallSimplicesCondition U)

/-- Hatcher's variable-depth homotopy operator. -/
private noncomputable def smallRetractionHomotopyAux (R : C) (n : ℕ) :
    (singularChains X R).X n ⟶ (singularChains X R).X (n + 1) :=
  Sigma.desc (fun x ↦
    iotaSingularChain X x ≫
      (singularChainHomotopyIdSubdivisionIter X R
        (smallestSubdivisionDepth hU x)).hom n (n + 1))

@[reassoc]
private lemma iota_smallRetractionHomotopyAux (R : C) {n : ℕ}
    (x : TopCat.toSSet.obj X _⦋n⦌) :
    iotaSingularChain X x ≫ smallRetractionHomotopyAux hU R n =
      iotaSingularChain X x ≫
        (singularChainHomotopyIdSubdivisionIter X R
          (smallestSubdivisionDepth hU x)).hom n (n + 1) :=
  Sigma.ι_comp_desc ..

/-- The degree-indexed form of Hatcher's variable-depth homotopy. -/
private noncomputable def smallRetractionHomotopy (R : C) (n m : ℕ) :
    (singularChains X R).X n ⟶ (singularChains X R).X m :=
  if h : n + 1 = m then
    smallRetractionHomotopyAux hU R n ≫ eqToHom (by simp [h])
  else 0

@[simp]
private lemma smallRetractionHomotopy_eq (R : C) (n : ℕ) :
    smallRetractionHomotopy hU R n (n + 1) =
      smallRetractionHomotopyAux hU R n := by
  simp [smallRetractionHomotopy]

private lemma smallRetractionHomotopy_zero (R : C) (n m : ℕ)
    (h : n + 1 ≠ m) : smallRetractionHomotopy hU R n m = 0 := by
  grind [smallRetractionHomotopy]

/-- The corrected endomorphism `1 - ∂D - D∂`. -/
private noncomputable def smallRetractionEndomorphism (R : C) :
    singularChains X R ⟶ singularChains X R :=
  𝟙 _ - Homotopy.nullHomotopicMap (smallRetractionHomotopy hU R)

private lemma smallRetractionEndomorphism_eq_sub (R : C) :
    smallRetractionEndomorphism hU R =
      𝟙 (singularChains X R) -
        Homotopy.nullHomotopicMap (smallRetractionHomotopy hU R) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def smallRetractionEndomorphismHomotopyId (R : C) :
    Homotopy (smallRetractionEndomorphism hU R)
      (𝟙 (singularChains X R)) :=
  (Homotopy.equivSubZero.symm
    (.trans (.ofEq (by simp [smallRetractionEndomorphism_eq_sub]))
      (.nullHomotopy (smallRetractionHomotopy hU R)
        (smallRetractionHomotopy_zero hU R)))).symm

@[reassoc]
private lemma iota_smallRetractionEndomorphism_f
    (R : C) {n : ℕ} (x : TopCat.toSSet.obj X _⦋n⦌)
    (hx : x ∈ (smallSubcomplex U).obj _) :
    iotaSingularChain X x ≫ (smallRetractionEndomorphism hU R).f n =
      iotaSingularChain X x := by
  dsimp [smallRetractionEndomorphism_eq_sub]
  simp only [Preadditive.comp_sub, Category.comp_id, sub_eq_self]
  replace hx := (smallestSubdivisionDepth_eq_zero_iff hU x).2 hx
  obtain _ | n := n
  · simp [ChainComplex.nullHomotopicMap_f_zero,
      iota_smallRetractionHomotopyAux_assoc, hx,
      singularChainHomotopyIdSubdivisionIter_hom]
  · rw [ChainComplex.nullHomotopicMap_f_succ]
    simp only [smallRetractionHomotopy_eq, Preadditive.comp_add,
      iotaSingularChain_d_assoc, Int.reduceNeg, Preadditive.sum_comp,
      Linear.smul_comp, iota_smallRetractionHomotopyAux_assoc]
    rw [Finset.sum_eq_zero (fun i hi ↦ ?_), hx]
    · simp [singularChainHomotopyIdSubdivisionIter_hom]
    · rw [iota_smallRetractionHomotopyAux,
        singularChainHomotopyIdSubdivisionIter_hom,
        Finset.sum_eq_zero (fun ⟨j, hj⟩ _ ↦ by
          have := smallestSubdivisionDepth_face_le hU x i
          omega), comp_zero, smul_zero]

@[simp]
private lemma smallRetractionEndomorphism_f_zero (R : C) :
    (smallRetractionEndomorphism hU R).f 0 =
      𝟙 ((singularChains X R).X 0) :=
  singularChains_hom_ext (fun x ↦ by
    rw [Category.comp_id, iota_smallRetractionEndomorphism_f]
    simp [hU.smallSubcomplex_obj_zero])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma smallChainInclusion_comp_endomorphism (R : C) :
    SSet.chainComplexMap (smallSubcomplex U).ι R ≫
        smallRetractionEndomorphism hU R =
      SSet.chainComplexMap (smallSubcomplex U).ι R := by
  ext n ⟨x, hx⟩
  simpa using! iota_smallRetractionEndomorphism_f hU R x hx

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private lemma iota_singularChainSubdivisionIter_comp_pi_eq_zero
    (R : C) {n : ℕ} (x : TopCat.toSSet.obj X _⦋n⦌)
    (k : ℕ) (hk : smallestSubdivisionDepth hU x ≤ k) :
    iotaSingularChain X x ≫ (singularChainSubdivisionIter X R k).f n ≫
      ((smallSubcomplex U).pair.chainComplexπ R).f n = 0 := by
  simp only [iota_singularChainSubdivisionIter_eq_sum_assoc,
    Preadditive.sum_comp, Linear.units_smul_comp]
  rw [Finset.sum_eq_zero]
  intro σ _
  erw [iota_subcomplexPair_pi_eq_zero_of_mem
      (A := smallSubcomplex U) R _
      ((iteratedSubdivisionIsSmall_smallestDepth hU x).of_le hk σ)]
  rw [smul_zero]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma singularChainMap_subtypeVal_comp_pi
    (R : C) (i : ι) (n : ℕ) :
    (singularChainMap (TopCat.ofHom (X := U i) (Y := X)
      ⟨Subtype.val, by fun_prop⟩) R).f n ≫
      ((smallSubcomplex U).pair.chainComplexπ R).f n = 0 :=
  singularChains_hom_ext (fun x ↦ by
    simp only [iota_singularChainMap_assoc, comp_zero]
    apply iota_subcomplexPair_pi_eq_zero_of_mem
      (A := smallSubcomplex U) R
    rw [mem_smallSubcomplex_iff_exists_lift]
    exact ⟨i, _, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private lemma iota_singularChainHomotopy_comp_pi_eq_zero
    (R : C) {n : ℕ} (x : TopCat.toSSet.obj X _⦋n⦌)
    (hx : x ∈ (smallSubcomplex U).obj _) :
    iotaSingularChain X x ≫
      (singularChainHomotopyIdSubdivision X R).hom n (n + 1) ≫
        ((smallSubcomplex U).pair.chainComplexπ R).f (n + 1) = 0 := by
  rw [mem_smallSubcomplex_iff_exists_lift] at hx
  obtain ⟨i, f, rfl⟩ := hx
  simp [iota_singularChainHomotopyIdSubdivision_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private lemma iota_singularChainSubdivisionIter_homotopy_comp_pi_eq_zero
    (R : C) {n : ℕ} (x : TopCat.toSSet.obj X _⦋n⦌)
    (k : ℕ) (hk : smallestSubdivisionDepth hU x ≤ k) :
    iotaSingularChain X x ≫ (singularChainSubdivisionIter X R k).f n ≫
      (singularChainHomotopyIdSubdivision X R).hom n (n + 1) ≫
        ((smallSubcomplex U).pair.chainComplexπ R).f (n + 1) = 0 := by
  simp only [iota_singularChainSubdivisionIter_eq_sum_assoc,
    Preadditive.sum_comp, Linear.units_smul_comp]
  rw [Finset.sum_eq_zero]
  intro σ _
  rw [iota_singularChainHomotopy_comp_pi_eq_zero (U := U) R _
      ((iteratedSubdivisionIsSmall_smallestDepth hU x).of_le hk σ),
    smul_zero]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private lemma iota_subdivisionIter_sub_endomorphism
    (R : C) {n : ℕ} (x : TopCat.toSSet.obj X _⦋n + 1⦌) :
    iotaSingularChain X x ≫
        ((singularChainSubdivisionIter X R
          (smallestSubdivisionDepth hU x)).f (n + 1) -
            (smallRetractionEndomorphism hU R).f (n + 1)) =
      ∑ i : Fin (n + 2),
        ∑ j : Fin (smallestSubdivisionDepth hU x) with
            smallestSubdivisionDepth hU ((TopCat.toSSet.obj X).δ i x) ≤ j.val,
          (-1 : ℤ) ^ (i.val + 1) •
            iotaSingularChain X ((TopCat.toSSet.obj X).δ i x) ≫
              (singularChainSubdivisionIter X R j.val).f n ≫
                (singularChainHomotopyIdSubdivision X R).hom _ _ := by
  calc
    _ = iotaSingularChain X x ≫
        (Homotopy.nullHomotopicMap
          (smallRetractionHomotopy hU R -
            (singularChainHomotopyIdSubdivisionIter X R
              (smallestSubdivisionDepth hU x)).hom)).f (n + 1) := by
      simp [smallRetractionEndomorphism_eq_sub,
        (singularChainHomotopyIdSubdivisionIter X R
          (smallestSubdivisionDepth hU x)).eq_sub_nullHomotopicMap]
    _ = iotaSingularChain X x ≫
          (singularChains X R).d (n + 1) n ≫
            (smallRetractionHomotopyAux hU R n -
              (singularChainHomotopyIdSubdivisionIter X R
                (smallestSubdivisionDepth hU x)).hom n (n + 1)) := by
      simp [ChainComplex.nullHomotopicMap_f_succ, smallRetractionHomotopy,
        iota_smallRetractionHomotopyAux_assoc]
    _ = _ := by
      rw [iotaSingularChain_d_assoc, Preadditive.sum_comp]
      congr
      ext i
      rw [Linear.smul_comp, ← Finset.smul_sum, pow_succ,
        ← smul_smul, neg_smul, one_smul]
      congr 1
      generalize hy : (TopCat.toSSet.obj X).δ i x = y
      have hy' : smallestSubdivisionDepth hU y ≤
          smallestSubdivisionDepth hU x := by
        simpa [← hy] using smallestSubdivisionDepth_face_le hU x i
      let t (j : Fin (smallestSubdivisionDepth hU x)) :=
        iotaSingularChain X y ≫
          (singularChainSubdivisionIter X R j.val).f n ≫
            (singularChainHomotopyIdSubdivision X R).hom _ (n + 1)
      calc
        _ = ∑ j : Fin (smallestSubdivisionDepth hU y),
              t (j.castLE hy') -
            ∑ j, t j := by
          rw [Preadditive.comp_sub,
            singularChainHomotopyIdSubdivisionIter_hom,
            Preadditive.comp_sum,
            iota_smallRetractionHomotopyAux,
            singularChainHomotopyIdSubdivisionIter_hom,
            Preadditive.comp_sum]
          dsimp [t]
        _ = - ∑ j : Fin (smallestSubdivisionDepth hU x) with
            smallestSubdivisionDepth hU y ≤ j.val, t j := by
          rw [fin_sum_univ_eq_sum_of_le _ _ hy']
          abel

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private lemma iota_endomorphism_comp_pi
    (R : C) {n : ℕ} (x : TopCat.toSSet.obj X _⦋n⦌) :
    iotaSingularChain X x ≫ (smallRetractionEndomorphism hU R).f n ≫
        ((smallSubcomplex U).pair.chainComplexπ R).f n =
      iotaSingularChain X x ≫
        (singularChainSubdivisionIter X R
          (smallestSubdivisionDepth hU x)).f n ≫
          ((smallSubcomplex U).pair.chainComplexπ R).f n := by
  obtain _ | n := n
  · simp
  · symm
    rw [← sub_eq_zero, ← Preadditive.comp_sub, ← Preadditive.sub_comp,
      iota_subdivisionIter_sub_endomorphism_assoc]
    simp only [Preadditive.sum_comp]
    refine Finset.sum_eq_zero (fun i _ ↦
      Finset.sum_eq_zero (fun ⟨j, hj⟩ hj' ↦ ?_))
    rw [Linear.smul_comp, Category.assoc, Category.assoc,
      iota_singularChainSubdivisionIter_homotopy_comp_pi_eq_zero
        (hU := hU) (R := R),
      smul_zero]
    simpa using hj'

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma smallRetractionEndomorphism_f_comp_pi
    (R : C) (n : ℕ) :
    (smallRetractionEndomorphism hU R).f n ≫
      ((smallSubcomplex U).pair.chainComplexπ R).f n = 0 := by
  refine singularChains_hom_ext (fun x ↦ ?_)
  rw [iota_endomorphism_comp_pi, comp_zero,
    iota_singularChainSubdivisionIter_comp_pi_eq_zero hU R _ _ (by simp)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma smallRetractionEndomorphism_comp_pi (R : C) :
    smallRetractionEndomorphism hU R ≫
      (smallSubcomplex U).pair.chainComplexπ R = 0 := by
  cat_disch

/-- Hatcher's corrected endomorphism, factored through the small-chain
subcomplex. -/
private noncomputable def smallChainRetraction (R : C) :
    singularChains X R ⟶ (smallSubcomplex U).toSSet.chainComplex R :=
  (KernelFork.IsLimit.lift'
    (isLimitKernelForkSubcomplexPair (smallSubcomplex U) R) _
      (smallRetractionEndomorphism_comp_pi hU R)).1

@[reassoc (attr := simp)]
private lemma smallChainRetraction_comp_inclusion (R : C) :
    smallChainRetraction hU R ≫
        SSet.chainComplexMap (smallSubcomplex U).ι R =
      smallRetractionEndomorphism hU R :=
  (KernelFork.IsLimit.lift'
    (isLimitKernelForkSubcomplexPair (smallSubcomplex U) R) _
      (smallRetractionEndomorphism_comp_pi hU R)).2

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma inclusion_comp_smallChainRetraction (R : C) :
    SSet.chainComplexMap (smallSubcomplex U).ι R ≫
      smallChainRetraction hU R = 𝟙 _ := by
  simp [← cancel_mono
    (SSet.chainComplexMap (smallSubcomplex U).ι R)]

/-- For an interior cover, the canonical inclusion of small singular chains
is a chain-homotopy equivalence. -/
@[simps]
noncomputable def smallChainInclusionHomotopyEquiv
    (hU : SmallSimplicesCondition U) (R : C) :
    HomotopyEquiv ((smallSubcomplex U).toSSet.chainComplex R)
      (singularChains X R) where
  hom := SSet.chainComplexMap (smallSubcomplex U).ι R
  inv := smallChainRetraction hU R
  homotopyHomInvId :=
    .ofEq (inclusion_comp_smallChainRetraction hU R)
  homotopyInvHomId :=
    .trans (.ofEq (smallChainRetraction_comp_inclusion hU R))
      (smallRetractionEndomorphismHomotopyId hU R)

/-- The canonical small-chain inclusion satisfies Mathlib's predicate for
chain-homotopy equivalences. -/
lemma smallChainInclusion_homotopyEquivalences
    (hU : SmallSimplicesCondition U) (R : C) :
    HomologicalComplex.homotopyEquivalences _ _
      (SSet.chainComplexMap (smallSubcomplex U).ι R) :=
  ⟨smallChainInclusionHomotopyEquiv hU R, rfl⟩

end SmallChainRetraction

end Hatcher.Excision
