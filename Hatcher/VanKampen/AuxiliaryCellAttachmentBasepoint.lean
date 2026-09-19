import Hatcher.VanKampen.AuxiliaryCellAttachmentDeformation
import Hatcher.VanKampen.WedgeFundamentalGroup

/-!
# Basepoint transport for Hatcher's auxiliary cell attachment

The common basepoint of the binary cover lies at the top of the auxiliary
spine. This file records Hatcher's path from that point to the copy of the
original basepoint and identifies the resulting change of basepoint with the
map induced by the base-side retraction.
-/

noncomputable section

open CategoryTheory FundamentalGroupoid Set Topology
open scoped unitInterval ContinuousMap

namespace Hatcher.VanKampen.AuxiliaryCellAttachment

universe u

variable {X J : Type u} {S : J → Type u}
variable [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
variable (f : ∀ j, S j → X) (s₀ : ∀ j, S j) (x₀ : X)
variable (γ : ∀ j, Path x₀ (f j (s₀ j)))

private theorem map_conj_eq_of_trans_eq_refl
    {C : Type*} {D : Type*} [CategoryTheory.Groupoid C]
    [CategoryTheory.Groupoid D] (F : C ⥤ D) {a b : C} {x : D}
    (e : a ≅ b) (ea : F.obj a ≅ x) (eb : F.obj b ≅ x)
    (h : ea.symm ≪≫ F.mapIso e ≪≫ eb = CategoryTheory.Iso.refl x)
    (g : CategoryTheory.End a) :
    eb.conj (F.map (e.conj g)) = ea.conj (F.map g) := by
  rw [F.map_conj]
  rw [← (F.mapIso e).trans_conj eb]
  have he : F.mapIso e ≪≫ eb = ea := by
    calc
      F.mapIso e ≪≫ eb = ea ≪≫ (ea.symm ≪≫ F.mapIso e ≪≫ eb) := by simp
      _ = ea := by rw [h]; simp
  rw [he]

private theorem mapOfEq_fundamentalGroupMulEquivOfPath_eq
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (F : C(A, B)) {a b : A} {y : B} (p : Path a b)
    (ha : F a = y) (hb : F b = y)
    (hp : ((Path.Homotopic.Quotient.mk p).map F).cast ha.symm hb.symm =
      Path.Homotopic.Quotient.refl y)
    (g : FundamentalGroup A a) :
    FundamentalGroup.mapOfEq F hb
        (FundamentalGroup.fundamentalGroupMulEquivOfPath p g) =
      FundamentalGroup.mapOfEq F ha g := by
  let e := (CategoryTheory.Groupoid.isoEquivHom
    (FundamentalGroupoid.mk a) (FundamentalGroupoid.mk b)).symm
      (Path.Homotopic.Quotient.mk p)
  let ea : (FundamentalGroupoid.map F).obj (FundamentalGroupoid.mk a) ≅
      FundamentalGroupoid.mk y :=
    CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk ha)
  let eb : (FundamentalGroupoid.map F).obj (FundamentalGroupoid.mk b) ≅
      FundamentalGroupoid.mk y :=
    CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk hb)
  have he : ea.symm ≪≫ (FundamentalGroupoid.map F).mapIso e ≪≫ eb =
      CategoryTheory.Iso.refl (FundamentalGroupoid.mk y) := by
    apply CategoryTheory.Iso.ext
    change
      CategoryTheory.eqToHom congr(FundamentalGroupoid.mk $ha.symm) ≫
          (Path.Homotopic.Quotient.mk p).map F ≫
          CategoryTheory.eqToHom congr(FundamentalGroupoid.mk $hb) =
        Path.Homotopic.Quotient.refl y
    rw [FundamentalGroupoid.conj_eqToHom]
    exact hp
  change eb.conj ((FundamentalGroupoid.map F).map (e.conj g)) =
    ea.conj ((FundamentalGroupoid.map F).map g)
  exact map_conj_eq_of_trans_eq_refl (FundamentalGroupoid.map F)
    e ea eb he g

/-- The chosen overlap basepoint as a point of the base-side cover. -/
def baseCoverBasepoint : baseCover f s₀ x₀ γ :=
  ⟨overlapBasepoint f s₀ x₀ γ,
    overlapBasepoint_mem_baseCover f s₀ x₀ γ⟩

private def basepointPathForward :
    Path (baseToBaseCover f s₀ x₀ γ x₀)
      (baseCoverBasepoint f s₀ x₀ γ) where
  toFun t := ⟨spine f s₀ x₀ γ t, spine_mem_baseCover f s₀ x₀ γ t⟩
  continuous_toFun := (spine f s₀ x₀ γ).continuous.subtype_mk _
  source' := by
    apply Subtype.ext
    exact spine_zero f s₀ x₀ γ
  target' := rfl

/-- Hatcher's path in the base-side member, from the common overlap basepoint
to the original basepoint. -/
def basepointPath :
    Path (baseCoverBasepoint f s₀ x₀ γ)
      (baseToBaseCover f s₀ x₀ γ x₀) :=
  (basepointPathForward f s₀ x₀ γ).symm

@[simp] theorem basepointPath_source :
    basepointPath f s₀ x₀ γ 0 = baseCoverBasepoint f s₀ x₀ γ :=
  (basepointPath f s₀ x₀ γ).source

@[simp] theorem basepointPath_target :
    basepointPath f s₀ x₀ γ 1 = baseToBaseCover f s₀ x₀ γ x₀ :=
  (basepointPath f s₀ x₀ γ).target

/-- The retraction supplied by the base-side strong deformation retract. -/
def baseCoverRetraction (hf : ∀ j, Continuous (f j)) :
    C(baseCover f s₀ x₀ γ, X) :=
  (baseCoverStrongDeformationRetract f s₀ x₀ γ hf).retract

@[simp] theorem baseCoverRetraction_base
    (hf : ∀ j, Continuous (f j)) (x : X) :
    baseCoverRetraction f s₀ x₀ γ hf (baseToBaseCover f s₀ x₀ γ x) = x := by
  have h := congrArg (fun g : C(X, X) ↦ g x)
    (baseCoverStrongDeformationRetract f s₀ x₀ γ hf).retract_inclusion
  exact h

@[simp] theorem baseCoverRetraction_spine
    (hf : ∀ j, Continuous (f j)) (t : I) :
    baseCoverRetraction f s₀ x₀ γ hf
      ⟨spine f s₀ x₀ γ t, spine_mem_baseCover f s₀ x₀ γ t⟩ = x₀ := by
  exact baseCoverStrongDeformationRetract_retract_spine f s₀ x₀ γ hf t

@[simp] theorem baseCoverRetraction_overlapBasepoint
    (hf : ∀ j, Continuous (f j)) :
    baseCoverRetraction f s₀ x₀ γ hf (baseCoverBasepoint f s₀ x₀ γ) = x₀ := by
  exact baseCoverStrongDeformationRetract_retract_overlapBasepoint f s₀ x₀ γ hf

@[simp] theorem baseCoverRetraction_basepointPath_apply
    (hf : ∀ j, Continuous (f j)) (t : I) :
    baseCoverRetraction f s₀ x₀ γ hf (basepointPath f s₀ x₀ γ t) = x₀ := by
  simp [basepointPath, basepointPathForward, baseCoverRetraction]

/-- The image of Hatcher's basepoint path under the retraction, with both
endpoints identified with the original basepoint. -/
def retractedBasepointPath (hf : ∀ j, Continuous (f j)) : Path x₀ x₀ :=
  ((basepointPath f s₀ x₀ γ).map
      (baseCoverRetraction f s₀ x₀ γ hf).continuous).cast
    (baseCoverRetraction_overlapBasepoint f s₀ x₀ γ hf).symm
    (baseCoverRetraction_base f s₀ x₀ γ hf x₀).symm

@[simp] theorem retractedBasepointPath_apply
    (hf : ∀ j, Continuous (f j)) (t : I) :
    retractedBasepointPath f s₀ x₀ γ hf t = x₀ := by
  simp [retractedBasepointPath]

@[simp] theorem retractedBasepointPath_eq_refl
    (hf : ∀ j, Continuous (f j)) :
    retractedBasepointPath f s₀ x₀ γ hf = Path.refl x₀ := by
  ext t
  simp

/-- The lower retraction sends Hatcher's basepoint path to the identity path
class at the original basepoint. -/
theorem basepointPath_class_map_retraction
    (hf : ∀ j, Continuous (f j)) :
    ((Path.Homotopic.Quotient.mk (basepointPath f s₀ x₀ γ)).map
        (baseCoverRetraction f s₀ x₀ γ hf)).cast
      (baseCoverRetraction_overlapBasepoint f s₀ x₀ γ hf).symm
      (baseCoverRetraction_base f s₀ x₀ γ hf x₀).symm =
        Path.Homotopic.Quotient.refl x₀ := by
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  change Path.Homotopic.Quotient.mk
    (retractedBasepointPath f s₀ x₀ γ hf) = _
  rw [retractedBasepointPath_eq_refl]
  rfl

@[simp] theorem retractedBasepointPath_class
    (hf : ∀ j, Continuous (f j)) :
    FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (retractedBasepointPath f s₀ x₀ γ hf)) =
      (1 : FundamentalGroup X x₀) := by
  rw [retractedBasepointPath_eq_refl]
  exact Path.Homotopic.Quotient.mk_refl x₀

/-- Basepoint change along the retracted path. -/
def retractedBasepointChange (hf : ∀ j, Continuous (f j)) :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₀ :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath
    (retractedBasepointPath f s₀ x₀ γ hf)

@[simp] theorem retractedBasepointChange_apply
    (hf : ∀ j, Continuous (f j)) (g : FundamentalGroup X x₀) :
    retractedBasepointChange f s₀ x₀ γ hf g = g := by
  rw [retractedBasepointChange, retractedBasepointPath_eq_refl]
  change (CategoryTheory.Iso.refl _).conj g = g
  rw [CategoryTheory.Iso.refl_conj]

private theorem baseCoverRetraction_map_base
    (hf : ∀ j, Continuous (f j)) (g : FundamentalGroup X x₀) :
    FundamentalGroup.mapOfEq (baseCoverRetraction f s₀ x₀ γ hf)
        (baseCoverRetraction_base f s₀ x₀ γ hf x₀)
        (FundamentalGroup.map (baseToBaseCover f s₀ x₀ γ) x₀ g) = g := by
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
      rw [FundamentalGroup.mapOfEq_apply]
      apply congrArg FundamentalGroup.fromPath
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      exact baseCoverRetraction_base f s₀ x₀ γ hf (p t)

/-- Change basepoint along Hatcher's explicit path from the common cover
basepoint to the copy of the original basepoint. -/
def basepointChange :
    FundamentalGroup (baseCover f s₀ x₀ γ) (baseCoverBasepoint f s₀ x₀ γ) ≃*
      FundamentalGroup (baseCover f s₀ x₀ γ) (baseToBaseCover f s₀ x₀ γ x₀) :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath (basepointPath f s₀ x₀ γ)

@[simp] theorem basepointChange_apply
    (g : FundamentalGroup (baseCover f s₀ x₀ γ) (baseCoverBasepoint f s₀ x₀ γ)) :
    basepointChange f s₀ x₀ γ g =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (basepointPath f s₀ x₀ γ) g :=
  rfl

/-- The retraction map at the overlap basepoint is the endpoint retraction map
preceded by change of basepoint along Hatcher's path. -/
theorem baseCoverRetraction_mapOfEq_eq
    (hf : ∀ j, Continuous (f j)) :
    FundamentalGroup.mapOfEq (baseCoverRetraction f s₀ x₀ γ hf)
        (baseCoverRetraction_overlapBasepoint f s₀ x₀ γ hf) =
      (FundamentalGroup.mapOfEq (baseCoverRetraction f s₀ x₀ γ hf)
        (baseCoverRetraction_base f s₀ x₀ γ hf x₀)).comp
        (basepointChange f s₀ x₀ γ).toMonoidHom := by
  ext g
  exact (mapOfEq_fundamentalGroupMulEquivOfPath_eq
    (baseCoverRetraction f s₀ x₀ γ hf)
    (basepointPath f s₀ x₀ γ)
    (baseCoverRetraction_overlapBasepoint f s₀ x₀ γ hf)
    (baseCoverRetraction_base f s₀ x₀ γ hf x₀)
    (basepointPath_class_map_retraction f s₀ x₀ γ hf) g).symm

/-- The binary-cover fundamental group, transported back to the original
basepoint by the base-side retraction. -/
def baseCoverFundamentalGroupEquiv (hf : ∀ j, Continuous (f j)) :
    FundamentalGroup (baseCover f s₀ x₀ γ) (baseCoverBasepoint f s₀ x₀ γ) ≃*
      FundamentalGroup X x₀ :=
  Hatcher.fundamentalGroupMulEquivOfHomotopyEquivOfEq
    (baseCoverStrongDeformationRetract f s₀ x₀ γ hf).toHomotopyEquiv
    (baseCoverBasepoint f s₀ x₀ γ) x₀
    (baseCoverRetraction_overlapBasepoint f s₀ x₀ γ hf)

@[simp] theorem baseCoverFundamentalGroupEquiv_apply
    (hf : ∀ j, Continuous (f j))
    (g : FundamentalGroup (baseCover f s₀ x₀ γ) (baseCoverBasepoint f s₀ x₀ γ)) :
    baseCoverFundamentalGroupEquiv f s₀ x₀ γ hf g =
      FundamentalGroup.mapOfEq (baseCoverRetraction f s₀ x₀ γ hf)
        (baseCoverRetraction_overlapBasepoint f s₀ x₀ γ hf) g := by
  exact Hatcher.fundamentalGroupMulEquivOfHomotopyEquivOfEq_apply
    (baseCoverStrongDeformationRetract f s₀ x₀ γ hf).toHomotopyEquiv
    (baseCoverBasepoint f s₀ x₀ γ) x₀
    (baseCoverRetraction_overlapBasepoint f s₀ x₀ γ hf) g

theorem baseCoverFundamentalGroupEquiv_toMonoidHom
    (hf : ∀ j, Continuous (f j)) :
    (baseCoverFundamentalGroupEquiv f s₀ x₀ γ hf).toMonoidHom =
      (FundamentalGroup.mapOfEq (baseCoverRetraction f s₀ x₀ γ hf)
        (baseCoverRetraction_base f s₀ x₀ γ hf x₀)).comp
        (basepointChange f s₀ x₀ γ).toMonoidHom := by
  ext g
  change baseCoverFundamentalGroupEquiv f s₀ x₀ γ hf g = _
  rw [baseCoverFundamentalGroupEquiv_apply]
  exact DFunLike.congr_fun (baseCoverRetraction_mapOfEq_eq f s₀ x₀ γ hf) g

@[simp] theorem baseCoverFundamentalGroupEquiv_symm_apply
    (hf : ∀ j, Continuous (f j)) (g : FundamentalGroup X x₀) :
    (baseCoverFundamentalGroupEquiv f s₀ x₀ γ hf).symm g =
      (basepointChange f s₀ x₀ γ).symm
        (FundamentalGroup.map (baseToBaseCover f s₀ x₀ γ) x₀ g) := by
  apply (baseCoverFundamentalGroupEquiv f s₀ x₀ γ hf).injective
  rw [MulEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun
    (baseCoverFundamentalGroupEquiv_toMonoidHom f s₀ x₀ γ hf)
    ((basepointChange f s₀ x₀ γ).symm
      (FundamentalGroup.map (baseToBaseCover f s₀ x₀ γ) x₀ g))
  change baseCoverFundamentalGroupEquiv f s₀ x₀ γ hf
      ((basepointChange f s₀ x₀ γ).symm
        (FundamentalGroup.map (baseToBaseCover f s₀ x₀ γ) x₀ g)) =
    FundamentalGroup.mapOfEq (baseCoverRetraction f s₀ x₀ γ hf)
      (baseCoverRetraction_base f s₀ x₀ γ hf x₀)
      (basepointChange f s₀ x₀ γ
        ((basepointChange f s₀ x₀ γ).symm
          (FundamentalGroup.map (baseToBaseCover f s₀ x₀ γ) x₀ g))) at h
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  exact (baseCoverRetraction_map_base f s₀ x₀ γ hf g).symm

/-- The inverse presentation, from the original fundamental group to the
binary-cover basepoint. -/
def originalToBaseCoverFundamentalGroupEquiv
    (hf : ∀ j, Continuous (f j)) :
    FundamentalGroup X x₀ ≃*
      FundamentalGroup (baseCover f s₀ x₀ γ) (baseCoverBasepoint f s₀ x₀ γ) :=
  (baseCoverFundamentalGroupEquiv f s₀ x₀ γ hf).symm

@[simp] theorem originalToBaseCoverFundamentalGroupEquiv_apply
    (hf : ∀ j, Continuous (f j)) (g : FundamentalGroup X x₀) :
    originalToBaseCoverFundamentalGroupEquiv f s₀ x₀ γ hf g =
      (basepointChange f s₀ x₀ γ).symm
        (FundamentalGroup.map (baseToBaseCover f s₀ x₀ γ) x₀ g) := by
  exact baseCoverFundamentalGroupEquiv_symm_apply f s₀ x₀ γ hf g

end Hatcher.VanKampen.AuxiliaryCellAttachment
