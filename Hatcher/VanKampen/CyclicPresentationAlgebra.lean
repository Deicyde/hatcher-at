import Hatcher.Circle.FundamentalGroup
import Mathlib.Data.ZMod.QuotientGroup

noncomputable section

namespace Hatcher

namespace Circle

/-- The class of the degree-`n` loop on the circle. -/
def degreeLoopClass (n : ℕ) : FundamentalGroup _root_.Circle 1 :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (loopOfInt (n : ℤ)))

@[simp]
theorem fundamentalGroupEquivInt_degreeLoopClass (n : ℕ) :
    fundamentalGroupEquivInt (degreeLoopClass n) =
      Multiplicative.ofAdd (n : ℤ) := by
  rw [fundamentalGroupEquivInt_apply]
  exact congrArg Multiplicative.ofAdd
    (windingNumberFun_loopOfInt (n : ℤ))

end Circle

private theorem normalClosure_singleton_eq_zpowers
    {G : Type*} [CommGroup G] (g : G) :
    Subgroup.normalClosure ({g} : Set G) = Subgroup.zpowers g := by
  rw [Subgroup.zpowers_eq_closure]
  apply le_antisymm
  · exact Subgroup.normalClosure_le_normal Subgroup.subset_closure
  · exact Subgroup.closure_le_normalClosure

/-- Winding number reduced modulo `n`. -/
private def circleModN (n : ℕ) :
    FundamentalGroup _root_.Circle 1 →* Multiplicative (ZMod n) :=
  (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))).comp
    Circle.fundamentalGroupEquivInt.toMonoidHom

private theorem circleModN_surjective (n : ℕ) :
    Function.Surjective (circleModN n) := by
  intro z
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd z)
  obtain ⟨g, hg⟩ := Circle.fundamentalGroupEquivInt.surjective
    (Multiplicative.ofAdd k)
  refine ⟨g, ?_⟩
  change Multiplicative.ofAdd
    ((Int.castAddHom (ZMod n))
      (Multiplicative.toAdd (Circle.fundamentalGroupEquivInt g))) = z
  rw [hg]
  change Multiplicative.ofAdd ((k : ℤ) : ZMod n) = z
  rw [hk]
  rfl

private theorem circleModN_ker (n : ℕ) :
    (circleModN n).ker =
      Subgroup.normalClosure ({Circle.degreeLoopClass n} : Set _) := by
  letI : CommGroup (FundamentalGroup _root_.Circle 1) :=
    MonoidHom.commGroupOfInjective
      Circle.fundamentalGroupEquivInt.toMonoidHom
      Circle.fundamentalGroupEquivInt.injective
  rw [normalClosure_singleton_eq_zpowers]
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_zpowers_iff]
  change Multiplicative.ofAdd
      ((Circle.windingNumberFun g : ℤ) : ZMod n) = 1 ↔ _
  change ((Circle.windingNumberFun g : ℤ) : ZMod n) = 0 ↔ _
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, Circle.fundamentalGroupEquivInt.injective ?_⟩
    rw [map_zpow, Circle.fundamentalGroupEquivInt_degreeLoopClass]
    rw [← ofAdd_zsmul, Circle.fundamentalGroupEquivInt_apply]
    change Multiplicative.ofAdd (k * (n : ℤ)) =
      Multiplicative.ofAdd (Circle.windingNumberFun g)
    exact congrArg Multiplicative.ofAdd ((Int.mul_comm k n).trans hk.symm)
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h := congrArg Circle.fundamentalGroupEquivInt hk
    rw [map_zpow, Circle.fundamentalGroupEquivInt_degreeLoopClass] at h
    rw [← ofAdd_zsmul, Circle.fundamentalGroupEquivInt_apply] at h
    have h' := congrArg Multiplicative.toAdd h
    exact h'.symm.trans (Int.mul_comm k n)

/-- The quotient of the circle's fundamental group by its degree-`n` loop is
the cyclic group of order `n`. -/
noncomputable def cyclicPresentationQuotientEquiv (n : ℕ) :
    FundamentalGroup _root_.Circle 1 ⧸
        Subgroup.normalClosure ({Circle.degreeLoopClass n} : Set _) ≃*
      Multiplicative (ZMod n) :=
  (QuotientGroup.quotientMulEquivOfEq (circleModN_ker n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (circleModN n)
      (circleModN_surjective n))

@[simp]
theorem cyclicPresentationQuotientEquiv_mk (n : ℕ)
    (g : FundamentalGroup _root_.Circle 1) :
    cyclicPresentationQuotientEquiv n
        (QuotientGroup.mk'
          (Subgroup.normalClosure ({Circle.degreeLoopClass n} : Set _)) g) =
      Multiplicative.ofAdd ((Circle.windingNumberFun g : ℤ) : ZMod n) := by
  rfl

@[simp]
theorem cyclicPresentationQuotientEquiv_degreeLoopClass (n m : ℕ) :
    cyclicPresentationQuotientEquiv n
        (QuotientGroup.mk'
          (Subgroup.normalClosure ({Circle.degreeLoopClass n} : Set _))
          (Circle.degreeLoopClass m)) =
      Multiplicative.ofAdd ((m : ℤ) : ZMod n) := by
  rw [cyclicPresentationQuotientEquiv_mk]
  exact congrArg (fun k : ℤ ↦ Multiplicative.ofAdd (k : ZMod n))
    (Circle.windingNumberFun_loopOfInt (m : ℤ))

end Hatcher
