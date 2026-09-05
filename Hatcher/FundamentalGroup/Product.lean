import Hatcher.Circle.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product

open CategoryTheory
open scoped FundamentalGroupoid

universe u v

namespace Hatcher

variable (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]

/-- Projection onto the two factors identifies the fundamental group of a
product with the product of the fundamental groups. -/
noncomputable def fundamentalGroupProdEquiv (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃*
      FundamentalGroup X x × FundamentalGroup Y y where
  toEquiv :=
    { toFun := fun p =>
        (Path.Homotopic.projLeft p, Path.Homotopic.projRight p)
      invFun := fun p => Path.Homotopic.prod p.1 p.2
      left_inv := Path.Homotopic.prod_projLeft_projRight
      right_inv := fun p => by
        ext
        · exact Path.Homotopic.projLeft_prod p.1 p.2
        · exact Path.Homotopic.projRight_prod p.1 p.2 }
  __ := ((FundamentalGroupoidFunctor.prodIso
    (TopCat.of X) (TopCat.of Y)).inv).mapEnd
      (FundamentalGroupoid.mk (x, y))

@[simp]
theorem fundamentalGroupProdEquiv_apply (x : X) (y : Y)
    (p : FundamentalGroup (X × Y) (x, y)) :
    fundamentalGroupProdEquiv X Y x y p =
      (Path.Homotopic.projLeft p, Path.Homotopic.projRight p) :=
  rfl

@[simp]
theorem fundamentalGroupProdEquiv_symm_apply (x : X) (y : Y)
    (p : FundamentalGroup X x × FundamentalGroup Y y) :
    (fundamentalGroupProdEquiv X Y x y).symm p =
      Path.Homotopic.prod p.1 p.2 :=
  rfl

@[simp]
theorem fundamentalGroupProdEquiv_prod (x : X) (y : Y)
    (p : FundamentalGroup X x) (q : FundamentalGroup Y y) :
    fundamentalGroupProdEquiv X Y x y (Path.Homotopic.prod p q) =
      (p, q) := by
  apply Prod.ext <;> simp [fundamentalGroupProdEquiv]

/-- The fundamental group of the torus is `ℤ × ℤ`. -/
noncomputable def torusFundamentalGroupEquiv :
    FundamentalGroup (_root_.Circle × _root_.Circle) (1, 1) ≃*
      Multiplicative ℤ × Multiplicative ℤ :=
  (fundamentalGroupProdEquiv _root_.Circle _root_.Circle 1 1).trans
    (Circle.fundamentalGroupEquivInt.prodCongr
      Circle.fundamentalGroupEquivInt)

@[simp]
theorem torusFundamentalGroupEquiv_prod_loopOfInt (m n : ℤ) :
    torusFundamentalGroupEquiv
        (Path.Homotopic.prod
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (Circle.loopOfInt m)))
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (Circle.loopOfInt n)))) =
      (Multiplicative.ofAdd m, Multiplicative.ofAdd n) := by
  change
    (Circle.fundamentalGroupEquivInt
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (Circle.loopOfInt m))),
      Circle.fundamentalGroupEquivInt
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (Circle.loopOfInt n)))) = _
  rw [Circle.fundamentalGroupEquivInt_apply,
    Circle.fundamentalGroupEquivInt_apply,
    Circle.windingNumberFun_loopOfInt,
    Circle.windingNumberFun_loopOfInt]

/-- Under the torus isomorphism, `(m, n)` corresponds to Hatcher's loop
`ωₘₙ(s) = (ωₘ(s), ωₙ(s))`. -/
theorem torusFundamentalGroupEquiv_symm_apply (m n : ℤ) :
    torusFundamentalGroupEquiv.symm
        (Multiplicative.ofAdd m, Multiplicative.ofAdd n) =
      Path.Homotopic.prod
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (Circle.loopOfInt m)))
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (Circle.loopOfInt n))) := by
  apply torusFundamentalGroupEquiv.injective
  rw [torusFundamentalGroupEquiv.apply_symm_apply,
    torusFundamentalGroupEquiv_prod_loopOfInt]

end Hatcher
