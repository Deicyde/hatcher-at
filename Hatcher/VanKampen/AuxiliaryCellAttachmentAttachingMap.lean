import Hatcher.VanKampen.AuxiliaryCellAttachmentOverlapPiece
import Hatcher.VanKampen.DiskBoundaryCircle

/-!
# The meridians in the auxiliary overlap

For a family of attached two-cells, the canonical meridian in each indexed
piece of the auxiliary overlap maps, under the base-side retraction, to the
corresponding attaching loop transported along the chosen basepoint path.
-/

noncomputable section

open CategoryTheory FundamentalGroupoid
open scoped ContinuousMap TopCat

namespace Hatcher.VanKampen.AuxiliaryCellAttachment

universe u

variable {X J : Type u} {S : J → Type u}
variable [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]

/-- The based fundamental-group equivalence induced by the canonical
homotopy equivalence from an overlap piece to its attaching space. -/
noncomputable def intersectionPieceFundamentalGroupEquiv
    (f : ∀ j, S j → X) (s₀ : ∀ j, S j) (x₀ : X)
    (γ : ∀ j, Path x₀ (f j (s₀ j))) (j : J) :
    FundamentalGroup (↑(intersectionPiece f s₀ x₀ γ j))
        (intersectionPieceBasepoint f s₀ x₀ γ j) ≃*
      FundamentalGroup (S j) (s₀ j) :=
  Hatcher.fundamentalGroupMulEquivOfHomotopyEquivOfEq
    (intersectionPieceHomotopyEquivBoundary f s₀ x₀ γ j)
    (intersectionPieceBasepoint f s₀ x₀ γ j) (s₀ j)
    (intersectionPieceHomotopyEquivBoundary_basepoint f s₀ x₀ γ j)

private theorem fundamentalGroupMapOfEq_eq_basepointChange_comp
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {F G : C(A, B)} (H : F.Homotopy G) (a : A) {b c : B}
    (hF : F a = b) (hG : G a = c) :
    FundamentalGroup.mapOfEq F hF =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath
        ((H.evalAt a).cast hF.symm hG.symm)).symm.toMonoidHom.comp
        (FundamentalGroup.mapOfEq G hG) := by
  subst b
  subst c
  apply MonoidHom.ext
  intro g
  have h := DFunLike.congr_fun
    (Hatcher.fundamentalGroupMap_eq_basepointChange_comp H a) g
  change (CategoryTheory.Iso.refl _).conj
      (FundamentalGroup.map F a g) =
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (H.evalAt a)).symm
      ((CategoryTheory.Iso.refl _).conj
        (FundamentalGroup.map G a g))
  rw [CategoryTheory.Iso.refl_conj, CategoryTheory.Iso.refl_conj]
  exact h

/-- On fundamental groups, the map from an overlap piece to the original base
is the attaching map preceded by the canonical piece equivalence and followed
by transport back along the chosen path `γ j`. -/
theorem intersectionPieceToBase_fundamentalGroup
    (f : ∀ j, S j → X) (s₀ : ∀ j, S j) (x₀ : X)
    (γ : ∀ j, Path x₀ (f j (s₀ j)))
    (hf : ∀ j, Continuous (f j)) (j : J) :
    FundamentalGroup.mapOfEq
        (intersectionPieceToBase f s₀ x₀ γ hf j)
        (intersectionPieceToBase_basepoint f s₀ x₀ γ hf j) =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath
          (γ j)).symm.toMonoidHom.comp
        ((FundamentalGroup.map (⟨f j, hf j⟩ : C(S j, X)) (s₀ j)).comp
          (intersectionPieceFundamentalGroupEquiv f s₀ x₀ γ j).toMonoidHom) := by
  let e := intersectionPieceHomotopyEquivBoundary f s₀ x₀ γ j
  let z := intersectionPieceBasepoint f s₀ x₀ γ j
  let F := intersectionPieceToBase f s₀ x₀ γ hf j
  let G := (⟨f j, hf j⟩ : C(S j, X)).comp e.toFun
  let H := intersectionPieceAttachingHomotopy f s₀ x₀ γ hf j
  let hF : F z = x₀ := intersectionPieceToBase_basepoint f s₀ x₀ γ hf j
  let hE : e z = s₀ j :=
    intersectionPieceHomotopyEquivBoundary_basepoint f s₀ x₀ γ j
  let hG : G z = f j (s₀ j) := congrArg (f j) hE
  have hmap := fundamentalGroupMapOfEq_eq_basepointChange_comp
    H z hF hG
  have htrace :
      Path.Homotopic.Quotient.mk
          ((H.evalAt z).cast hF.symm hG.symm) =
        Path.Homotopic.Quotient.mk (γ j) :=
    Path.Homotopic.Quotient.eq.mpr
      (intersectionPieceAttachingTrace_homotopic f s₀ x₀ γ hf j)
  have hchange :
      FundamentalGroup.fundamentalGroupMulEquivOfPath
          ((H.evalAt z).cast hF.symm hG.symm) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath (γ j) := by
    unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
    exact congrArg
      (fun q : Path.Homotopic.Quotient x₀ (f j (s₀ j)) ↦
        ((CategoryTheory.Groupoid.isoEquivHom
          (FundamentalGroupoid.mk x₀)
          (FundamentalGroupoid.mk (f j (s₀ j)))).symm q).conj)
      htrace
  have hcomp :
      FundamentalGroup.mapOfEq G hG =
        (FundamentalGroup.map (⟨f j, hf j⟩ : C(S j, X)) (s₀ j)).comp
          (intersectionPieceFundamentalGroupEquiv
            f s₀ x₀ γ j).toMonoidHom := by
    apply MonoidHom.ext
    intro g
    induction g using Path.Homotopic.Quotient.ind with
    | mk p =>
        change FundamentalGroup.mapOfEq G hG
            (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
          FundamentalGroup.map (⟨f j, hf j⟩ : C(S j, X)) (s₀ j)
            (Hatcher.fundamentalGroupMulEquivOfHomotopyEquivOfEq
              e z (s₀ j) hE
              (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)))
        rw [Hatcher.fundamentalGroupMulEquivOfHomotopyEquivOfEq_apply]
        rw [FundamentalGroup.mapOfEq_apply]
        rw [FundamentalGroup.mapOfEq_apply]
        rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
        rfl
  change FundamentalGroup.mapOfEq F hF = _
  calc
    FundamentalGroup.mapOfEq F hF =
        (FundamentalGroup.fundamentalGroupMulEquivOfPath
          ((H.evalAt z).cast hF.symm hG.symm)).symm.toMonoidHom.comp
          (FundamentalGroup.mapOfEq G hG) := hmap
    _ = (FundamentalGroup.fundamentalGroupMulEquivOfPath
          (γ j)).symm.toMonoidHom.comp
        ((FundamentalGroup.map (⟨f j, hf j⟩ : C(S j, X)) (s₀ j)).comp
          (intersectionPieceFundamentalGroupEquiv
            f s₀ x₀ γ j).toMonoidHom) := by
      rw [hchange, hcomp]

/-- Applying the base-cover fundamental-group equivalence after including a
piece is the same as applying the piece-to-base map directly. -/
theorem baseCoverFundamentalGroupEquiv_map_intersectionPiece
    (f : ∀ j, S j → X) (s₀ : ∀ j, S j) (x₀ : X)
    (γ : ∀ j, Path x₀ (f j (s₀ j)))
    (hf : ∀ j, Continuous (f j)) (j : J)
    (g : FundamentalGroup (↑(intersectionPiece f s₀ x₀ γ j))
      (intersectionPieceBasepoint f s₀ x₀ γ j)) :
    baseCoverFundamentalGroupEquiv f s₀ x₀ γ hf
        (FundamentalGroup.mapOfEq
          (intersectionPieceToBaseCover f s₀ x₀ γ j)
          (intersectionPieceToBaseCover_basepoint f s₀ x₀ γ j) g) =
      FundamentalGroup.mapOfEq
        (intersectionPieceToBase f s₀ x₀ γ hf j)
        (intersectionPieceToBase_basepoint f s₀ x₀ γ hf j) g := by
  rw [baseCoverFundamentalGroupEquiv_apply]
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [FundamentalGroup.mapOfEq_apply]
      rw [FundamentalGroup.mapOfEq_apply]
      rw [FundamentalGroup.mapOfEq_apply]
      rfl

section TwoCells

abbrev BoundaryTwo : Type u :=
  ((TopCat.diskBoundary.{u} 2 : TopCat.{u}) : Type u)

/-- The positively oriented standard generator of the two-disk boundary. -/
noncomputable def diskBoundaryTwoGenerator :
    FundamentalGroup BoundaryTwo Hatcher.diskBoundaryTwoBasepoint.{u} :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk Hatcher.diskBoundaryTwoLoop.{u})

/-- The standard boundary generator corresponds to `1 ∈ ℤ`. -/
noncomputable def diskBoundaryTwoFundamentalGroupEquivInt :
    FundamentalGroup BoundaryTwo Hatcher.diskBoundaryTwoBasepoint.{u} ≃*
      Multiplicative ℤ :=
  (Hatcher.fundamentalGroupMulEquivOfHomotopyEquivOfEq
    Hatcher.diskBoundaryTwoHomeomorphCircle.{u}.toHomotopyEquiv
    Hatcher.diskBoundaryTwoBasepoint.{u} 1
    Hatcher.diskBoundaryTwoHomeomorphCircle_basepoint.{u}).trans
      Hatcher.Circle.fundamentalGroupEquivInt

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem diskBoundaryTwoFundamentalGroupEquivInt_generator :
    diskBoundaryTwoFundamentalGroupEquivInt.{u}
        diskBoundaryTwoGenerator.{u} =
      Multiplicative.ofAdd 1 := by
  rw [diskBoundaryTwoFundamentalGroupEquivInt, MulEquiv.trans_apply]
  rw [Hatcher.fundamentalGroupMulEquivOfHomotopyEquivOfEq_apply]
  have hbase :
      Hatcher.diskBoundaryTwoHomeomorphCircle.{u}.toHomotopyEquiv.toFun
          Hatcher.diskBoundaryTwoBasepoint.{u} = (1 : _root_.Circle) :=
    Hatcher.diskBoundaryTwoHomeomorphCircle_basepoint.{u}
  change Hatcher.Circle.fundamentalGroupEquivInt
      (FundamentalGroup.mapOfEq
        Hatcher.diskBoundaryTwoHomeomorphCircle.{u}.toHomotopyEquiv.toFun
        hbase diskBoundaryTwoGenerator.{u}) = Multiplicative.ofAdd 1
  rw [diskBoundaryTwoGenerator, FundamentalGroup.mapOfEq_apply]
  have hp :
      (Hatcher.diskBoundaryTwoLoop.{u}.map
          Hatcher.diskBoundaryTwoHomeomorphCircle.{u}.toHomotopyEquiv.toFun.continuous).cast
        hbase.symm hbase.symm = Hatcher.Circle.loopOfInt 1 := by
    exact Hatcher.diskBoundaryTwoHomeomorphCircle_map_loop.{u}
  change Hatcher.Circle.fundamentalGroupEquivInt
      (Path.Homotopic.Quotient.mk
        ((Hatcher.diskBoundaryTwoLoop.{u}.map
          Hatcher.diskBoundaryTwoHomeomorphCircle.{u}.toHomotopyEquiv.toFun.continuous).cast
            hbase.symm hbase.symm)) = Multiplicative.ofAdd 1
  rw [hp]
  rw [Hatcher.Circle.fundamentalGroupEquivInt_apply]
  exact congrArg Multiplicative.ofAdd
    (Hatcher.Circle.windingNumberFun_loopOfInt 1)

/-- The standard positively oriented boundary loop generates the whole
fundamental group of the two-disk boundary. -/
theorem diskBoundaryTwoGenerator_zpowers_eq_top :
    Subgroup.zpowers diskBoundaryTwoGenerator.{u} = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  rw [Subgroup.mem_zpowers_iff]
  let e := diskBoundaryTwoFundamentalGroupEquivInt.{u}
  let n : ℤ := Multiplicative.toAdd (e g)
  refine ⟨n, e.injective ?_⟩
  rw [map_zpow, diskBoundaryTwoFundamentalGroupEquivInt_generator]
  rw [← ofAdd_zsmul]
  change Multiplicative.ofAdd (n * (1 : ℤ)) = e g
  simp [n]

variable (f : ∀ _j : J, BoundaryTwo → X) (x₀ : X)
variable (γ : ∀ j : J,
  Path x₀ (f j Hatcher.diskBoundaryTwoBasepoint))

/-- The canonical positively oriented meridian in the `j`-th overlap piece. -/
noncomputable def intersectionMeridian (j : J) :
    FundamentalGroup
      (↑(intersectionPiece f
        (fun _ : J ↦ Hatcher.diskBoundaryTwoBasepoint) x₀ γ j))
      (intersectionPieceBasepoint f
        (fun _ : J ↦ Hatcher.diskBoundaryTwoBasepoint) x₀ γ j) :=
  (intersectionPieceFundamentalGroupEquiv f
      (fun _ : J ↦ Hatcher.diskBoundaryTwoBasepoint) x₀ γ j).symm
    diskBoundaryTwoGenerator.{u}

/-- The chosen meridian generates the fundamental group of its overlap
piece.  This is the form needed to pass from the indexed overlap cover to a
normal-closure calculation. -/
theorem intersectionMeridian_zpowers_eq_top (j : J) :
    Subgroup.zpowers (intersectionMeridian f x₀ γ j) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  rw [Subgroup.mem_zpowers_iff]
  let e := intersectionPieceFundamentalGroupEquiv f
    (fun _ : J ↦ Hatcher.diskBoundaryTwoBasepoint) x₀ γ j
  have hg : e g ∈ Subgroup.zpowers diskBoundaryTwoGenerator.{u} := by
    rw [diskBoundaryTwoGenerator_zpowers_eq_top]
    trivial
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨n, e.injective ?_⟩
  rw [map_zpow, intersectionMeridian]
  rw [e.apply_symm_apply]
  exact hn

/-- Directly applying the piece-to-base map to the canonical meridian gives
the transported attaching loop. -/
theorem intersectionMeridian_toBase_eq_attachingLoop
    (hf : ∀ j, Continuous (f j)) (j : J) :
    FundamentalGroup.mapOfEq
        (intersectionPieceToBase f
          (fun _ : J ↦ Hatcher.diskBoundaryTwoBasepoint) x₀ γ hf j)
        (intersectionPieceToBase_basepoint f
          (fun _ : J ↦ Hatcher.diskBoundaryTwoBasepoint) x₀ γ hf j)
        (intersectionMeridian f x₀ γ j) =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath (γ j)).symm
        (FundamentalGroup.map
          (⟨f j, hf j⟩ : C(BoundaryTwo, X))
          Hatcher.diskBoundaryTwoBasepoint diskBoundaryTwoGenerator.{u}) := by
  have h := DFunLike.congr_fun
    (intersectionPieceToBase_fundamentalGroup f
      (fun _ : J ↦ Hatcher.diskBoundaryTwoBasepoint) x₀ γ hf j)
    (intersectionMeridian f x₀ γ j)
  simpa [intersectionMeridian, MonoidHom.comp_apply] using h

/-- The canonical overlap meridian maps through the base-side cover to the
original attaching loop, transported from the attaching point to `x₀` along
the chosen path `γ j`. -/
theorem intersectionMeridian_eq_attachingLoop
    (hf : ∀ j, Continuous (f j)) (j : J) :
    baseCoverFundamentalGroupEquiv f
        (fun _ : J ↦ Hatcher.diskBoundaryTwoBasepoint) x₀ γ hf
        (FundamentalGroup.mapOfEq
          (intersectionPieceToBaseCover f
            (fun _ : J ↦ Hatcher.diskBoundaryTwoBasepoint) x₀ γ j)
          (intersectionPieceToBaseCover_basepoint f
            (fun _ : J ↦ Hatcher.diskBoundaryTwoBasepoint) x₀ γ j)
          (intersectionMeridian f x₀ γ j)) =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath (γ j)).symm
        (FundamentalGroup.map
          (⟨f j, hf j⟩ : C(BoundaryTwo, X))
          Hatcher.diskBoundaryTwoBasepoint diskBoundaryTwoGenerator.{u}) := by
  rw [baseCoverFundamentalGroupEquiv_map_intersectionPiece]
  exact intersectionMeridian_toBase_eq_attachingLoop f x₀ γ hf j

end TwoCells

end Hatcher.VanKampen.AuxiliaryCellAttachment
