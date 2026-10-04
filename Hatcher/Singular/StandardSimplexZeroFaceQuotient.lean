/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.StandardSimplexBoundaryHorn
import Hatcher.Singular.PointQuotient
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The zero-face comparison of simplex point quotients
-/

noncomputable section

open CategoryTheory Limits Set Topology

namespace Hatcher.Simplex

/-- The zero face of the successor simplex, as a set. -/
def standardSimplexZeroFaceSet (n : ℕ) : Set (StandardSimplex (n + 1)) :=
  {x | x.weights 0 = 0}

theorem isClosed_standardSimplexZeroFaceSet (n : ℕ) :
    IsClosed (standardSimplexZeroFaceSet n) := by
  exact isClosed_eq
    (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) 0) continuous_const

theorem isClosed_standardSimplexZeroHorn (n : ℕ) :
    IsClosed (standardSimplexZeroHorn n) := by
  rw [show standardSimplexZeroHorn n =
      ⋃ i ∈ ({i : Fin (n + 2) | i ≠ 0} : Set (Fin (n + 2))),
        {x | x.weights i = 0} by
    ext x
    simp only [standardSimplexZeroHorn, mem_ofPred_eq, mem_iUnion, exists_prop]]
  exact (Set.toFinite {i : Fin (n + 2) | i ≠ 0}).isClosed_biUnion
    (fun i _ => isClosed_eq
      (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i) continuous_const)

theorem standardSimplexBoundary_succ_eq_zeroFace_union_zeroHorn (n : ℕ) :
    standardSimplexBoundary (n + 1) =
      standardSimplexZeroFaceSet n ∪ standardSimplexZeroHorn n := by
  ext x
  constructor
  · rintro ⟨i, hi⟩
    by_cases h0 : i = 0
    · left
      simpa [standardSimplexZeroFaceSet, h0] using hi
    · right
      exact ⟨i, h0, hi⟩
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact standardSimplexZeroHorn_subset_boundary n h

theorem standardSimplexZeroFace_injective (n : ℕ) :
    Function.Injective (standardSimplexZeroFace n) := by
  intro x y h
  ext i
  have hi := congrArg (fun z : StandardSimplex (n + 1) => z.weights i.succ) h
  simpa using hi

theorem standardSimplexZeroFace_range (n : ℕ) :
    Set.range (standardSimplexZeroFace n) = standardSimplexZeroFaceSet n := by
  ext x
  change x ∈ Set.range (Convexity.StdSimplex.map Fin.succ) ↔ _
  rw [Convexity.StdSimplex.mem_range_map_iff]
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h i hi
    by_cases h0 : i = 0
    · simpa [standardSimplexZeroFaceSet, h0] using h
    · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero h0
      exact (hi ⟨j, rfl⟩).elim

/-- Inserting a zero barycentric coordinate is a homeomorphism onto the zero
face of the successor simplex. -/
theorem standardSimplexZeroFace_isEmbedding (n : ℕ) :
    IsEmbedding (standardSimplexZeroFace n) := by
  let _ : T2Space (StandardSimplex (n + 1)) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).t2Space
  exact ((standardSimplexZeroFace n).continuous.isClosedEmbedding
    (standardSimplexZeroFace_injective n)).isEmbedding

noncomputable def standardSimplexZeroFaceHomeomorph (n : ℕ) :
    StandardSimplex n ≃ₜ standardSimplexZeroFaceSet n where
  toEquiv :=
    { toFun := fun x => ⟨standardSimplexZeroFace n x,
          standardSimplexZeroFace_weights_zero n x⟩
      invFun := fun y => (standardSimplexZeroFace_isEmbedding n).toHomeomorph.symm
        ⟨y.1, (Set.ext_iff.mp (standardSimplexZeroFace_range n) y.1).mpr y.2⟩
      left_inv := fun x => by
        exact (standardSimplexZeroFace_isEmbedding n).toHomeomorph_symm_apply x
      right_inv := fun y => by
        apply Subtype.ext
        change standardSimplexZeroFace n
            ((standardSimplexZeroFace_isEmbedding n).toHomeomorph.symm
              ⟨y.1, (Set.ext_iff.mp (standardSimplexZeroFace_range n) y.1).mpr y.2⟩) = y.1
        exact congrArg Subtype.val
          ((standardSimplexZeroFace_isEmbedding n).toHomeomorph.apply_symm_apply
            ⟨y.1, (Set.ext_iff.mp (standardSimplexZeroFace_range n) y.1).mpr y.2⟩) }
  continuous_toFun := (standardSimplexZeroFace n).continuous.subtype_mk _
  continuous_invFun :=
    (standardSimplexZeroFace_isEmbedding n).toHomeomorph.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)

@[simp]
theorem standardSimplexZeroFaceHomeomorph_apply_coe (n : ℕ)
    (x : StandardSimplex n) :
    (standardSimplexZeroFaceHomeomorph n x : StandardSimplex (n + 1)) =
      standardSimplexZeroFace n x := rfl

@[simp]
theorem standardSimplexZeroFaceHomeomorph_symm_apply (n : ℕ)
    (x : StandardSimplex n) :
    (standardSimplexZeroFaceHomeomorph n).symm
      ⟨standardSimplexZeroFace n x,
        standardSimplexZeroFace_weights_zero n x⟩ = x := by
  apply (standardSimplexZeroFaceHomeomorph n).injective
  ext
  simp

private theorem zeroFace_preimage_mem_boundary {n : ℕ}
    (x : StandardSimplex n)
    (hx : standardSimplexZeroFace n x ∈ standardSimplexZeroHorn n) :
    x ∈ standardSimplexBoundary n := by
  obtain ⟨i, hi0, hi⟩ := hx
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi0
  exact ⟨j, by simpa using hi⟩

private theorem boundary_mem_zeroHorn_of_not_zeroFace {n : ℕ}
    (x : standardSimplexBoundary (n + 1))
    (hx : x.1 ∉ standardSimplexZeroFaceSet n) :
    x.1 ∈ standardSimplexZeroHorn n := by
  have h := x.property
  have h' := Set.ext_iff.mp
    (standardSimplexBoundary_succ_eq_zeroFace_union_zeroHorn n) x.1
  exact (h'.mp h).resolve_left hx

/-- The square consisting of the boundary inclusion, zero face, zero horn,
and successor boundary is a pushout in `TopCat`. -/
theorem standardSimplexZeroFace_isPushout (n : ℕ) :
    IsPushout
      (standardSimplexPair n).map
      (TopPair.Hom.snd (standardSimplexZeroFacePairHom n))
      (TopPair.Hom.fst (standardSimplexZeroFacePairHom n))
      (Hatcher.Relative.TopTriple.pairAB.obj
        (standardSimplexBoundaryHornTriple n)).map := by
  classical
  let F : Set (standardSimplexBoundary (n + 1)) :=
    {x | x.1 ∈ standardSimplexZeroFaceSet n}
  let H : Set (standardSimplexBoundary (n + 1)) :=
    {x | x.1 ∈ standardSimplexZeroHorn n}
  have hF : IsClosed F :=
    (isClosed_standardSimplexZeroFaceSet n).preimage continuous_subtype_val
  have hH : IsClosed H :=
    (isClosed_standardSimplexZeroHorn n).preimage continuous_subtype_val
  have hFH : F ∪ H = Set.univ := by
    ext x
    simp only [F, H, mem_union, mem_ofPred_eq, mem_univ, iff_true]
    exact (Set.ext_iff.mp
      (standardSimplexBoundary_succ_eq_zeroFace_union_zeroHorn n) x.1).mp x.property
  apply IsPushout.mk'
  · exact (TopPair.Hom.w (standardSimplexZeroFacePairHom n)).symm
  · intro T φ ψ hφ hψ
    ext x
    have hx : x ∈ F ∪ H := by rw [hFH]; trivial
    rcases hx with hx | hx
    · let y : StandardSimplex n :=
        (standardSimplexZeroFaceHomeomorph n).symm ⟨x.1, hx⟩
      have hy : standardSimplexZeroFace n y = x.1 := by
        calc
          standardSimplexZeroFace n y =
              (standardSimplexZeroFaceHomeomorph n y).1 :=
            (standardSimplexZeroFaceHomeomorph_apply_coe n y).symm
          _ = x.1 := congrArg Subtype.val
            ((standardSimplexZeroFaceHomeomorph n).apply_symm_apply ⟨x.1, hx⟩)
      have hxy := ConcreteCategory.congr_hom hφ y
      change φ (standardSimplexZeroFaceToBoundary n y) =
        ψ (standardSimplexZeroFaceToBoundary n y) at hxy
      have hy' : standardSimplexZeroFaceToBoundary n y = x := Subtype.ext hy
      simpa only [hy'] using hxy
    · let y : standardSimplexZeroHorn n := ⟨x.1, hx⟩
      have hxy := ConcreteCategory.congr_hom hψ y
      change φ ((standardSimplexBoundaryHornTriple n).mapBA y) =
        ψ ((standardSimplexBoundaryHornTriple n).mapBA y) at hxy
      have hy : (standardSimplexBoundaryHornTriple n).mapBA y = x := Subtype.ext rfl
      simpa only [hy] using hxy
  · intro T a b hab
    let d : standardSimplexBoundary (n + 1) → T := fun x =>
      if hx : x.1 ∈ standardSimplexZeroFaceSet n then
        a ((standardSimplexZeroFaceHomeomorph n).symm ⟨x.1, hx⟩)
      else
        b ⟨x.1, boundary_mem_zeroHorn_of_not_zeroFace x hx⟩
    have hdF : ContinuousOn d F := by
      rw [continuousOn_iff_continuous_domRestrict]
      let e : F → standardSimplexZeroFaceSet n :=
        fun x => ⟨x.1.1, x.2⟩
      have he : Continuous e := by
        exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      have hc : Continuous (fun x : F =>
          a ((standardSimplexZeroFaceHomeomorph n).symm (e x))) :=
        a.hom.continuous.comp
          ((standardSimplexZeroFaceHomeomorph n).symm.continuous.comp he)
      convert hc using 1
      ext x
      change d x.1 = a ((standardSimplexZeroFaceHomeomorph n).symm (e x))
      have hx : x.1.1 ∈ standardSimplexZeroFaceSet n := x.property
      simp [d, e, hx]
    have hdH : ContinuousOn d H := by
      rw [continuousOn_iff_continuous_domRestrict]
      let e : H → standardSimplexZeroHorn n := fun x => ⟨x.1.1, x.2⟩
      have he : Continuous e := by
        exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      have hc : Continuous (fun x : H => b (e x)) := b.hom.continuous.comp he
      convert hc using 1
      ext x
      change d x.1 = b (e x)
      dsimp only [d]
      split_ifs with hx
      · let y : StandardSimplex n :=
          (standardSimplexZeroFaceHomeomorph n).symm ⟨x.1.1, hx⟩
        have hy : standardSimplexZeroFace n y = x.1.1 := by
          calc
            standardSimplexZeroFace n y =
                (standardSimplexZeroFaceHomeomorph n y).1 :=
              (standardSimplexZeroFaceHomeomorph_apply_coe n y).symm
            _ = x.1.1 := congrArg Subtype.val
              ((standardSimplexZeroFaceHomeomorph n).apply_symm_apply ⟨x.1.1, hx⟩)
        have hxh : x.1.1 ∈ standardSimplexZeroHorn n := x.property
        have hyb : y ∈ standardSimplexBoundary n := by
          apply zeroFace_preimage_mem_boundary y
          rw [hy]
          exact hxh
        have hw := ConcreteCategory.congr_hom hab
          (⟨y, hyb⟩ : standardSimplexBoundary n)
        change a y = b (standardSimplexBoundaryZeroFaceToHorn n ⟨y, hyb⟩) at hw
        have heq : standardSimplexBoundaryZeroFaceToHorn n ⟨y, hyb⟩ = e x :=
          Subtype.ext hy
        simpa only [heq] using hw
      · rfl
    refine ⟨TopCat.ofHom ⟨d, ?_⟩, ?_, ?_⟩
    · rw [← continuousOn_univ, ← hFH]
      exact hdF.union_of_isClosed hdH hF hH
    · ext x
      change d (standardSimplexZeroFaceToBoundary n x) = a x
      have h0 : (standardSimplexZeroFaceToBoundary n x).1 ∈
          standardSimplexZeroFaceSet n := standardSimplexZeroFace_weights_zero n x
      simp [d, h0]
      exact congrArg (fun y => a y)
        (standardSimplexZeroFaceHomeomorph_symm_apply n x)
    · ext x
      change d ((standardSimplexBoundaryHornTriple n).mapBA x) = b x
      dsimp only [d]
      split_ifs with hx
      · let y : StandardSimplex n :=
          (standardSimplexZeroFaceHomeomorph n).symm
            ⟨((standardSimplexBoundaryHornTriple n).mapBA x).1, hx⟩
        have hy : standardSimplexZeroFace n y =
            ((standardSimplexBoundaryHornTriple n).mapBA x).1 := by
          calc
            standardSimplexZeroFace n y =
                (standardSimplexZeroFaceHomeomorph n y).1 :=
              (standardSimplexZeroFaceHomeomorph_apply_coe n y).symm
            _ = ((standardSimplexBoundaryHornTriple n).mapBA x).1 :=
              congrArg Subtype.val
                ((standardSimplexZeroFaceHomeomorph n).apply_symm_apply
                  ⟨((standardSimplexBoundaryHornTriple n).mapBA x).1, hx⟩)
        have hyb : y ∈ standardSimplexBoundary n := by
          apply zeroFace_preimage_mem_boundary y
          rw [hy]
          exact x.property
        have hw := ConcreteCategory.congr_hom hab
          (⟨y, hyb⟩ : standardSimplexBoundary n)
        change a y = b (standardSimplexBoundaryZeroFaceToHorn n ⟨y, hyb⟩) at hw
        have heq : standardSimplexBoundaryZeroFaceToHorn n ⟨y, hyb⟩ = x :=
          Subtype.ext (hy.trans rfl)
        simpa only [heq] using hw
      · rfl

private theorem standardSimplexZeroFaceOuterIsPushout (n : ℕ) :
    IsPushout
      (standardSimplexPair n).map
      (Hatcher.Relative.pointQuotientCollapse (standardSimplexPair n))
      ((TopPair.Hom.fst (standardSimplexZeroFacePairHom n)) ≫
        Hatcher.Relative.pointQuotientProjection
          (Hatcher.Relative.TopTriple.pairAB.obj
            (standardSimplexBoundaryHornTriple n)))
      (Hatcher.Relative.pointQuotientPointInclusion
        (Hatcher.Relative.TopTriple.pairAB.obj
          (standardSimplexBoundaryHornTriple n))) := by
  have h₁ := standardSimplexZeroFace_isPushout n
  have h₂ := IsPushout.of_hasPushout
    (Hatcher.Relative.TopTriple.pairAB.obj
      (standardSimplexBoundaryHornTriple n)).map
    (Hatcher.Relative.pointQuotientCollapse
      (Hatcher.Relative.TopTriple.pairAB.obj
        (standardSimplexBoundaryHornTriple n)))
  have h := h₁.paste_vert h₂
  have hc :
      TopPair.Hom.snd (standardSimplexZeroFacePairHom n) ≫
          Hatcher.Relative.pointQuotientCollapse
            (Hatcher.Relative.TopTriple.pairAB.obj
              (standardSimplexBoundaryHornTriple n)) =
        Hatcher.Relative.pointQuotientCollapse (standardSimplexPair n) :=
    TopCat.isTerminalPUnit.hom_ext _ _
  rw [hc] at h
  simpa only [Hatcher.Relative.pointQuotientProjection,
    Hatcher.Relative.pointQuotientPointInclusion,
    Hatcher.Relative.pointQuotient] using h

/-- The zero face identifies the pointed quotients
`Δ[n]/∂Δ[n]` and `∂Δ[n+1]/Λ⁰[n+1]`.  Its forward map is the
functorial map induced by the canonical zero-face morphism of pairs.  The
construction also covers `n = 0`, where the first boundary is empty. -/
noncomputable def zeroFacePointQuotientIso (n : ℕ) :
    Hatcher.Relative.pointQuotient (standardSimplexPair n) ≅
      Hatcher.Relative.pointQuotient
        (Hatcher.Relative.TopTriple.pairAB.obj
          (standardSimplexBoundaryHornTriple n)) :=
  (IsPushout.of_hasPushout
      (standardSimplexPair n).map
      (Hatcher.Relative.pointQuotientCollapse (standardSimplexPair n))).isoIsPushout
    _ _ (standardSimplexZeroFaceOuterIsPushout n)

@[simp]
theorem zeroFacePointQuotientIso_hom (n : ℕ) :
    (zeroFacePointQuotientIso n).hom =
      Hatcher.Relative.pointQuotientMap
        (standardSimplexZeroFacePairHom n) := by
  unfold zeroFacePointQuotientIso
  apply (IsPushout.of_hasPushout
    (standardSimplexPair n).map
    (Hatcher.Relative.pointQuotientCollapse (standardSimplexPair n))).hom_ext
  · rw [IsPushout.inl_isoIsPushout_hom]
    exact (Hatcher.Relative.pointQuotientProjection_naturality
      (standardSimplexZeroFacePairHom n)).symm
  · rw [IsPushout.inr_isoIsPushout_hom]
    exact (Hatcher.Relative.pointQuotientPointInclusion_naturality
      (standardSimplexZeroFacePairHom n)).symm

end Hatcher.Simplex
