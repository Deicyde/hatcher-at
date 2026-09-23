import Hatcher.Appendix.CompactSubspaceFiniteSubcomplex
import Hatcher.Appendix.ClassicalSkeletonCellAttachment
import Hatcher.VanKampen.CellAttachmentComponents

/-!
# Path connectedness of the classical two-skeleton

This file proves the component-level ingredient in Hatcher's proof that a
path-connected CW complex has the same fundamental group as its two-skeleton.
An ambient path lies in a bounded skeleton, and higher-dimensional cell
attachments can then be removed one at a time without merging its endpoints'
components.
-/

noncomputable section

open Set unitInterval

namespace Hatcher.ClassicalCW

universe u

open Topology

/-- The two-skeleton of a path-connected classical CW complex is path-connected. -/
theorem pathConnectedSpace_twoSkeleton
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [PathConnectedSpace C] :
    PathConnectedSpace (CWComplex.skeleton C (2 : ℕ∞)) := by
  let liftSkeleton {m n : ℕ} (h : m ≤ n) :
      ↑(CWComplex.skeleton C m) → ↑(CWComplex.skeleton C n) :=
    fun x ↦ ⟨x.1, CWComplex.skeleton_mono (by exact_mod_cast h) x.2⟩
  have hlift_continuous {m n : ℕ} (h : m ≤ n) :
      Continuous (liftSkeleton h) := by
    exact continuous_subtype_val.subtype_mk _
  have hnonempty : ∀ n : ℕ,
      Nonempty ↑(CWComplex.skeleton C n) →
        Nonempty ↑(CWComplex.skeleton C (2 : ℕ)) := by
    intro n
    induction n with
    | zero =>
        intro h
        exact h.map (liftSkeleton (by omega))
    | succ n ih =>
        intro h
        by_cases hn : n + 1 ≤ 2
        · exact h.map (liftSkeleton hn)
        · apply ih
          rcases h with ⟨x⟩
          have hx : x.1 ∈ (CWComplex.skeleton C n : Set X) ∪
              ⋃ j : RelCWComplex.cell C (n + 1),
                RelCWComplex.closedCell (n + 1) j := by
            rw [RelCWComplex.skeleton_union_iUnion_closedCell_eq_skeleton_succ]
            exact x.2
          rcases hx with hx | hx
          · exact ⟨⟨x.1, hx⟩⟩
          · simp only [Set.mem_iUnion] at hx
            obtain ⟨j, _⟩ := hx
            obtain ⟨z, hz⟩ :=
              RelCWComplex.nonempty_cellFrontier (Nat.succ_ne_zero n) j
            exact ⟨⟨z, RelCWComplex.cellFrontier_subset_skeleton n j hz⟩⟩
  have htwo : Nonempty ↑(CWComplex.skeleton C (2 : ℕ)) := by
    let x : C := Classical.choice (PathConnectedSpace.nonempty : Nonempty C)
    have hx : x.1 ∈ ⋃ n : ℕ, CWComplex.skeleton C n := by
      rw [RelCWComplex.iUnion_skeleton_eq_complex]
      exact x.2
    simp only [Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    exact hnonempty n ⟨⟨x.1, hn⟩⟩
  refine ⟨htwo, ?_⟩
  intro x y
  let xC : C := ⟨x.1, (CWComplex.skeleton C (2 : ℕ)).subset_complex x.2⟩
  let yC : C := ⟨y.1, (CWComplex.skeleton C (2 : ℕ)).subset_complex y.2⟩
  obtain ⟨p⟩ := PathConnectedSpace.joined xC yC
  let pX : I → X := fun t ↦ (p t : X)
  have hpX : Continuous pX := continuous_subtype_val.comp p.continuous
  have hpC : Set.range pX ⊆ C := by
    rintro _ ⟨t, rfl⟩
    exact (p t).2
  obtain ⟨n, hn⟩ := Hatcher.compact_subset_skeleton
    (isCompact_range hpX) hpC
  have hxN : x.1 ∈ CWComplex.skeleton C n := by
    apply hn
    refine ⟨0, ?_⟩
    change (p 0 : X) = x.1
    exact congrArg Subtype.val p.source
  have hyN : y.1 ∈ CWComplex.skeleton C n := by
    apply hn
    refine ⟨1, ?_⟩
    change (p 1 : X) = y.1
    exact congrArg Subtype.val p.target
  let xN : ↑(CWComplex.skeleton C n) := ⟨x.1, hxN⟩
  let yN : ↑(CWComplex.skeleton C n) := ⟨y.1, hyN⟩
  let pN : Path xN yN :=
    { toFun := fun t ↦ ⟨pX t, hn ⟨t, rfl⟩⟩
      continuous_toFun := hpX.subtype_mk _
      source' := by
        ext
        exact congrArg (fun z : C ↦ (z : X)) p.source
      target' := by
        ext
        exact congrArg (fun z : C ↦ (z : X)) p.target }
  have hdescend : ∀ n : ℕ, ∀ (a b : ↑(CWComplex.skeleton C n)),
      (ha : a.1 ∈ CWComplex.skeleton C (2 : ℕ)) →
      (hb : b.1 ∈ CWComplex.skeleton C (2 : ℕ)) →
      Joined a b → Joined
        (⟨a.1, ha⟩ : ↑(CWComplex.skeleton C (2 : ℕ)))
        (⟨b.1, hb⟩ : ↑(CWComplex.skeleton C (2 : ℕ))) := by
    intro n
    induction n with
    | zero =>
        intro a b ha hb hab
        exact ⟨hab.somePath.map (hlift_continuous (by omega))⟩
    | succ n ih =>
        intro a b ha hb hab
        by_cases hn2 : n + 1 ≤ 2
        · exact ⟨hab.somePath.map (hlift_continuous hn2)⟩
        · have h2n : 2 ≤ n := by omega
          let a' : ↑(CWComplex.skeleton C n) :=
            ⟨a.1, CWComplex.skeleton_mono (by exact_mod_cast h2n) ha⟩
          let b' : ↑(CWComplex.skeleton C n) :=
            ⟨b.1, CWComplex.skeleton_mono (by exact_mod_cast h2n) hb⟩
          have ha' : skeletonInclusion C n a' = a := Subtype.ext rfl
          have hb' : skeletonInclusion C n b' = b := Subtype.ext rfl
          rw [← ha', ← hb'] at hab
          have hab' : Joined a' b' :=
            (Hatcher.joined_iff_of_attachCells_of_one_lt
              (skeletonInclusion_attachCells C n) (by omega) a' b').mp hab
          exact ih a' b' ha hb hab'
  exact hdescend n xN yN x.2 y.2 ⟨pN⟩

end Hatcher.ClassicalCW
