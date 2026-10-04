/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.TripleChains

/-!
# The chain-level formula for the connecting map of a triple

For a topological triple `B ⊆ A ⊆ X`, the connecting morphism sends the
class of a relative cycle in `C_n(X,A;R)` to the class of the boundary of any
lift in `C_n(X,B;R)`, viewed in `C_{n-1}(A,B;R)`.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits

namespace Hatcher.Relative

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- **Hatcher, Example 2.23 (page 125).** The connecting morphism in the long
exact sequence of a topological triple sends a relative cycle class to the
class of its boundary.  The hypotheses explicitly give the lift to
`C_n(X,B;R)` and its boundary representative in `C_{n-1}(A,B;R)`, so the
formula fixes the sign as `+1`. -/
theorem tripleConnecting_eq
    (T : TopTriple.{w}) (R : C) (n m : ℕ) (h : m + 1 = n)
    {Q : C}
    (x₃ : Q ⟶ ((chainComplexFunctor R).obj (TopTriple.pairXA.obj T)).X n)
    (hx₃ : x₃ ≫ ((chainComplexFunctor R).obj
      (TopTriple.pairXA.obj T)).d n m = 0)
    (x₂ : Q ⟶ ((chainComplexFunctor R).obj (TopTriple.pairXB.obj T)).X n)
    (hx₂ : x₂ ≫ (tripleChainComplexMapXBToXA T R).f n = x₃)
    (x₁ : Q ⟶ ((chainComplexFunctor R).obj (TopTriple.pairAB.obj T)).X m)
    (hx₁ : x₁ ≫ (tripleChainComplexMapABToXB T R).f m =
      x₂ ≫ ((chainComplexFunctor R).obj (TopTriple.pairXB.obj T)).d n m)
    (k : ℕ) (hk : (ComplexShape.down ℕ).next m = k)
    (hx₁cycle : x₁ ≫ ((chainComplexFunctor R).obj
      (TopTriple.pairAB.obj T)).d m k = 0) :
    ((chainComplexFunctor R).obj (TopTriple.pairXA.obj T)).liftCycles x₃ m
        ((ComplexShape.down ℕ).next_eq' (by simpa using h)) hx₃ ≫
      ((chainComplexFunctor R).obj (TopTriple.pairXA.obj T)).homologyπ n ≫
      tripleConnecting T R n m h =
    ((chainComplexFunctor R).obj (TopTriple.pairAB.obj T)).liftCycles x₁ k hk hx₁cycle ≫
      ((chainComplexFunctor R).obj (TopTriple.pairAB.obj T)).homologyπ m := by
  let hT := tripleChainComplexShortComplex_shortExact T R
  change _ ≫ _ ≫ hT.δ n m _ = _
  exact hT.δ_eq n m (by simpa using h) x₃ hx₃ x₂ hx₂ x₁ hx₁ k hk

/-- The connecting morphism of a topological triple is an isomorphism when
the two adjacent homology groups of `(X,B)` vanish. -/
theorem tripleConnecting_isIso
    (T : TopTriple.{w}) (R : C) (n m : ℕ) (h : m + 1 = n)
    (hn : IsZero ((homologyFunctor R n).obj (TopTriple.pairXB.obj T)))
    (hm : IsZero ((homologyFunctor R m).obj (TopTriple.pairXB.obj T))) :
    IsIso (tripleConnecting T R n m h) := by
  let S := tripleSequence T R n m h
  have hS : S.Exact := tripleSequence_exact T R n m h
  let δ := S.map' 2 3
  have : Mono δ :=
    (hS.exact 1).mono_g (hn.eq_of_src _ _)
  have : Epi δ :=
    (hS.exact 2).epi_f (hm.eq_of_tgt _ _)
  change IsIso δ
  exact isIso_of_mono_of_epi δ

end Hatcher.Relative
