/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.Homotopy

/-!
# Maps and homotopies of augmented chain complexes

This file lifts augmentation-compatible chain maps, chain homotopies, and
chain-homotopy equivalences through `ChainComplex.augment`.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace ChainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Lift a chain map and a compatible map of augmentation objects to the
corresponding augmented chain complexes. -/
noncomputable def augmentMap
    {K L : ChainComplex C ℕ} {P Q : C}
    (εK : K.X 0 ⟶ P) (hK : K.d 1 0 ≫ εK = 0)
    (εL : L.X 0 ⟶ Q) (hL : L.d 1 0 ≫ εL = 0)
    (f : K ⟶ L) (a : P ⟶ Q)
    (ha : εK ≫ a = f.f 0 ≫ εL) :
    augment K εK hK ⟶ augment L εL hL where
  f
    | 0 => a
    | n + 1 => f.f n
  comm' i j _ := by
    match i, j with
    | 0, _ => simp [augment]
    | 1, 0 => exact ha.symm
    | _ + 2, 0 => simp [augment]
    | i + 1, j + 1 => simp [augment, f.comm]

@[simp]
lemma augmentMap_f_zero
    {K L : ChainComplex C ℕ} {P Q : C}
    (εK : K.X 0 ⟶ P) (hK : K.d 1 0 ≫ εK = 0)
    (εL : L.X 0 ⟶ Q) (hL : L.d 1 0 ≫ εL = 0)
    (f : K ⟶ L) (a : P ⟶ Q)
    (ha : εK ≫ a = f.f 0 ≫ εL) :
    (augmentMap εK hK εL hL f a ha).f 0 = a := rfl

@[simp]
lemma augmentMap_f_succ
    {K L : ChainComplex C ℕ} {P Q : C}
    (εK : K.X 0 ⟶ P) (hK : K.d 1 0 ≫ εK = 0)
    (εL : L.X 0 ⟶ Q) (hL : L.d 1 0 ≫ εL = 0)
    (f : K ⟶ L) (a : P ⟶ Q)
    (ha : εK ≫ a = f.f 0 ≫ εL) (n : ℕ) :
    (augmentMap εK hK εL hL f a ha).f (n + 1) = f.f n := rfl

private noncomputable def augmentHomotopyHom
    {K L : ChainComplex C ℕ} {P Q : C}
    (εK : K.X 0 ⟶ P) (hK : K.d 1 0 ≫ εK = 0)
    (εL : L.X 0 ⟶ Q) (hL : L.d 1 0 ≫ εL = 0)
    {f g : K ⟶ L} (h : Homotopy f g) :
    ∀ i j, (augment K εK hK).X i ⟶ (augment L εL hL).X j := fun i j ↦
  match i, j with
  | 0, _ => 0
  | _ + 1, 0 => 0
  | i + 1, j + 1 => h.hom i j

set_option backward.isDefEq.respectTransparency false in
/-- Lift a chain homotopy through `ChainComplex.augment`, provided the two
augmented maps agree in degree zero and restrict to the original maps in every
successor degree. -/
noncomputable def augmentHomotopy
    {K L : ChainComplex C ℕ} {P Q : C}
    (εK : K.X 0 ⟶ P) (hK : K.d 1 0 ≫ εK = 0)
    (εL : L.X 0 ⟶ Q) (hL : L.d 1 0 ≫ εL = 0)
    {f g : K ⟶ L} {F G : augment K εK hK ⟶ augment L εL hL}
    (h : Homotopy f g) (hzero : F.f 0 = G.f 0)
    (hF : ∀ n, F.f (n + 1) = f.f n)
    (hG : ∀ n, G.f (n + 1) = g.f n) : Homotopy F G where
  hom := augmentHomotopyHom εK hK εL hL h
  zero i j hij := by
    obtain _ | i := i
    · rfl
    obtain _ | j := j
    · rfl
    apply h.zero i j
    simpa using hij
  comm i := by
    obtain _ | n := i
    · rw [Homotopy.dNext_zero_chainComplex,
        Homotopy.prevD_chainComplex]
      simpa only [augmentHomotopyHom, zero_comp, zero_add] using hzero
    · rw [Homotopy.dNext_succ_chainComplex,
        Homotopy.prevD_chainComplex, hF n, hG n]
      obtain _ | n := n
      · have hn := h.comm 0
        rw [Homotopy.dNext_zero_chainComplex,
          Homotopy.prevD_chainComplex] at hn
        change f.f 0 = εK ≫ (0 : P ⟶ L.X 0) +
          h.hom 0 (0 + 1) ≫ L.d (0 + 1) 0 + g.f 0
        rw [comp_zero, zero_add]
        simpa only [zero_add] using hn
      · have hn := h.comm (n + 1)
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex] at hn
        change f.f (n + 1) =
          K.d (n + 1) n ≫ h.hom n (n + 1) +
            h.hom (n + 1) (n + 1 + 1) ≫
              L.d (n + 1 + 1) (n + 1) + g.f (n + 1)
        exact hn

/-- Lift an augmentation-compatible chain-homotopy equivalence through
`ChainComplex.augment`. -/
noncomputable def augmentHomotopyEquiv
    {K L : ChainComplex C ℕ} {P : C}
    (εK : K.X 0 ⟶ P) (hK : K.d 1 0 ≫ εK = 0)
    (εL : L.X 0 ⟶ P) (hL : L.d 1 0 ≫ εL = 0)
    (e : HomotopyEquiv K L)
    (he : εK = e.hom.f 0 ≫ εL)
    (he' : εL = e.inv.f 0 ≫ εK) :
    HomotopyEquiv (augment K εK hK) (augment L εL hL) where
  hom := augmentMap εK hK εL hL e.hom (𝟙 P) (by simpa using he)
  inv := augmentMap εL hL εK hK e.inv (𝟙 P) (by simpa using he')
  homotopyHomInvId :=
    augmentHomotopy εK hK εK hK e.homotopyHomInvId
      (by simp [augmentMap])
      (fun n ↦ by simp [augmentMap])
      (fun n ↦ by simp)
  homotopyInvHomId :=
    augmentHomotopy εL hL εL hL e.homotopyInvHomId
      (by simp [augmentMap])
      (fun n ↦ by simp [augmentMap])
      (fun n ↦ by simp)

end ChainComplex
