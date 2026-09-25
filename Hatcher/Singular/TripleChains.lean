import Hatcher.Singular.Relative
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp

/-!
# Topological triples

This file packages a nested triple of spaces `B ↪ A ↪ X`, its morphisms, and the
three associated topological pairs.  The chain-level short exact sequence of a triple
is developed separately from this thin topological interface.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits

namespace Hatcher.Relative

universe w v u

/-- A topological triple `(X, A, B)` consists of composable topological embeddings
`B ↪ A ↪ X`. -/
structure TopTriple where
  /-- The ambient space `X`. -/
  X : TopCat.{w}
  /-- The intermediate subspace `A`. -/
  A : TopCat.{w}
  /-- The innermost subspace `B`. -/
  B : TopCat.{w}
  /-- The embedding `B ↪ A`. -/
  mapBA : B ⟶ A
  /-- The embedding `A ↪ X`. -/
  mapAX : A ⟶ X
  /-- The map `B → A` is a topological embedding. -/
  isEmbedding_mapBA : Topology.IsEmbedding mapBA
  /-- The map `A → X` is a topological embedding. -/
  isEmbedding_mapAX : Topology.IsEmbedding mapAX

namespace TopTriple

/-- The composite embedding `B ↪ X`. -/
abbrev mapBX (T : TopTriple.{w}) : T.B ⟶ T.X :=
  T.mapBA ≫ T.mapAX

/-- The composite `B → X` of a topological triple is an embedding. -/
lemma isEmbedding_mapBX (T : TopTriple.{w}) : Topology.IsEmbedding T.mapBX :=
  T.isEmbedding_mapAX.comp T.isEmbedding_mapBA

/-- A morphism of topological triples is a compatible map on each of `B`, `A`, and `X`. -/
@[ext]
structure Hom (P Q : TopTriple.{w}) where
  /-- The map on ambient spaces. -/
  mapX : P.X ⟶ Q.X
  /-- The map on intermediate subspaces. -/
  mapA : P.A ⟶ Q.A
  /-- The map on innermost subspaces. -/
  mapB : P.B ⟶ Q.B
  /-- Compatibility with the embeddings `B ↪ A`. -/
  wBA : mapB ≫ Q.mapBA = P.mapBA ≫ mapA
  /-- Compatibility with the embeddings `A ↪ X`. -/
  wAX : mapA ≫ Q.mapAX = P.mapAX ≫ mapX

instance : Category TopTriple where
  Hom := Hom
  id T :=
    { mapX := 𝟙 T.X
      mapA := 𝟙 T.A
      mapB := 𝟙 T.B
      wBA := by simp
      wAX := by simp }
  comp f g :=
    { mapX := f.mapX ≫ g.mapX
      mapA := f.mapA ≫ g.mapA
      mapB := f.mapB ≫ g.mapB
      wBA := by
        rw [Category.assoc, g.wBA, ← Category.assoc, f.wBA, Category.assoc]
      wAX := by
        rw [Category.assoc, g.wAX, ← Category.assoc, f.wAX, Category.assoc] }
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp

/-- Construct a morphism of topological triples from its three component maps. -/
def homMk {P Q : TopTriple.{w}}
    (mapX : P.X ⟶ Q.X) (mapA : P.A ⟶ Q.A) (mapB : P.B ⟶ Q.B)
    (wBA : mapB ≫ Q.mapBA = P.mapBA ≫ mapA)
    (wAX : mapA ≫ Q.mapAX = P.mapAX ≫ mapX) : P ⟶ Q :=
  ⟨mapX, mapA, mapB, wBA, wAX⟩

@[simp]
lemma Hom.mapX_id (T : TopTriple.{w}) : Hom.mapX (𝟙 T) = 𝟙 T.X := rfl

@[simp]
lemma Hom.mapA_id (T : TopTriple.{w}) : Hom.mapA (𝟙 T) = 𝟙 T.A := rfl

@[simp]
lemma Hom.mapB_id (T : TopTriple.{w}) : Hom.mapB (𝟙 T) = 𝟙 T.B := rfl

@[simp]
lemma Hom.mapX_comp {P Q S : TopTriple.{w}} (f : P ⟶ Q) (g : Q ⟶ S) :
    Hom.mapX (f ≫ g) = f.mapX ≫ g.mapX := rfl

@[simp]
lemma Hom.mapA_comp {P Q S : TopTriple.{w}} (f : P ⟶ Q) (g : Q ⟶ S) :
    Hom.mapA (f ≫ g) = f.mapA ≫ g.mapA := rfl

@[simp]
lemma Hom.mapB_comp {P Q S : TopTriple.{w}} (f : P ⟶ Q) (g : Q ⟶ S) :
    Hom.mapB (f ≫ g) = f.mapB ≫ g.mapB := rfl

@[reassoc]
lemma Hom.wBX {P Q : TopTriple.{w}} (f : P ⟶ Q) :
    f.mapB ≫ Q.mapBX = P.mapBX ≫ f.mapX := by
  rw [show Q.mapBX = Q.mapBA ≫ Q.mapAX from rfl]
  rw [show P.mapBX = P.mapBA ≫ P.mapAX from rfl]
  rw [← Category.assoc, f.wBA, Category.assoc, f.wAX]
  exact (Category.assoc _ _ _).symm

/-- The pair `(A, B)` associated to a topological triple. -/
def pairAB : TopTriple.{w} ⥤ TopPair.{w} where
  obj T := TopPair.of T.mapBA T.isEmbedding_mapBA
  map f := TopPair.ofHom f.mapA f.mapB f.wBA
  map_id T := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl
  map_comp f g := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl

/-- The pair `(X, B)` associated to a topological triple. -/
def pairXB : TopTriple.{w} ⥤ TopPair.{w} where
  obj T := TopPair.of T.mapBX T.isEmbedding_mapBX
  map f := TopPair.ofHom f.mapX f.mapB f.wBX
  map_id T := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl
  map_comp f g := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl

/-- The pair `(X, A)` associated to a topological triple. -/
def pairXA : TopTriple.{w} ⥤ TopPair.{w} where
  obj T := TopPair.of T.mapAX T.isEmbedding_mapAX
  map f := TopPair.ofHom f.mapX f.mapA f.wAX
  map_id T := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl
  map_comp f g := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl

/-- The canonical map of pairs `(A, B) → (X, B)`. -/
def pairABToXB (T : TopTriple.{w}) : pairAB.obj T ⟶ pairXB.obj T :=
  TopPair.ofHom T.mapAX (𝟙 T.B) (by
    change (𝟙 T.B) ≫ (T.mapBA ≫ T.mapAX) = T.mapBA ≫ T.mapAX
    simp)

/-- The canonical map of pairs `(X, B) → (X, A)`. -/
def pairXBToXA (T : TopTriple.{w}) : pairXB.obj T ⟶ pairXA.obj T :=
  TopPair.ofHom (𝟙 T.X) T.mapBA (by
    change T.mapBA ≫ T.mapAX = (T.mapBA ≫ T.mapAX) ≫ 𝟙 T.X
    simp)

@[simp]
lemma pairAB_obj_map (T : TopTriple.{w}) : (pairAB.obj T).map = T.mapBA := rfl

@[simp]
lemma pairXB_obj_map (T : TopTriple.{w}) : (pairXB.obj T).map = T.mapBX := rfl

@[simp]
lemma pairXA_obj_map (T : TopTriple.{w}) : (pairXA.obj T).map = T.mapAX := rfl

/-- The canonical maps `(A, B) → (X, B)` are natural in the triple. -/
def pairABToXBNatTrans : pairAB ⟶ pairXB where
  app := pairABToXB
  naturality P Q f := by
    apply MorphismProperty.Arrow.Hom.ext
    · change f.mapB ≫ 𝟙 Q.B = 𝟙 P.B ≫ f.mapB
      simp
    · change f.mapA ≫ Q.mapAX = P.mapAX ≫ f.mapX
      exact f.wAX

/-- The canonical maps `(X, B) → (X, A)` are natural in the triple. -/
def pairXBToXANatTrans : pairXB ⟶ pairXA where
  app := pairXBToXA
  naturality P Q f := by
    apply MorphismProperty.Arrow.Hom.ext
    · change f.mapB ≫ Q.mapBA = P.mapBA ≫ f.mapA
      exact f.wBA
    · change f.mapX ≫ 𝟙 Q.X = 𝟙 P.X ≫ f.mapX
      simp

end TopTriple

section TripleChains

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- The canonical map `C_*(A,B;R) ⟶ C_*(X,B;R)` for a topological triple. -/
noncomputable def tripleChainComplexMapABToXB (T : TopTriple.{w}) (R : C) :
    (chainComplexFunctor R).obj (TopTriple.pairAB.obj T) ⟶
      (chainComplexFunctor R).obj (TopTriple.pairXB.obj T) :=
  (chainComplexFunctor R).map (TopTriple.pairABToXB T)

/-- The canonical map `C_*(X,B;R) ⟶ C_*(X,A;R)` for a topological triple. -/
noncomputable def tripleChainComplexMapXBToXA (T : TopTriple.{w}) (R : C) :
    (chainComplexFunctor R).obj (TopTriple.pairXB.obj T) ⟶
      (chainComplexFunctor R).obj (TopTriple.pairXA.obj T) :=
  (chainComplexFunctor R).map (TopTriple.pairXBToXA T)

set_option backward.isDefEq.respectTransparency false in
/-- The two canonical relative-chain maps of a topological triple compose to zero. -/
@[reassoc (attr := simp)]
lemma tripleChainComplexMap_comp (T : TopTriple.{w}) (R : C) :
    tripleChainComplexMapABToXB T R ≫ tripleChainComplexMapXBToXA T R = 0 := by
  rw [← cancel_epi ((chainComplexFunctorπ R).app (TopTriple.pairAB.obj T))]
  simp only [tripleChainComplexMapABToXB, tripleChainComplexMapXBToXA]
  rw [← Category.assoc, ← (chainComplexFunctorπ R).naturality
    (TopTriple.pairABToXB T)]
  rw [Category.assoc, ← (chainComplexFunctorπ R).naturality
    (TopTriple.pairXBToXA T)]
  have hAB :
      (TopPair.proj₁ ⋙ (singularChainComplexFunctor C).obj R).map
          (TopTriple.pairABToXB T) =
        ((singularChainComplexFunctor C).obj R).map T.mapAX := rfl
  have hXA :
      (TopPair.proj₁ ⋙ (singularChainComplexFunctor C).obj R).map
          (TopTriple.pairXBToXA T) = 𝟙 _ := by
    change ((singularChainComplexFunctor C).obj R).map (𝟙 T.X) = 𝟙 _
    exact ((singularChainComplexFunctor C).obj R).map_id T.X
  rw [hAB, hXA, Category.id_comp, comp_zero]
  simpa only [TopTriple.pairXA_obj_map] using
    chainComplexFunctor_condition R (TopTriple.pairXA.obj T)

/-- The canonical three-term chain complex attached to a topological triple. -/
noncomputable def tripleChainComplexShortComplex (T : TopTriple.{w}) (R : C) :
    ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (tripleChainComplexMapABToXB T R)
    (tripleChainComplexMapXBToXA T R) (tripleChainComplexMap_comp T R)

/-- A map of topological triples induces a map of their relative-chain short complexes. -/
noncomputable def tripleChainComplexShortComplexMap {P Q : TopTriple.{w}}
    (f : P ⟶ Q) (R : C) :
    tripleChainComplexShortComplex P R ⟶ tripleChainComplexShortComplex Q R where
  τ₁ := (chainComplexFunctor R).map (TopTriple.pairAB.map f)
  τ₂ := (chainComplexFunctor R).map (TopTriple.pairXB.map f)
  τ₃ := (chainComplexFunctor R).map (TopTriple.pairXA.map f)
  comm₁₂ := by
    simpa only [tripleChainComplexShortComplex, tripleChainComplexMapABToXB,
      TopTriple.pairABToXBNatTrans, Functor.map_comp] using
      congrArg ((chainComplexFunctor R).map)
        (TopTriple.pairABToXBNatTrans.naturality f)
  comm₂₃ := by
    simpa only [tripleChainComplexShortComplex, tripleChainComplexMapXBToXA,
      TopTriple.pairXBToXANatTrans, Functor.map_comp] using
      congrArg ((chainComplexFunctor R).map)
        (TopTriple.pairXBToXANatTrans.naturality f)

/-- Relative chains are canonically the cokernel of the inclusion of the
subspace chains into the ambient chains. -/
private noncomputable def relativeChainCokernelIso (P : TopPair.{w}) (R : C) :
    cokernel (((singularChainComplexFunctor C).obj R).map P.map) ≅
      (chainComplexFunctor R).obj P :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso
    (isColimitCokernelCoforkChainComplex R P)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma relativeChainCokernelIso_hom_fac (P : TopPair.{w}) (R : C) :
    cokernel.π (((singularChainComplexFunctor C).obj R).map P.map) ≫
        (relativeChainCokernelIso P R).hom =
      (chainComplexFunctorπ R).app P := by
  simpa only [relativeChainCokernelIso, cokernelCoforkChainComplex,
    Cofork.ofπ_ι_app] using
    (cokernelIsCokernel
        (((singularChainComplexFunctor C).obj R).map P.map)).comp_coconePointUniqueUpToIso_hom
      (isColimitCokernelCoforkChainComplex R P) WalkingParallelPair.one

set_option backward.isDefEq.respectTransparency false in
/-- **Hatcher, §2.1 (pages 118–119).** For a topological triple
`B ⊆ A ⊆ X`, the canonical sequence of relative singular chain complexes
`0 → C_*(A,B;R) → C_*(X,B;R) → C_*(X,A;R) → 0` is short exact. -/
theorem tripleChainComplexShortComplex_shortExact (T : TopTriple.{w}) (R : C) :
    (tripleChainComplexShortComplex T R).ShortExact := by
  let F := (singularChainComplexFunctor C).obj R
  let f := F.map (TopTriple.pairAB.obj T).map
  let g := F.map (TopTriple.pairXA.obj T).map
  letI : Mono T.mapAX :=
    (TopCat.mono_iff_injective _).2 T.isEmbedding_mapAX.injective
  haveI : Mono g := by
    dsimp [g, F]
    infer_instance
  let hK := kernelCokernelCompSequence_exact f g
  have hδ : (kernelCokernelCompSequence f g).map' 2 3 = 0 := by
    change kernelCokernelCompSequence.δ f g = 0
    rw [kernelCokernelCompSequence.δ_fac, kernel.ι_of_mono]
    simp
  haveI : Mono ((kernelCokernelCompSequence f g).map' 3 4) :=
    (hK.exact 2).mono_g hδ
  haveI : Epi ((kernelCokernelCompSequence f g).map' 4 5) := inferInstance
  let hTail : (hK.sc 3).ShortExact :=
    ShortComplex.ShortExact.mk' (hK.exact 3) inferInstance inferInstance
  let eAB : cokernel f ≅ (chainComplexFunctor R).obj (TopTriple.pairAB.obj T) := by
    exact relativeChainCokernelIso (TopTriple.pairAB.obj T) R
  let hfg : f ≫ g = F.map (TopTriple.pairXB.obj T).map := by
    change F.map T.mapBA ≫ F.map T.mapAX = F.map (T.mapBA ≫ T.mapAX)
    exact (F.map_comp T.mapBA T.mapAX).symm
  let eXB : cokernel (f ≫ g) ≅
      (chainComplexFunctor R).obj (TopTriple.pairXB.obj T) :=
    cokernelIsoOfEq hfg ≪≫
      relativeChainCokernelIso (TopTriple.pairXB.obj T) R
  let eXA : cokernel g ≅ (chainComplexFunctor R).obj (TopTriple.pairXA.obj T) := by
    exact relativeChainCokernelIso (TopTriple.pairXA.obj T) R
  have eAB_fac : cokernel.π f ≫ eAB.hom =
      (chainComplexFunctorπ R).app (TopTriple.pairAB.obj T) := by
    simpa only [eAB, f, F, TopTriple.pairAB_obj_map] using
      relativeChainCokernelIso_hom_fac (TopTriple.pairAB.obj T) R
  have eXB_fac : cokernel.π (f ≫ g) ≫ eXB.hom =
      (chainComplexFunctorπ R).app (TopTriple.pairXB.obj T) := by
    dsimp only [eXB]
    rw [Iso.trans_hom, ← Category.assoc, π_comp_cokernelIsoOfEq_hom,
      relativeChainCokernelIso_hom_fac]
  have eXA_fac : cokernel.π g ≫ eXA.hom =
      (chainComplexFunctorπ R).app (TopTriple.pairXA.obj T) := by
    simpa only [eXA, g, F, TopTriple.pairXA_obj_map] using
      relativeChainCokernelIso_hom_fac (TopTriple.pairXA.obj T) R
  have pairAB_naturality :
      (chainComplexFunctorπ R).app (TopTriple.pairAB.obj T) ≫
          (chainComplexFunctor R).map (TopTriple.pairABToXB T) =
        g ≫ (chainComplexFunctorπ R).app (TopTriple.pairXB.obj T) := by
    rw [← (chainComplexFunctorπ R).naturality (TopTriple.pairABToXB T)]
    rfl
  have pairXA_naturality :
      (chainComplexFunctorπ R).app (TopTriple.pairXB.obj T) ≫
          (chainComplexFunctor R).map (TopTriple.pairXBToXA T) =
        (chainComplexFunctorπ R).app (TopTriple.pairXA.obj T) := by
    rw [← (chainComplexFunctorπ R).naturality (TopTriple.pairXBToXA T)]
    change F.map (𝟙 T.X) ≫
        (chainComplexFunctorπ R).app (TopTriple.pairXA.obj T) = _
    rw [F.map_id, Category.id_comp]
  have tailAB_fac :
      cokernel.π f ≫ cokernel.map f (f ≫ g) (𝟙 _) g (by simp) =
        g ≫ cokernel.π (f ≫ g) := by
    simp
  have tailXA_fac :
      cokernel.π (f ≫ g) ≫ cokernel.map (f ≫ g) g f (𝟙 _) (by simp) =
        cokernel.π g := by
    simp
  let e : hK.sc 3 ≅ tripleChainComplexShortComplex T R :=
    ShortComplex.isoMk eAB eXB eXA
      (by
        change eAB.hom ≫ (chainComplexFunctor R).map (TopTriple.pairABToXB T) =
          cokernel.map f (f ≫ g) (𝟙 _) g (by simp) ≫ eXB.hom
        rw [← cancel_epi (cokernel.π f)]
        rw [← Category.assoc, eAB_fac]
        rw [← Category.assoc, tailAB_fac, Category.assoc, eXB_fac]
        exact pairAB_naturality)
      (by
        change eXB.hom ≫ (chainComplexFunctor R).map (TopTriple.pairXBToXA T) =
          cokernel.map (f ≫ g) g f (𝟙 _) (by simp) ≫ eXA.hom
        rw [← cancel_epi (cokernel.π (f ≫ g))]
        rw [← Category.assoc, eXB_fac]
        rw [← Category.assoc, tailXA_fac, eXA_fac]
        exact pairXA_naturality)
  exact ShortComplex.shortExact_of_iso e hTail

/-- The connecting morphism
`H_n(X,A;R) ⟶ H_m(A,B;R)` for adjacent degrees in the homology sequence
of a topological triple. -/
noncomputable def tripleConnecting
    (T : TopTriple.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    (homologyFunctor R n).obj (TopTriple.pairXA.obj T) ⟶
      (homologyFunctor R m).obj (TopTriple.pairAB.obj T) :=
  (tripleChainComplexShortComplex_shortExact T R).δ n m (by simpa)

/-- Six consecutive terms in the long exact relative-homology sequence of a
topological triple. -/
noncomputable def tripleSequence
    (T : TopTriple.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    ComposableArrows C 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    (tripleChainComplexShortComplex_shortExact T R)
    n m (by simpa)

/-- **Hatcher, §2.1 (pages 118–119).** Six consecutive terms in the
relative-homology sequence of a topological triple are exact. -/
theorem tripleSequence_exact
    (T : TopTriple.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    (tripleSequence T R n m h).Exact := by
  exact HomologicalComplex.HomologySequence.composableArrows₅_exact
    (tripleChainComplexShortComplex_shortExact T R)
    n m (by simpa)

set_option backward.isDefEq.respectTransparency false in
/-- The terminal degree-zero map
`H₀(X,B;R) ⟶ H₀(X,A;R)` in the homology sequence of a topological
triple is an epimorphism. -/
theorem tripleHomologyMapXBToXA_zero_epi (T : TopTriple.{w}) (R : C) :
    Epi ((homologyFunctor R 0).map (TopTriple.pairXBToXA T)) := by
  haveI : Epi (tripleChainComplexMapXBToXA T R) :=
    (tripleChainComplexShortComplex_shortExact T R).epi_g
  change Epi (HomologicalComplex.homologyMap
    (tripleChainComplexMapXBToXA T R) 0)
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)

end TripleChains

end Hatcher.Relative
