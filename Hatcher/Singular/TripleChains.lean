import Hatcher.Singular.Relative

/-!
# Topological triples

This file packages a nested triple of spaces `B ↪ A ↪ X`, its morphisms, and the
three associated topological pairs.  The chain-level short exact sequence of a triple
is developed separately from this thin topological interface.
-/

noncomputable section

open CategoryTheory

namespace Hatcher.Relative

universe w

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

end Hatcher.Relative
