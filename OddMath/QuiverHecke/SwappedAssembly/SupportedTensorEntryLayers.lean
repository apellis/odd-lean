import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorEntryPullback

/-! # Whole-Hom layer transport for the original tensor row

SwappedVacuumCoordinates §§5–7: the literal supported matrix layer
becomes chronological postcomposition on the canonical original-weight
row. Its global and local target charts are related by their prescribed
change-of-chart isomorphisms; no generator-comparison premise is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
namespace TensorEntryPullback
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (E : C ≌ D) {X Y : D} {A B A' B' : C}

/-- The whole original-Hom arrow prescribed by two actual target charts. -/
def arrow (e : X ≅ E.functor.obj A) (d : Y ≅ E.functor.obj B) (m : X ⟶ Y) : A ⟶ B :=
  E.functor.preimage (e.inv ≫ m ≫ d.hom)

/-- The prescribed pulled-back arrow has its literal target-chart square. -/
theorem arrow_square (e : X ≅ E.functor.obj A) (d : Y ≅ E.functor.obj B) (m : X ⟶ Y) :
    m ≫ d.hom = e.hom ≫ E.functor.map (arrow E e d m) := by
  simp only [arrow, Functor.map_preimage, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The original row intertwines every literal whole-Hom map. -/
theorem map_arrow {Z : D} (e : X ≅ E.functor.obj A) (d : Y ≅ E.functor.obj B)
    (f : Z ⟶ X) (m : X ⟶ Y) :
    map E d (f ≫ m) = map E e f ≫ arrow E e d m :=
  map_square E e d f m _ (arrow_square E e d m)

/-- Change only the displayed original-Hom target chart. -/
def chartChange (e : X ≅ E.functor.obj A) (d : X ≅ E.functor.obj A') : A ≅ A' :=
  E.functor.preimageIso (e.symm ≪≫ d)

/-- The global and local pulled-back arrows are canonically conjugate. -/
theorem arrow_chartChange (e : X ≅ E.functor.obj A) (d : Y ≅ E.functor.obj B)
    (e' : X ≅ E.functor.obj A') (d' : Y ≅ E.functor.obj B') (m : X ⟶ Y) :
    arrow E e d m ≫ (chartChange E d d').hom =
      (chartChange E e e').hom ≫ arrow E e' d' m := by
  apply E.functor.map_injective
  simp only [arrow, chartChange, Functor.map_comp, Functor.preimageIso_hom,
    Functor.map_preimage, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]

end TensorEntryPullback

universe u
local instance tensorEntryLayersHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "cS" => tensorSourceContent D ΛP ΛR s
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "E" => tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cS)
local notation "Q" => interpretation D Sc m cutoff N ΛP ΛR hP hR
  (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L)

/-- The literal layer pulled back through the canonical global path charts. -/
def tensorOriginalWordLayer (gens : (P).Generators) (A : Layer (SKM.sig D))
    (p : SPath A.dom.word (0,cS) (0,0)) (q : SPath A.cod.word (0,cS) (0,0))
    (hp : ∀ c ∈ A.dom.word, c.l.1 = true) (hq : ∀ c ∈ A.cod.word, c.l.1 = true) :
    TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p hp ⟶
      TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR q hq :=
  TensorEntryPullback.arrow (E)
    (tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s p hp)
    (tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s q hq)
    ((P).compLayer gens A p q (tensorVacuum D Sc m cutoff L ΛP ΛR).obj)

/-- Every actual native matrix layer becomes postcomposition on the
canonical original-weight whole-Hom row, without a comparison hypothesis. -/
theorem tensorOriginalWordEntry_layer (gens : (P).Generators)
    (A : Layer (SKM.sig D)) (hA : A.Valid)
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) +
      (-ΛR + contentWeight D (0 : I →₀ ℕ)) = A.cod.endR)
    (p : SPath A.dom.word (0,cS) (0,0)) (q : SPath A.cod.word (0,cS) (0,0))
    (hp : ∀ c ∈ A.dom.word, c.l.1 = true) (hq : ∀ c ∈ A.cod.word, c.l.1 = true)
    (x : matrixModule D Sc m cutoff N ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s)
      (tensorTargetFamily D Sc m cutoff ΛP ΛR L) A.dom) :
    tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s hEnd q hq
      (((Q gens).res A.cod) ((Q gens).op A ((Q gens).ext A.dom x))) =
    tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s (hEnd.trans hA.endR_eq) p hp x ≫
      tensorOriginalWordLayer D Sc m cutoff ΛP ΛR L hP hR s gens A p q hp hq := by
  change TensorEntryPullback.map (E)
    (tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s q hq)
    (tensorVacuumRowProjection D Sc m cutoff ΛP ΛR L hP hR s hEnd q
      (((Q gens).res A.cod) ((Q gens).op A ((Q gens).ext A.dom x)))) = _
  rw [tensorVacuumRowProjection_layer D Sc m cutoff ΛP ΛR L hP hR s gens A hA hEnd p q hp x]
  exact TensorEntryPullback.map_arrow (E) _ _ _ _

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
