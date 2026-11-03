import OddMath.QuiverHecke.SwappedAssembly.ReservoirLayerEntries
import OddMath.QuiverHecke.SwappedAssembly.ReservoirVacuumDot
import OddMath.QuiverHecke.SwappedAssembly.Generators.Leftward

/-! # Factor generators in reservoir layer matrices

SwappedVacuumCoordinates §§2–6: identify the literal surviving matrix
entry with its prescribed factor generator, retaining both path contexts
and their append transports. The statement concerns entire Hom maps.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
private theorem mapped_conjugate {A C : Type*} [Category* A] [Category* C]
    (F : A ⥤ C) {M N : A} {X G : C} (hX : X = F.obj M) (e : M ≅ N)
    (a : M ⟶ M) (b : N ⟶ N) (h : a ≫ e.hom = e.hom ≫ b) (x : G ⟶ X) :
    (x ≫ eqToHom hX ≫ F.map a ≫ eqToHom hX.symm) ≫
        (eqToHom hX ≫ F.map e.hom) =
      x ≫ (eqToHom hX ≫ F.map e.hom) ≫ F.map b := by
  subst X
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [Category.assoc, ← F.map_comp, h, F.map_comp]

namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

/-- Remove the zero-content shift from the middle strand of a contextual
reservoir dot, leaving both actual outer path functors in place. -/
def reservoirLayerDotIso (ν : X) (u v : List (Letter I)) (i : I)
    {sl : Sector I} {c d : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
    (pu : SPath (SKM.lay D ν u (.dot i) v).left sl (0,c))
    (pv : SPath (SKM.lay D ν u (.dot i) v).right (nextSector (true,i) false (0,c)) (0,d))
    (Z : P.H (0,d)) :
    (P.pathFunctor ((pu.append (.cons ⟨(true,i), SKM.wt D ν v⟩ false (0,c) hv (.nil _))).append pv)).obj Z ≅
      (P.pathFunctor pu).obj ((P.pathFunctor pv).obj Z ≫
        P.W.E i (P.reservoirVacuumEdge i c hv)) :=
  eqToIso (P.pathFunctor_append_append_obj pu (.cons ⟨(true,i), SKM.wt D ν v⟩ false (0,c) hv (.nil _)) pv Z) ≪≫
    (P.pathFunctor pu).mapIso (reservoirVacuumPostIso P.T.obj P.W i (P.muP (0,c))
      (P.reservoirVacuumEdge i c hv) ((P.pathFunctor pv).obj Z))

/-- The prescribed dot in the literal reservoir layer matrix becomes the
given factor dot through the canonical middle-strand chart. The input
matrix is arbitrary, and neither outer context is restricted. -/
theorem layerMap_reservoir_dot (a : P.CrossCoeff) {Gs Ys : ∀ s, P.H s}
    (ν : X) (u v : List (Letter I)) (i : I)
    (hr : ∀ l ∈ (SKM.lay D ν u (.dot i) v).right, l.l.1 = true)
    (x : P.Mod Gs Ys (SKM.lay D ν u (.dot i) v).dom)
    {sl : Sector I} {c d : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
    (pu : SPath (SKM.lay D ν u (.dot i) v).left sl (0,c))
    (pv : SPath (SKM.lay D ν u (.dot i) v).right (nextSector (true,i) false (0,c)) (0,d))
    (hq : P.wt (0,d) = (SKM.lay D ν u (.dot i) v).cod.endR) :
    P.layerMap (P.upwardGens a) (SKM.lay D ν u (.dot i) v) x sl ⟨(0,d),hq⟩
        ((pu.append (.cons ⟨(true,i), SKM.wt D ν v⟩ false (0,c) hv (.nil _))).append pv) ≫
        (P.reservoirLayerDotIso ν u v i hv pu pv (Ys (0,d))).hom =
      x sl ⟨(0,d),hq.trans (SKM.lay_valid D ν u (.dot i) v).endR_eq⟩
        ((pu.append (.cons ⟨(true,i), SKM.wt D ν v⟩ false (0,c) hv (.nil _))).append pv) ≫
        (P.reservoirLayerDotIso ν u v i hv pu pv (Ys (0,d))).hom ≫
        (P.pathFunctor pu).map (((P.pathFunctor pv).obj (Ys (0,d))) ◁
          P.W.dot i (P.reservoirVacuumEdge i c hv)) := by
  rw [P.layerMap_reservoir_append (P.upwardGens a) _ (SKM.lay_valid D ν u (.dot i) v)
    (by change ∀ l ∈ ([⟨(true,i), SKM.wt D ν v⟩] : List (Col I X)), l.l.1 = true; simp) hr x pu
    (.cons ⟨(true,i), SKM.wt D ν v⟩ false (0,c) hv (.nil _)) (.cons ⟨(true,i), SKM.wt D ν v⟩ false (0,c) hv (.nil _)) pv hq rfl]
  exact mapped_conjugate (P.pathFunctor pu)
    (P.pathFunctor_append_append_obj pu (.cons ⟨(true,i), SKM.wt D ν v⟩ false (0,c) hv (.nil _)) pv (Ys (0,d)))
    (reservoirVacuumPostIso P.T.obj P.W i (P.muP (0,c))
      (P.reservoirVacuumEdge i c hv) ((P.pathFunctor pv).obj (Ys (0,d))))
    (P.dotImage i _ (.cons ⟨(true,i), SKM.wt D ν v⟩ false (0,c) hv (.nil _))
      (.cons ⟨(true,i), SKM.wt D ν v⟩ false (0,c) hv (.nil _)) ((P.pathFunctor pv).obj (Ys (0,d))))
    (((P.pathFunctor pv).obj (Ys (0,d))) ◁ P.W.dot i (P.reservoirVacuumEdge i c hv))
    (P.dotImage_reservoirVacuum i _ c hv hv ((P.pathFunctor pv).obj (Ys (0,d)))) _


end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
