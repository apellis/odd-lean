import OddMath.QuiverHecke.SwappedAssembly.ReservoirLayerEntries
import OddMath.QuiverHecke.SwappedAssembly.ReservoirLayerGenerators
import OddMath.QuiverHecke.SwappedAssembly.Generators.Leftward

/-! # Equal-colour factor crossings in reservoir layer matrices

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

/-- The prescribed two-letter reservoir chart in both path contexts.
The factor crossing, including its parity, remains unchanged. -/
def reservoirLayerSameCrossIso (ν : X) (u v : List (Letter I)) (i : I)
    {sl : Sector I} {c d : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
    (hw : StepValid (true,i) false (nextSector (true,i) false (0,c)))
    (pu : SPath (SKM.lay D ν u (.cross i i) v).left sl (0,c))
    (pv : SPath (SKM.lay D ν u (.cross i i) v).right
      (nextSector (true,i) false (nextSector (true,i) false (0,c))) (0,d))
    (Z : P.H (0,d)) :
    (P.pathFunctor ((pu.append
      (.cons ⟨(true,i), SKM.wt D (SKM.wt D ν v) [up i]⟩ false (0,c) hv
        (.cons ⟨(true,i), SKM.wt D ν v⟩ false _ hw (.nil _)))).append pv)).obj Z ≅
      (P.pathFunctor pu).obj ((P.pathFunctor pv).obj Z ≫
        P.W.E i (P.muM_postE i hw) ≫ P.W.E i (P.muM_postE i hv)) :=
  eqToIso (P.pathFunctor_append_append_obj pu
    (.cons ⟨(true,i), SKM.wt D (SKM.wt D ν v) [up i]⟩ false (0,c) hv
      (.cons ⟨(true,i), SKM.wt D ν v⟩ false _ hw (.nil _))) pv Z) ≪≫
    (P.pathFunctor pu).mapIso ((homContentPostWordIso P.T.obj P.W i 0 (P.muP (0,c))
      (P.muM_postE i hw) (P.muM_postE i hv)).app ((P.pathFunctor pv).obj Z))

/-- The actual reservoir block of the equal-colour crossing matrix,
with two arbitrary path contexts and an arbitrary input matrix, is the
original factor crossing in the prescribed word chart. -/
theorem layerMap_reservoir_cross_same (a : P.CrossCoeff) {Gs Ys : ∀ s, P.H s}
    (ν : X) (u v : List (Letter I)) (i : I)
    (hr : ∀ l ∈ (SKM.lay D ν u (.cross i i) v).right, l.l.1 = true)
    (x : P.Mod Gs Ys (SKM.lay D ν u (.cross i i) v).dom)
    {sl : Sector I} {c d : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
    (hw : StepValid (true,i) false (nextSector (true,i) false (0,c)))
    (pu : SPath (SKM.lay D ν u (.cross i i) v).left sl (0,c))
    (pv : SPath (SKM.lay D ν u (.cross i i) v).right
      (nextSector (true,i) false (nextSector (true,i) false (0,c))) (0,d))
    (hq : P.wt (0,d) = (SKM.lay D ν u (.cross i i) v).cod.endR) :
    P.layerMap (P.upwardGens a) (SKM.lay D ν u (.cross i i) v) x sl ⟨(0,d),hq⟩
        ((pu.append (.cons ⟨(true,i), SKM.wt D (SKM.wt D ν v) [up i]⟩ false (0,c) hv
          (.cons ⟨(true,i), SKM.wt D ν v⟩ false _ hw (.nil _)))).append pv) ≫
        (P.reservoirLayerSameCrossIso ν u v i hv hw pu pv (Ys (0,d))).hom =
      x sl ⟨(0,d),hq.trans (SKM.lay_valid D ν u (.cross i i) v).endR_eq⟩
        ((pu.append (.cons ⟨(true,i), SKM.wt D (SKM.wt D ν v) [up i]⟩ false (0,c) hv
          (.cons ⟨(true,i), SKM.wt D ν v⟩ false _ hw (.nil _)))).append pv) ≫
        (P.reservoirLayerSameCrossIso ν u v i hv hw pu pv (Ys (0,d))).hom ≫
        (P.pathFunctor pu).map (((P.pathFunctor pv).obj (Ys (0,d))) ◁
          P.W.cross i i (P.muM_postE i hw) (P.muM_postE i hv)
            (P.muM_postE i hw) (P.muM_postE i hv)) := by
  let pg := SPath.cons ⟨(true,i), SKM.wt D (SKM.wt D ν v) [up i]⟩ false (0,c) hv
    (.cons ⟨(true,i), SKM.wt D ν v⟩ false _ hw (.nil _))
  rw [P.layerMap_reservoir_append (P.upwardGens a) _ (SKM.lay_valid D ν u (.cross i i) v)
    (by change ∀ l ∈ ([⟨(true,i),_⟩,⟨(true,i),_⟩] : List (Col I X)), l.l.1 = true; simp)
    hr x pu pg pg pv hq rfl]
  have hc : P.crossImage a i i (SKM.wt D ν v) pg pg ((P.pathFunctor pv).obj (Ys (0,d))) =
      homContentPostCrossingApp P.T.obj P.W i 0 (P.muP (0,c))
        (P.muM_postE i hw) (P.muM_postE i hv) ((P.pathFunctor pv).obj (Ys (0,d))) := by
    rw [crossImage]
    split_ifs with hii
    · rfl
    · exact False.elim (hii rfl)
  let e := (homContentPostWordIso P.T.obj P.W i 0 (P.muP (0,c))
    (P.muM_postE i hw) (P.muM_postE i hv)).app ((P.pathFunctor pv).obj (Ys (0,d)))
  let g := ((P.pathFunctor pv).obj (Ys (0,d))) ◁
    P.W.cross i i (P.muM_postE i hw) (P.muM_postE i hv) (P.muM_postE i hw) (P.muM_postE i hv)
  have hs : P.crossImage a i i (SKM.wt D ν v) pg pg ((P.pathFunctor pv).obj (Ys (0,d))) ≫ e.hom =
      e.hom ≫ g := by
    rw [hc]
    change (e.hom ≫ g ≫ e.inv) ≫ e.hom = e.hom ≫ g
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact mapped_conjugate (P.pathFunctor pu) (P.pathFunctor_append_append_obj pu pg pv (Ys (0,d)))
    e _ g hs _


end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
