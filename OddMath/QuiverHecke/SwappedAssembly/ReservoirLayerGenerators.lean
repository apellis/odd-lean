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

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
