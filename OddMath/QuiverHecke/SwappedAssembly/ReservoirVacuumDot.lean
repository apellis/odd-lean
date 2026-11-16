import OddMath.QuiverHecke.SwappedAssembly.Generators.Dot
import OddMath.SKM.RouquierHomContentCoherence

/-! # The reservoir dot at probe content zero

SwappedActionAssembly §6 and SwappedVacuumCoordinates §§2–4: remove the
vanishing probe-content shift from the actual reservoir entry of the
swapped dot. The comparison retains the given factor dot and acts on the
whole Hom object, including odd maps and every input vector.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

/-- The canonical equality chart removes precisely the zero probe-content
shift from raising postcomposition. -/
def reservoirVacuumPostIso (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM)
    (Z : homWeightSector T W.obj muP muM) :
    (homContentPostE T W i 0 muP h).obj Z ≅ Z ≫ W.E i h :=
  eqToIso (by
    simp only [homContentPostE, Functor.comp_obj, homContentShift, map_zero,
      mul_zero, homParityShift_zero, Functor.id_obj]
    rfl)

/-- In the zero-shift chart, the prescribed postcomposition dot is the
literal factor dot whiskered by the given Hom object. -/
theorem reservoirVacuumPostDot (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM)
    (Z : homWeightSector T W.obj muP muM) :
    homContentPostDot T W i 0 muP h Z ≫ (reservoirVacuumPostIso T W i muP h Z).hom =
      (reservoirVacuumPostIso T W i muP h Z).hom ≫ Z ◁ W.dot i h := by
  simp [reservoirVacuumPostIso, homContentPostDot, homContentPostE,
    homContentShift, homParityShift, homPost]

namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The weight certificate of the occupied reservoir strand at probe
content zero. -/
theorem reservoirVacuumEdge (i : I) (c : I →₀ ℕ)
    (hv : StepValid (true, i) false (0, c)) :
    P.muM (nextSector (true, i) false (0, c)) + D.α i = P.muM (0, c) := by
  simp only [muM, nextSector]
  rw [add_assoc, contentWeight_sub_single hv]

/-- The actual occupied entry of the swapped dot, transported through
its zero-shift endpoint chart, is the original reservoir dot. -/
theorem dotImage_reservoirVacuum (i : I) (ν : X) (c : I →₀ ℕ)
    (hv hv' : StepValid (true, i) false (0, c))
    (Z : P.H (nextSector (true, i) false (0, c))) :
    P.dotImage i ν (.cons _ false (0, c) hv (.nil _))
        (.cons _ false (0, c) hv' (.nil _)) Z ≫
        (reservoirVacuumPostIso P.T.obj P.W i (P.muP (0, c))
          (P.reservoirVacuumEdge i c hv) Z).hom =
      (reservoirVacuumPostIso P.T.obj P.W i (P.muP (0, c))
        (P.reservoirVacuumEdge i c hv) Z).hom ≫
          Z ◁ P.W.dot i (P.reservoirVacuumEdge i c hv) := by
  rw [P.dotImage_reservoir]
  exact reservoirVacuumPostDot P.T.obj P.W i (P.muP (0, c)) _ Z

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
