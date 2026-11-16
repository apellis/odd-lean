import OddMath.QuiverHecke.SwappedAssembly.Generators.Cross
import OddMath.SKM.RouquierHomContentCoherence

/-! # The reservoir crossing at probe content zero

SwappedVacuumCoordinates §§2–6: remove the zero probe-content shifts
from the prescribed distinct-colour reservoir crossing, including its
target-sector transport, on the entire Hom object.
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

/-- The zero-shift pair chart uses only the zero-content equality and
the given postcomposition associator. -/
def reservoirVacuumPairIso (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i j : I) (muP : X) {a b d : X} (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
    (Z : homWeightSector T W.obj muP a) :
    (homContentPostE T W i 0 muP h₂).obj ((homContentPostE T W j 0 muP h₁).obj Z) ≅
      Z ≫ W.E j h₁ ≫ W.E i h₂ :=
  eqToIso (by
    simp only [homContentPostE, Functor.comp_obj, homContentShift, map_zero,
      mul_zero, homParityShift_zero, Functor.id_obj]
    rfl) ≪≫ associator Z (W.E j h₁) (W.E i h₂)

namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
private theorem cross_edge (i j : I) (c : I →₀ ℕ)
    (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c))) :
    P.muM (nextSector (true,j) false (nextSector (true,i) false (0,c))) + D.α i =
      P.muM (nextSector (true,j) false (0,c)) := by
  rw [hs]
  exact P.muM_postE i hw₂

private def crossingSource (i j : I) (c : I →₀ ℕ)
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c)))
    (Z : P.H (nextSector (true,i) false (nextSector (true,j) false (0,c)))) :
    P.H (nextSector (true,j) false (nextSector (true,i) false (0,c))) := hs ▸ Z

/-- The target chart reverses precisely the target-sector transport
already present in `postCrossNe`, before removing its zero shifts. -/
def reservoirVacuumCrossTargetIso (i j : I) (c : I →₀ ℕ)
    (hw₁ : StepValid (true,j) false (0,c))
    (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c)))
    (Z : P.H (nextSector (true,i) false (nextSector (true,j) false (0,c)))) :
    (P.step (true,j) false (0,c) hw₁).obj ((P.step (true,i) false _ hw₂).obj Z) ≅
      (crossingSource P i j c hs Z) ≫
        P.W.E i (cross_edge P i j c hw₂ hs) ≫ P.W.E j (P.muM_postE j hw₁) :=
  (P.step (true,j) false (0,c) hw₁).mapIso
    (eqToIso (eq_of_heq (P.postE_obj_heq i 0 hs (cross_edge P i j c hw₂ hs)
      (P.muM_postE i hw₂) Z))).symm ≪≫
    reservoirVacuumPairIso P.T.obj P.W j i (P.muP (0,c))
      (cross_edge P i j c hw₂ hs) (P.muM_postE j hw₁) (crossingSource P i j c hs Z)

/-- The actual distinct-colour reservoir block, in its two canonical
zero-shift charts, is the original factor crossing on every Hom map. -/
theorem postCrossNe_reservoirVacuum (i j : I) (c : I →₀ ℕ)
    (hv₁ : StepValid (true,i) false (0,c))
    (hv₂ : StepValid (true,j) false (nextSector (true,i) false (0,c)))
    (hw₁ : StepValid (true,j) false (0,c))
    (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c)))
    (Z : P.H (nextSector (true,i) false (nextSector (true,j) false (0,c)))) :
    P.postCrossNe i j (0,c) hv₁ hv₂ hw₁ hw₂ hs Z ≫
        (P.reservoirVacuumCrossTargetIso i j c hw₁ hw₂ hs Z).hom =
      (reservoirVacuumPairIso P.T.obj P.W i j (P.muP (0,c))
        (P.muM_postE j hv₂) (P.muM_postE i hv₁) (crossingSource P i j c hs Z)).hom ≫
        (crossingSource P i j c hs Z) ◁
          P.W.cross i j (P.muM_postE j hv₂) (P.muM_postE i hv₁)
            (cross_edge P i j c hw₂ hs) (P.muM_postE j hw₁) := by
  simp [postCrossNe, reservoirVacuumCrossTargetIso, reservoirVacuumPairIso,
    postPairIso, crossingSource, homContentShift, homParityShiftAdd, homParityShiftCommute, homParityShift,
    Category.assoc]
  let Z₀ := crossingSource P i j c hs Z
  let E₁ := P.W.E j (P.muM_postE j hv₂)
  let E₂ := P.W.E i (P.muM_postE i hv₁)
  let F₁ := P.W.E i (cross_edge P i j c hw₂ hs)
  let F₂ := P.W.E j (P.muM_postE j hw₁)
  let f : (Z₀ ≫ E₁) ≫ E₂ ⟶ Z₀ ≫ E₁ ≫ E₂ := (associator Z₀ E₁ E₂).hom
  let g : Z₀ ≫ E₁ ≫ E₂ ⟶ Z₀ ≫ F₁ ≫ F₂ :=
    Z₀ ◁ P.W.cross i j (P.muM_postE j hv₂) (P.muM_postE i hv₁)
      (cross_edge P i j c hw₂ hs) (P.muM_postE j hw₁)
  change 𝟙 _ ≫ 𝟙 _ ≫ f ≫ g = f ≫ g
  simp only [Category.id_comp]

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
