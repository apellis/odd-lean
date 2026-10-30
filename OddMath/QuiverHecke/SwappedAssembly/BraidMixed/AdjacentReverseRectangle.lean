/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseCoefficient
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentSplitBraid

/-! # Reverse adjacent split comparison rectangle

The comparison entry follows from the actual homogeneous probe-pair
interchange triangle, with no Q cancellation or crossing inverse.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hR : StepValid (true, i) false s)
  (hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
    nextSector (true, j) true (nextSector (true, i) true s))
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

/-- The reverse probe crossing with its reservoir spectator and terminal cast. -/
def adjacentReverseProbeCross :=
  eqToHom (congrArg (fun Y => (P.step (true, j) true s trivial).obj
    ((P.step (true, i) true _ trivial).obj Y))
    (P.reservoirDot_cast i hs₀ hR hR Z).1).symm ≫
  P.preCrossNe j i s hs₀ ((P.step (true, i) false
    (nextSector (true, j) true (nextSector (true, i) true s)) hR).obj Z)

/-- The unweighted comparison rectangle for the reverse split matrix. -/
theorem adjacentReverse_J_rectangle :
    (P.step (true, j) true s trivial).map
        (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).hom ≫
      P.adjacentReverseMove i j s hR hs Z =
    P.adjacentReverseProbeCross i j s hR hs₀ Z ≫
      (P.step (true, i) true s trivial).map
        (P.mixedJ j i (nextSector (true, i) true s) hR Z).hom ≫
      (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)).hom := by
  have hp := P.preCrossNe_mixedJ_pair_heq j i i s hR hs₀ hs Z
  have hA := congrArg (fun Y => (P.step (true, j) true s trivial).obj
    ((P.step (true, i) true _ trivial).obj Y))
    (P.reservoirDot_cast i hs₀ hR hR Z).1
  have hp' := eq_of_heq ((sandwich_heq hA.symm rfl _).trans hp)
  simp only [eqToHom_refl, Category.comp_id, ← Category.assoc] at hp'
  simpa only [adjacentReverseProbeCross, adjacentReverseMove, prObj, rpObj,
    castH, step, homContentPreE, homContentPostE, homPre, homPost,
    Functor.comp_obj, Functor.comp_map, Category.assoc] using hp'.symm

/-- All four entries of the reverse adjacent split rectangle, in the actual
library diagonal convention. The comparison and coefficient entries determine
the square and conjugate entries without cancelling crossings. -/
theorem adjacentReverse_splitMatrix (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let J := (P.step (true, j) true s trivial).mapIso
      (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))
    let K := P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)
    let A := (P.step (true, j) true s trivial).map
      (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))
    let B := c.a i s hR ((P.step (true, j) true _ trivial).obj Z)
    let M := P.adjacentReverseMove i j s hR hs Z
    let U := P.adjacentReverseProbeCross i j s hR hs₀ Z ≫
      (P.step (true, i) true s trivial).map
        (P.mixedJ j i (nextSector (true, i) true s) hR Z).hom
    (A ≫ M = M ≫ B) ∧
      (J.hom ≫ M = U ≫ K.hom) ∧
      (-(A ≫ A ≫ J.inv) ≫ U = M ≫ (-(B ≫ B ≫ K.inv))) ∧
      (-(J.hom ≫ A ≫ J.inv) ≫ U = U ≫ (-(K.hom ≫ B ≫ K.inv))) := by
  dsimp only
  have hA := P.adjacentReverseMove_coeff c hc h i j s hR hs Z hij
  have hJ := P.adjacentReverse_J_rectangle i j s hR hs₀ hs Z
  have hJ' := hJ.trans (Category.assoc _ _ _).symm
  refine ⟨hA, hJ', ?_, ?_⟩
  · exact splitMatrix_square _ _ _ _ _ _ hA hJ'
  · exact splitMatrix_conj _ _ _ _ _ _ hA hJ'

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
