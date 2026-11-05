/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Braid
import OddMath.QuiverHecke.CyclotomicAction.SuperCrossing

/-!
# The square-zero relation on cyclotomic composition corners

Ports the same-colour quadratic input of
`Categorification/KLR/CyclotomicAction/Square.lean` to the concrete super
cyclotomic quotient. The signed right multiplier, rather than ordinary right
multiplication, is used on the composition superbimodule. Thus the conclusion
also holds for an odd colour. Mixed-colour polynomial transport is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- Positioned-word coordinates for the concrete last-pair crossing. -/
theorem inductionLastCrossing_eq_cl (i j : I) {n : ℕ} (w : Word I n) :
    inductionLastCrossing D Sc i j w =
      cl D Sc _ _ [.cross w.1.length] (by
        simp [appendWord, pl, PG.ld, Shape.dom, Shape.cod, List.append_assoc]) := by
  unfold inductionLastCrossing inductionStrandCrossing cl
  simp only [Presentation.associator_eq, eqToIso]
  dsimp only [wordObj]
  erw [Presentation.diag_whiskerLeft]
  rw [← (pres D Sc).diag_cast _ (Obj.tensor_assoc (ob D w.1) (ob D [i]) (ob D [j])).symm
    (Obj.tensor_assoc (ob D w.1) (ob D [j]) (ob D [i])).symm]
  apply Presentation.diag_eq_of_layers_eq
  simp [appendWord, pl, PG.ld, layList, lay, ob, List.append_assoc, Layer.wl]

/-- Two equal-colour last crossings compose to zero on each word. -/
theorem inductionLastCrossing_square (i : I) {n : ℕ} (w : Word I n) :
    inductionLastCrossing D Sc i i w ≫ inductionLastCrossing D Sc i i w = 0 := by
  rw [inductionLastCrossing_eq_cl, cl_comp]
  have aux {t : List I} (ht : t = w.1 ++ [i, i] ++ [])
      (h : SChain t (pl t [.cross w.1.length, .cross w.1.length]) t) :
      cl D Sc t t [.cross w.1.length, .cross w.1.length] h = 0 := by
    subst t
    exact cross_cross_eq D Sc w.1 [] i h
  exact aux (by simp [appendWord, List.append_assoc]) _

variable [Fintype I]

/-- Square-zero in the actual affine finite-matrix algebra. -/
theorem affineLastCrossing_square (i : I) (n : ℕ) :
    affineLastCrossing D Sc i i n * affineLastCrossing D Sc i i n = 0 := by
  unfold affineLastCrossing
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro w _
  rw [Finset.sum_mul, Finset.sum_eq_single w]
  · rw [FiniteHomMatrix.single_mul_single, inductionLastCrossing_square]
    exact FiniteHomMatrix.single_zero _ _
  · intro b _ hb
    apply FiniteHomMatrix.single_mul_single_of_ne
    intro h
    exact hb (appendWord_injective i n (appendWord_injective i (n + 1) h))
  · simp

/-- Square-zero descends through the actual two-sided cyclotomic ideal. -/
theorem cyclotomicLastCrossing_square (i : I) (a : I → _root_.Polynomial k) (n : ℕ) :
    cyclotomicLastCrossing D Sc i i a n * cyclotomicLastCrossing D Sc i i a n = 0 := by
  rw [cyclotomicLastCrossing, ← map_mul, affineLastCrossing_square, map_zero]

variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => compositionCorner D Sc i i a ha n
local notation "f" => compositionSuperCrossing D Sc i i a ha n

end OddMath.QuiverHecke
