/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalSlideAlgebra

/-!
# The distinct-colour dot–crossing relations of the last pair of strands

The algebra half of the distinct-colour slides (1.8) of Brundan–Ellis, arXiv:1701.04133v2,
Definition 1.5. For distinct colours `i ≠ j` the quiver Hecke supercategory has, with
`ε = (-1)^{|i||j|}` and diagrams read bottom to top,

  `x_i τ = ε τ x_i`,  `τ x_j = ε x_j τ`,

the dot staying on the strand of its colour (`slide_left_ne`, `slide_right_ne`). Whiskering by
an old word gives the corresponding identities between the last-pair crossing, the appended
dot and the new last dot (`induction_slide_left_ne`, `induction_slide_right_ne`). Since matrix
multiplication reverses diagram composition, in the affine algebra and at every height of the
extended tower they read

  `c φⱼ(y_i) = ε y_i c`,  `φᵢ(y_j) c = ε c y_j`

with `c` the last-pair crossing of `heightLastCrossing D Sc a i j n`, `y` the new last dot and
`φ` the append map (`heightLastCrossing_slide_left_ne`, `heightLastCrossing_slide_right_ne`).
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
namespace OddMath.QuiverHecke
open SKM (zsign)
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

section Local
variable (i j : I)

variable {i j}

end Local

section Word
variable {i j : I}

end Word

section Affine
variable [Fintype I] {i j : I}

private theorem affineLastDot_mul_single (c : I) {m : ℕ} (t : Word I m)
    (s : Word I (m + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc (appendWord c t)) :
    affineLastDot D Sc c m * FiniteHomMatrix.single (appendWord c t) s f =
      FiniteHomMatrix.single (appendWord c t) s (f ≫ inductionLastDot D Sc c t) := by
  rw [affineLastDot, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective c m h)) _ _
  · simp

private theorem single_mul_affineLastCrossing {n : ℕ} (s : Word I n)
    (r : Word I (n + 1 + 1))
    (f : wordObj D Sc (appendWord i (appendWord j s)) ⟶ wordObj D Sc r) :
    FiniteHomMatrix.single r (appendWord i (appendWord j s)) f * affineLastCrossing D Sc i j n =
    FiniteHomMatrix.single r (appendWord j (appendWord i s))
      (inductionLastCrossing D Sc i j s ≫ f) := by
  rw [affineLastCrossing, Finset.mul_sum, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective j n (appendWord_injective i (n + 1) h.symm))) _ _
  · simp

end Affine

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.CyclotomicAction
open SKM (zsign)
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] (a : I → _root_.Polynomial k) {i j : I}

end OddMath.QuiverHecke.CyclotomicAction
