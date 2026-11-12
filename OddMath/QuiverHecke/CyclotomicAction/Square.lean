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

variable [Fintype I]

variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => compositionCorner D Sc i i a ha n
local notation "f" => compositionSuperCrossing D Sc i i a ha n

end OddMath.QuiverHecke
