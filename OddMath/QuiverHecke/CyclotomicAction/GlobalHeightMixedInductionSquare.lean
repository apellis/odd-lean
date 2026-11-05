/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightMixedCornerSquare

/-!
# The distinct-colour quadratic relation for two inductions

The quadratic relations (1.7) of Brundan–Ellis, arXiv:1701.04133v2, Definition 1.5, for
distinct colours `i ≠ j`, on the height-level induction functors of the extended cyclotomic
tower. The corner identities `heightCompositionCorner_square_ne`,
`heightCompositionCorner_square_zero` are transported through the two-colour comparison
`Ind_j ⋙ Ind_i ≅ T_{ij} ⊗ -` (`heightTwoColourComparisonHom`): conjugation by the comparison
(`heightTwoColourConj`) is linear and multiplicative, sends the corner multiplications by the
dots to the outer and inner dots of the induction functors, and so sends `endoPower` of a
corner map to `endoPower` of its image.

* `heightInduction_square_ne`: for `d_{ij} ≠ 0`, the composite of the crossings
  `ψ_{ij} ψ_{ji}` (components) is
  `t'_{ij} x_out^{d_{ij}} + t'_{ji} x_in^{d_{ji}} + ∑ s'^{pq}_{ij} x_in^q x_out^p`;
* `heightInduction_square_zero`: for `d_{ij} = 0` it is `t'_{ij}`;

with the parameters of `parameterTwist`, `x_out` the dot of colour `i` on the outer induction
and `x_in` the dot of colour `j` on the inner induction.
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-! ### Conjugation by the two-colour comparison -/

section Conjugation
variable (i j : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
  (M : HeightModules D Sc a ha n)

local notation "T" => heightCompositionCorner D Sc i j a ha n
local notation "Pc" => heightInductionCorner D Sc i a ha (n + 1)
local notation "Qc" => heightInductionCorner D Sc j a ha n
local notation "H" => heightTwoColourComparisonHom D Sc i j a ha n M
local notation "Iv" => heightTwoColourComparisonInv D Sc i j a ha n M

end Conjugation

/-! ### The quadratic relation on the induction functors -/

section InductionSquare
variable {i j : I} (hij : i ≠ j) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ) (M : HeightModules D Sc a ha n)

set_option quotPrecheck false in
local notation "Xout" => (heightSuperInductionDot D Sc i a ha (n + 1)).app (D.parity i)
  ((heightSuperInduction D Sc j a ha n).obj M)
set_option quotPrecheck false in
local notation "Xin" => (heightSuperInduction D Sc i a ha (n + 1)).map
  ((heightSuperInductionDot D Sc j a ha n).app (D.parity j) M)
set_option quotPrecheck false in
local notation "Ψ" => (heightSuperInductionCrossing D Sc i j a ha n).app
  (D.parity i * D.parity j) M ≫
    (heightSuperInductionCrossing D Sc j i a ha n).app (D.parity j * D.parity i) M

include hij

end InductionSquare

end OddMath.QuiverHecke.CyclotomicAction
