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

/-- Conjugation of a corner endomorphism by the two-colour comparison. -/
def heightTwoColourConj : (T ⟶ T) →ₗ[k] (tensor Pc (tensor Qc M) ⟶ tensor Pc (tensor Qc M)) where
  toFun A := H ≫ whiskerRight A M ≫ Iv
  map_add' A B := by
    rw [add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' c A := by
    rw [smul_whiskerRight, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply]

theorem heightTwoColourConj_apply (A : T ⟶ T) :
    heightTwoColourConj D Sc i j a ha n M A = H ≫ whiskerRight A M ≫ Iv := rfl

theorem heightTwoColourConj_id : heightTwoColourConj D Sc i j a ha n M (𝟙 T) = 𝟙 _ := by
  rw [heightTwoColourConj_apply, id_whiskerRight, Category.id_comp,
    heightTwoColourComparisonHom_inv]

theorem heightTwoColourConj_comp (A B : T ⟶ T) :
    heightTwoColourConj D Sc i j a ha n M (A ≫ B) =
      heightTwoColourConj D Sc i j a ha n M A ≫ heightTwoColourConj D Sc i j a ha n M B := by
  simp only [heightTwoColourConj_apply, comp_whiskerRight, Category.assoc]
  rw [← Category.assoc Iv H, heightTwoColourComparisonInv_hom, Category.id_comp]

theorem heightTwoColourConj_endoPower (A : T ⟶ T) (m : ℕ) :
    heightTwoColourConj D Sc i j a ha n M (endoPower A m) =
      endoPower (heightTwoColourConj D Sc i j a ha n M A) m := by
  induction m with
  | zero => exact heightTwoColourConj_id D Sc i j a ha n M
  | succ m ih =>
    rw [endoPower_succ, endoPower_succ, heightTwoColourConj_comp, ih]

/-- An endomorphism intertwined with `A` by the comparison is the conjugate of `A`. -/
theorem heightTwoColourConj_eq_of_comp {Y : tensor Pc (tensor Qc M) ⟶ tensor Pc (tensor Qc M)}
    {A : T ⟶ T} (h : Y ≫ H = H ≫ whiskerRight A M) :
    heightTwoColourConj D Sc i j a ha n M A = Y := by
  rw [heightTwoColourConj_apply, ← Category.assoc, ← h, Category.assoc,
    heightTwoColourComparisonHom_inv, Category.comp_id]

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

private theorem conj_lastDot :
    heightTwoColourConj D Sc i j a ha n M (heightTwoColourRightMul D Sc i j i a ha n
      (twoColourCornerMulData_lastDot D Sc i j a ha n)) = Xout := by
  have hX : Xout = whiskerRight (heightInductionSuperDot D Sc i a ha (n + 1))
      (tensor (heightInductionCorner D Sc j a ha n) M) := by
    simp only [heightSuperInductionDot, ↓reduceIte]; rfl
  rw [hX]
  exact heightTwoColourConj_eq_of_comp D Sc i j a ha n M
    (heightTwoColourComparison_dot_outer_app D Sc i j a ha n M)

private theorem conj_appendDot :
    heightTwoColourConj D Sc i j a ha n M (heightTwoColourRightMul D Sc i j j a ha n
      (twoColourCornerMulData_appendDot D Sc i j a ha n)) = Xin := by
  have hX : (heightSuperInductionDot D Sc j a ha n).app (D.parity j) M =
      whiskerRight (heightInductionSuperDot D Sc j a ha n) M := by
    simp only [heightSuperInductionDot, ↓reduceIte]
  rw [hX]
  exact heightTwoColourConj_eq_of_comp D Sc i j a ha n M
    (heightTwoColourComparison_dot_inner_app D Sc i j a ha n M)

private theorem crossing_square_eq_conj :
    Ψ = heightTwoColourConj D Sc i j a ha n M
      (heightCompositionSuperCrossing D Sc i j a ha n ≫
        heightCompositionSuperCrossing D Sc j i a ha n) := by
  rw [heightSuperInductionCrossing_app, heightSuperInductionCrossing_app,
    heightTwoColourConj_apply, comp_whiskerRight]
  change heightTwoColourComparisonHom D Sc i j a ha n M ≫
      whiskerRight (heightCompositionSuperCrossing D Sc i j a ha n) M ≫
        heightTwoColourComparisonInv D Sc j i a ha n M ≫
          heightTwoColourComparisonHom D Sc j i a ha n M ≫
            whiskerRight (heightCompositionSuperCrossing D Sc j i a ha n) M ≫
              heightTwoColourComparisonInv D Sc i j a ha n M = _
  rw [← Category.assoc (heightTwoColourComparisonInv D Sc j i a ha n M),
    heightTwoColourComparisonInv_hom, Category.id_comp]
  simp only [Category.assoc]

include hij

/-- **The distinct-colour quadratic relation for two inductions**, `d_{ij} ≠ 0`
(components; BE2 (1.7) with the parameters of `parameterTwist`). -/
theorem heightInduction_square_ne (hd : D.d i j ≠ 0) :
    Ψ = ((parameterTwist D Sc).t i j : k) • endoPower Xout (D.dn i j) +
      ((parameterTwist D Sc).t j i : k) • endoPower Xin (D.dn j i) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        (parameterTwist D Sc).s i j p q • (endoPower Xin q ≫ endoPower Xout p) := by
  rw [crossing_square_eq_conj, heightCompositionCorner_square_ne D Sc hij a ha n hd]
  simp only [map_add, map_smul, map_sum, heightTwoColourConj_comp,
    heightTwoColourConj_endoPower, conj_lastDot, conj_appendDot]

/-- **The distinct-colour quadratic relation for two inductions**, `d_{ij} = 0`. -/
theorem heightInduction_square_zero (hd : D.d i j = 0) :
    Ψ = ((parameterTwist D Sc).t i j : k) • 𝟙 _ := by
  rw [crossing_square_eq_conj, heightCompositionCorner_square_zero D Sc hij a ha n hd, map_smul,
    heightTwoColourConj_id]
  rfl

end InductionSquare

end OddMath.QuiverHecke.CyclotomicAction
