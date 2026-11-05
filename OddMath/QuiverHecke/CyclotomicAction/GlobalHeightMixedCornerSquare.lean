/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightMixedQuadratic
import OddMath.QuiverHecke.CyclotomicAction.ParameterTransport
import OddMath.SKM.Calculus

/-!
# The distinct-colour quadratic relation on the two-colour composition corners

The corner half of the quadratic relations (1.7) of Brundan–Ellis, arXiv:1701.04133v2,
Definition 1.5, for distinct colours, at a fixed height of the extended tower. On the corner
`T_{ij} = C θ(1)`, `θ = φᵢ ∘ φⱼ`, write `x_out` for signed right multiplication by the new last
dot `y_i` and `x_in` for signed right multiplication by the appended dot `φᵢ(y_j)`
(`heightTwoColourRightMul`). An `m`-fold power of signed right multiplication by a dot of
parity `c` acts on an element of parity `p` by the sign `(-1)^{c(mp + ⌊m/2⌋)}`
(`heightTwoColourRightMul_pow_apply`). With the algebra identity
`heightLastCrossing_mul_mixed`, the composite of the two corner crossings is, in diagrammatic
order,

  `ψ_{ij} ψ_{ji} = t'_{ij} x_out^{d_{ij}} + t'_{ji} x_in^{d_{ji}}
      + ∑_{0<p<d_{ij}, 0<q<d_{ji}} s'^{pq}_{ij} x_in^q x_out^p`

(`heightCompositionCorner_square_ne`), and `ψ_{ij} ψ_{ji} = t'_{ij}` if `d_{ij} = 0`
(`heightCompositionCorner_square_zero`), where `t'`, `s'` are the parameters of
`parameterTwist`. The signs of the odd powers of the crossing parities and of the dots are
exactly the signs recorded by `parameterTwist`: every surviving monomial has `p|i|` and `q|j|`
even (`Sc.s_eq_zero`, `Datum.even_d_of_odd`).
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-! ### Sign bookkeeping -/

theorem parameterSignUnit_coe (p : ZMod 2) :
    ((parameterSignUnit (k := k) p : kˣ) : k) = SKM.zsign k p := by
  unfold parameterSignUnit SKM.zsign
  split_ifs <;> simp

private theorem zmod_two_eq_zero_or_one (p : ZMod 2) : p = 0 ∨ p = 1 := by
  revert p; decide

private theorem zmod_two_mul_self (p : ZMod 2) : p * p = p := by
  rcases zmod_two_eq_zero_or_one p with rfl | rfl <;> decide

omit [Fintype I] in
/-- The twisted distinct-colour leading parameter. -/
theorem parameterTwist_t_of_ne {i j : I} (hij : i ≠ j) :
    (((parameterTwist D Sc).t i j : kˣ) : k) =
      SKM.zsign k (parameterSignExponent D i j (D.dn i j) 0) * (Sc.t i j : k) := by
  simp [parameterTwist, hij, parameterSignUnit_coe]

omit [Fintype I] in
/-- The twisted mixed parameters. -/
theorem parameterTwist_s (i j : I) (p q : ℕ) :
    (parameterTwist D Sc).s i j p q =
      SKM.zsign k (parameterSignExponent D i j p q) * Sc.s i j p q := rfl

omit [Fintype I] in
/-- An odd colour has an even number of dots on every connected strand. -/
theorem dn_cast_mul_parity {i j : I} (hij : i ≠ j) :
    (D.dn i j : ZMod 2) * D.parity i = 0 := by
  rcases zmod_two_eq_zero_or_one (D.parity i) with h | h
  · rw [h, mul_zero]
  · rw [h, mul_one]
    have he : Even (D.dn i j : ℤ) := by
      rw [D.dn_cast hij]
      exact D.even_d_of_odd h j
    exact (ZMod.natCast_eq_zero_iff_even).2 (Int.even_coe_nat _ |>.1 he)

/-! ### Powers of signed right multiplication -/

section Power
variable {i j c : I} {a : I → _root_.Polynomial k} {ha : CyclotomicPolynomialParity D a}
  {n : ℕ}

local notation "C" => heightAlgebra D Sc a (n + 1 + 1)
local notation "T" => heightCompositionCorner D Sc i j a ha n

end Power

/-! ### The corner square -/

section CornerSquare
variable {i j : I} (hij : i ≠ j) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)
include hij

local notation "T" => heightCompositionCorner D Sc i j a ha n
local notation "Cr" => heightCompositionSuperCrossing D Sc i j a ha n
local notation "Cr'" => heightCompositionSuperCrossing D Sc j i a ha n
local notation "Dr" => heightTwoColourRightMul D Sc i j i a ha n
  (twoColourCornerMulData_lastDot D Sc i j a ha n)
local notation "Dl" => heightTwoColourRightMul D Sc i j j a ha n
  (twoColourCornerMulData_appendDot D Sc i j a ha n)
local notation "A" => heightAppend D Sc a i (n + 1) (heightLastDot D Sc a j n)
local notation "B" => heightLastDot D Sc a i (n + 1)

end CornerSquare

end OddMath.QuiverHecke.CyclotomicAction
