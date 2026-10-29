/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LeadingMoveProduct

/-!
# The global sign of the ordered square product

The unsigned product `leadingMoveSquareProduct` is defined directly from square
differences, not from coefficients or an inverse coordinate map. Its factors are
in chronological order (earlier factors on the right in the endomorphism ring).
The library's endpoint polynomial is this product times one parity sign for each
old strand of the moving colour. No restriction on the other colours is needed.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Unsigned local square difference: odd colours use squared dots, even
colours use dots, and unequal colours contribute the identity. -/
def leadingSourceUnsignedSquare (t : List I) (i j : I) (m p : ℕ) :
    End ((pres D Sc).obj (ob D t)) :=
  if i = j then
    if D.parity i = 1 then (dotE D Sc t m ^ 2 - dotE D Sc t p ^ 2) ^ 2
    else (dotE D Sc t m - dotE D Sc t p) ^ 2
  else 1

/-- Independently prescribed unsigned ordered product at a fixed endpoint.
The old positions increase from `a + 1`, with earlier factors on the right. -/
def leadingSourceUnsignedProduct (t : List I) (i : I) (m : ℕ) : ℕ → List I →
    End ((pres D Sc).obj (ob D t))
  | _, [] => 1
  | a, j :: ν => leadingSourceUnsignedProduct t i m (a + 1) ν *
      leadingSourceUnsignedSquare D Sc t i j m (a + 1)

/-- The unsigned ordered `S` product on the original source word. -/
def leadingMoveSquareProduct (i : I) (l ν : List I) :
    End ((pres D Sc).obj (ob D (l ++ i :: ν))) :=
  leadingSourceUnsignedProduct D Sc (l ++ i :: ν) i l.length l.length ν

/-- A matching factor contributes exactly the library parity sign. -/
theorem leadingSourceSquare_eq_sign_smul (t : List I) (i j : I) (m p : ℕ) :
    leadingSourceSquare D Sc t i j m p =
      (if i = j then SKM.zsign k (D.parity i) else 1) •
        leadingSourceUnsignedSquare D Sc t i j m p := by
  by_cases hij : i = j
  · subst j
    by_cases hp : D.parity i = 1
    all_goals simp [leadingSourceSquare, leadingSourceUnsignedSquare, SKM.zsign, hp]
  · simp [leadingSourceSquare, leadingSourceUnsignedSquare, hij]

/-- Pulling out the local signs gives `(-1)^(parity(i) * count_i(ν))`.
The power of `zsign` expresses this without choosing an integer lift of parity. -/
theorem leadingSourceProduct_eq_sign_smul (t : List I) (i : I) (m a : ℕ)
    (ν : List I) :
    leadingSourceProduct D Sc t i m a ν =
      SKM.zsign k (D.parity i) ^ ν.count i •
        leadingSourceUnsignedProduct D Sc t i m a ν := by
  induction ν generalizing a with
  | nil => simp [leadingSourceProduct, leadingSourceUnsignedProduct]
  | cons j ν ih =>
    rw [leadingSourceProduct, leadingSourceUnsignedProduct, ih,
      leadingSourceSquare_eq_sign_smul]
    by_cases hij : i = j
    · subst j
      simp [pow_succ, smul_smul, mul_comm]
    · simp [hij, Ne.symm hij]

/-- The signed product equals the explicit global library sign times `S`. -/
theorem leadingMoveProduct_eq_sign_smul_squareProduct (i : I) (l ν : List I) :
    leadingMoveProduct D Sc i l ν =
      SKM.zsign k (D.parity i) ^ ν.count i • leadingMoveSquareProduct D Sc i l ν :=
  leadingSourceProduct_eq_sign_smul D Sc (l ++ i :: ν) i l.length l.length ν

/-- The endpoint polynomial equals the global sign times the independently
specified unsigned `S`, for arbitrary words and both parities. -/
theorem leadingMoveEndpointPolynomial_eq_sign_smul_squareProduct
    (i : I) (l ν : List I) :
    leadingMoveEndpointPolynomial D Sc i l ν =
      SKM.zsign k (D.parity i) ^ ν.count i • leadingMoveSquareProduct D Sc i l ν := by
  rw [leadingMoveEndpointPolynomial_eq_product,
    leadingMoveProduct_eq_sign_smul_squareProduct]

/-- Synthesizing the explicit finite coefficients as endpoint monomials gives
exactly the global sign times the unsigned product; no coordinate inverse is used. -/
theorem leadingSource_expansion_eq_sign_smul (t : List I) (i : I) (m a : ℕ)
    (ν : List I) :
    (∑ c : MoveChoices ν, leadingMoveCoeff D (k := k) i ν c •
      (show End ((pres D Sc).obj (ob D t)) from
        endpointDotMonomial D Sc t (leadingSourceDots D i m a ν c))) =
      SKM.zsign k (D.parity i) ^ ν.count i •
        leadingSourceUnsignedProduct D Sc t i m a ν := by
  rw [← leadingSourceProduct_expansion, leadingSourceProduct_eq_sign_smul]

end OddMath.QuiverHecke
