/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LeadingMoveTransport

/-!
# Ordered square-difference product of a leading move

The source-endpoint polynomial of the leading moving chain is the ordered
product of signed square differences. The product uses endomorphism-ring
multiplication, with the earliest chronological factor on the right.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- The local signed square difference, independently of expansion choices. -/
def leadingSourceSquare (t : List I) (i j : I) (m p : ℕ) :
    End ((pres D Sc).obj (ob D t)) :=
  if i = j then
    if D.parity i = 1 then -(dotE D Sc t m ^ 2 - dotE D Sc t p ^ 2) ^ 2
    else (dotE D Sc t m - dotE D Sc t p) ^ 2
  else 1

/-- Ordered product at a fixed source word. Old positions increase from `a+1`;
endomorphism multiplication puts earlier chronological factors on the right. -/
def leadingSourceProduct (t : List I) (i : I) (m : ℕ) : ℕ → List I →
    End ((pres D Sc).obj (ob D t))
  | _, [] => 1
  | a, j :: ν => leadingSourceProduct t i m (a + 1) ν *
      leadingSourceSquare D Sc t i j m (a + 1)

/-- The ordered square-difference product on the original source endpoint. -/
def leadingMoveProduct (i : I) (l ν : List I) :
    End ((pres D Sc).obj (ob D (l ++ i :: ν))) :=
  leadingSourceProduct D Sc (l ++ i :: ν) i l.length l.length ν

theorem endpointDotMonomial_append (t : List I) (ps qs : List ℕ) :
    endpointDotMonomial D Sc t (ps ++ qs) =
      (show End ((pres D Sc).obj (ob D t)) from endpointDotMonomial D Sc t qs) *
        (show End ((pres D Sc).obj (ob D t)) from endpointDotMonomial D Sc t ps) := by
  simp only [endpointDotMonomial, List.map_append, cl_mul]

theorem leadingSourceSquare_expansion (t : List I) (i j : I) (m p : ℕ) :
    leadingSourceSquare D Sc t i j m p =
      ∑ c : Fin 4, leadingBlockCoeff D (k := k) i j c •
        (show End ((pres D Sc).obj (ob D t)) from
          endpointDotMonomial D Sc t (leadingSourceBlockDots D i j m p c)) := by
  by_cases hij : i = j
  · subst j
    by_cases hp : D.parity i = 1
    all_goals
      simp only [leadingSourceSquare, leadingBlockCoeff, leadingSourceBlockDots,
        hp, ite_true, ite_false, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue,
        Fin.sum_univ_zero, add_zero, neg_smul, one_smul, Fin.val_zero, Fin.val_succ]
      simp only [pow_two, sub_mul, mul_sub, neg_sub]
      simp only [dotE_eq_cl D Sc (sChain_dotAny _ _), cl_mul,
        endpointDotMonomial, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append]
      abel
  · simp [leadingSourceSquare, leadingBlockCoeff, leadingSourceBlockDots, hij,
      endpointDotMonomial, cl_nil]

theorem leadingSourceProduct_expansion (t : List I) (i : I) (m a : ℕ) (ν : List I) :
    leadingSourceProduct D Sc t i m a ν =
      ∑ c : MoveChoices ν, leadingMoveCoeff D (k := k) i ν c •
        (show End ((pres D Sc).obj (ob D t)) from
          endpointDotMonomial D Sc t (leadingSourceDots D i m a ν c)) := by
  induction ν generalizing a with
  | nil =>
    change (1 : End ((pres D Sc).obj (ob D t))) = ∑ c : Unit, _
    simp [leadingMoveCoeff, leadingSourceDots, endpointDotMonomial, cl_nil]
  | cons j ν ih =>
    rw [leadingSourceProduct, ih, leadingSourceSquare_expansion]
    conv_rhs =>
      change ∑ c : Fin 4 × MoveChoices ν, _
      rw [Fintype.sum_prod_type]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    simp only [leadingMoveCoeff, leadingSourceDots, endpointDotMonomial_append,
      smul_mul_assoc, mul_smul_comm, smul_smul]

/-- Exact endpoint identification for arbitrary prefixes and words, in either parity. -/
theorem leadingMoveEndpointPolynomial_eq_product (i : I) (l ν : List I) :
    leadingMoveEndpointPolynomial D Sc i l ν = leadingMoveProduct D Sc i l ν := by
  simp only [leadingMoveEndpointPolynomial, collectedSourceSign_leadingMoveBlocks,
    mul_one, collectedSourceDots_leadingMoveBlocks, leadingMoveProduct,
    leadingSourceProduct_expansion]

end OddMath.QuiverHecke
