import OddMath.QuiverHecke.CyclotomicAction.CoefficientPolynomialTransport

noncomputable section
namespace CoefficientPolynomialTransportConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke

/-- Odd rank one over a ring with two invertible. -/
def datum : SKM.Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two

def scalars : SKM.Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

def oddColour : {i : Unit // datum.parity i = 1} := ⟨(), rfl⟩

def delta : SKM.SYM datum ℚ := SKM.SYM.delta datum ℚ oddColour

/-- The tested exterior coefficient is not specialized to zero. -/
theorem delta_ne_zero : delta ≠ 0 := by
  intro h
  have he := congrArg (SKM.SYM.exteriorProjection datum ℚ) h
  simp only [delta, SKM.SYM.exteriorProjection_delta, map_zero] at he
  have hz := (ExteriorAlgebra.ι_eq_zero_iff (R := ℚ) _).mp he
  have hz' := congrArg (fun f : SKM.SYM.OddModule datum ℚ => f oddColour) hz
  simp at hz'

/-- 1 + delta*x + x² is even although its linear coefficient is odd. -/
def evenCoefficients : Fin 3 → SKM.SYM datum ℚ := ![1, delta, 1]

theorem evenCoefficients_parity (m : Fin 3) :
    SKM.SYM.polynomialExteriorEquiv datum ℚ (evenCoefficients m) ∈
      SKM.SYM.polynomialExteriorParity datum ℚ (0 - m.val • datum.parity ()) := by
  fin_cases m
  · simpa [evenCoefficients] using
      (SetLike.GradedOne.one_mem : (1 : SKM.SYM.PolynomialExterior datum ℚ) ∈
        SKM.SYM.polynomialExteriorParity datum ℚ 0)
  · simpa [evenCoefficients, delta, datum] using
      SKM.SYM.polynomialExterior_delta_mem_odd datum ℚ oddColour
  · simpa [evenCoefficients, datum, show (2 : ZMod 2) = 0 from rfl] using
      (SetLike.GradedOne.one_mem : (1 : SKM.SYM.PolynomialExterior datum ℚ) ∈
        SKM.SYM.polynomialExteriorParity datum ℚ 0)

/-- The coefficient sign cancels the dot sign at an odd crossing. -/
example :
    coefficientDotPolynomial datum scalars [(), ()] 0 2 evenCoefficients ≫
        sourceCoefficientHom datum scalars 1 (moveHom datum scalars () [] [()]) =
      sourceCoefficientHom datum scalars 1 (moveHom datum scalars () [] [()]) ≫
        coefficientDotPolynomial datum scalars [(), ()] 1 2 evenCoefficients := by
  simpa using coefficientDotPolynomial_comp_moveHom datum scalars () [] [()]
    2 evenCoefficients 0 evenCoefficients_parity

/-- The same cancellation holds on an old strand inside a three-crossing chain. -/
example := coefficientDotPolynomial_mem_comp_moveHom datum scalars () () [()] [()] []
  2 evenCoefficients 0 evenCoefficients_parity

/-- delta + x has odd total parity and a nonzero exterior constant term. -/
def oddCoefficients : Fin 2 → SKM.SYM datum ℚ := ![delta, 1]

theorem oddCoefficients_parity (m : Fin 2) :
    SKM.SYM.polynomialExteriorEquiv datum ℚ (oddCoefficients m) ∈
      SKM.SYM.polynomialExteriorParity datum ℚ (1 - m.val • datum.parity ()) := by
  fin_cases m
  · simpa [oddCoefficients, delta] using
      SKM.SYM.polynomialExterior_delta_mem_odd datum ℚ oddColour
  · simpa [oddCoefficients, datum] using
      (SetLike.GradedOne.one_mem : (1 : SKM.SYM.PolynomialExterior datum ℚ) ∈
        SKM.SYM.polynomialExteriorParity datum ℚ 0)

example :
    coefficientDotPolynomial datum scalars [(), ()] 0 1 oddCoefficients ≫
        sourceCoefficientHom datum scalars 1 (moveHom datum scalars () [] [()]) =
      -(sourceCoefficientHom datum scalars 1 (moveHom datum scalars () [] [()]) ≫
        coefficientDotPolynomial datum scalars [(), ()] 1 1 oddCoefficients) := by
  simpa [datum, wordSumParity, sign] using
    coefficientDotPolynomial_comp_moveHom datum scalars () [] [()]
      1 oddCoefficients 1 oddCoefficients_parity

/-- Old-strand transport uses the whole chain, also when its parity is even. -/
example := coefficientDotPolynomial_mem_comp_moveHom datum scalars () () [] [()] []
  1 oddCoefficients 1 oddCoefficients_parity

/-- The empty chain does not discard odd coefficients. -/
example := coefficientDotPolynomial_comp_moveHom datum scalars () [] []
  1 oddCoefficients 1 oddCoefficients_parity

#print axioms coefficientDotPolynomial_comp_moveHom
#print axioms coefficientDotPolynomial_mem_comp_moveHom
#print axioms delta_ne_zero
end CoefficientPolynomialTransportConsumer
