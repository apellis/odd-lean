/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.VermaComparison
import OddMath.CoveringQuantum.UDot.VermaWeightExamples

/-!
# Verma polarization and polynomial comparison on infinite non-bar data

The constructed polarization and its comparison with the half form apply to the
countable datum `VermaWeightExamples.datum` at a negative highest weight. These
applications use generated elements of the Serre quotient and a two-letter word.
The adjoint convention is BE2 rho / Clark IV Proposition 5.8's tau1-prime; the
comparison retains its word sign. This is an algebraic precursor motivated by
CHWII Proposition 6.10, not its limit theorem. No nonzero-vector, convergence,
integrable-descent, nondegeneracy or graphical-equality assertion is made.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.VermaComparisonExamples
open PreF Coefficients GenericVerma VermaWeightExamples

/-- The chosen highest weight has a negative coroot pairing. -/
def highestWeight : ℕ →₀ ℤ := Finsupp.single 0 (-3)

/-- Infinite colours, failure of bar-consistency, and the negative pairing. -/
theorem applicability : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent ∧
    datum.h 0 highestWeight = -3 := by
  refine ⟨inferInstance, not_barConsistent, ?_⟩
  simp [highestWeight, datum, RootDatum.h]

/-- A generated quotient input with a vacuum component. -/
def leftInput : datum.serreF Coefficients.q pi :=
  datum.toSerreF Coefficients.q pi (θ Coefficients.Ring 0) +
    (Coefficients.q : Coefficients.Ring) • 1

/-- The free second input used in the polynomial comparison. -/
def freeInput : PreF Coefficients.Ring ℕ :=
  monomial Coefficients.Ring [0, 1] +
    (Coefficients.q : Coefficients.Ring) • θ Coefficients.Ring 0

/-- Its image in the existing Serre quotient. -/
def rightInput : datum.serreF Coefficients.q pi :=
  datum.toSerreF Coefficients.q pi freeInput

/-- A constructed element of the modified quotient, not an assumed operator. -/
def operator : modified datum Coefficients.q pi :=
  negativeHalf datum Coefficients.q pi highestWeight leftInput

/-- Vacuum normalization at the negative highest weight. -/
theorem unit_pairing : polarization datum highestWeight 1 1 = 1 :=
  polarization_one_one datum highestWeight

/-- Symmetry on the generated quotient inputs. -/
theorem generated_symmetry :
    polarization datum highestWeight leftInput rightInput =
      polarization datum highestWeight rightInput leftInput :=
  polarization_comm datum highestWeight leftInput rightInput

/-- Rho-adjointness for the constructed modified action on these inputs. -/
theorem generated_adjoint :
    polarization datum highestWeight
      (modifiedRepresentation datum highestWeight operator leftInput) rightInput =
    polarization datum highestWeight leftInput
      (modifiedRepresentation datum highestWeight
        (rhoModified datum Coefficients.q pi pi_sq operator) rightInput) :=
  polarization_adjoint datum highestWeight operator leftInput rightInput

/-- Comparison for a nonempty word, with the explicit deformation parameter and sign. -/
theorem word_comparison :
    polarization datum highestWeight
      (datum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [0, 1])) rightInput =
    wordSign datum highestWeight [0, 1] *
      MvPolynomial.eval (deformationParameter datum highestWeight)
        (wordPolynomial datum [0, 1] freeInput) :=
  polarization_word_polynomial datum highestWeight [0, 1] freeInput

/-- The exact constant coefficient is the existing half pairing. -/
theorem word_constant :
    MvPolynomial.constantCoeff (wordPolynomial datum [0, 1] freeInput) =
      datum.form Coefficients.q pi (monomial Coefficients.Ring [0, 1]) freeInput :=
  wordPolynomial_constantCoeff datum [0, 1] freeInput

/-- The two-letter comparison polynomial has total degree at most two. -/
theorem word_degree : (wordPolynomial datum [0, 1] freeInput).totalDegree ≤ 2 :=
  wordPolynomial_totalDegree datum [0, 1] freeInput

/-- The normalized polarization minus the actual Serre-half form is the evaluated error. -/
theorem normalized_difference :
    wordSign datum highestWeight [0, 1] *
      polarization datum highestWeight
        (datum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [0, 1])) rightInput -
      datum.serreForm Coefficients.q pi pi_sq
        (datum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [0, 1])) rightInput =
    MvPolynomial.eval (deformationParameter datum highestWeight)
      (comparisonError datum [0, 1] freeInput) :=
  polarization_sub_half datum highestWeight [0, 1] freeInput

/-- The error has zero constant coefficient, not a claimed q-adic valuation. -/
theorem error_constant :
    MvPolynomial.constantCoeff (comparisonError datum [0, 1] freeInput) = 0 :=
  comparisonError_constantCoeff datum [0, 1] freeInput

/-- The exact word-length bound specializes to two for this error. -/
theorem error_degree : (comparisonError datum [0, 1] freeInput).totalDegree ≤ 2 :=
  comparisonError_totalDegree datum [0, 1] freeInput

end OddMath.CoveringQuantum.UDot.VermaComparisonExamples
