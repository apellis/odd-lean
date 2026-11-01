import OddMath.Algebra.DegreeShiftRowDivision
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenOffDiagonalLeading

/-! # Even boundary division on arbitrary old Homs

DeformedBoundaryDivision (5), moving parity zero: the existing polynomial
boundary itself has the proved unit leading maps in its ordinary coefficient
coordinates. The module-valued degree-shift division theorem gives exact
kernel support and unique quotient/remainder windows. No corrected-coordinate
basis change or categorical crossing inverse is assumed.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Exact low kernel of the even boundary in ordinary source coordinates. -/
theorem offDiagonalPolynomialBoundary_even_eq_zero_iff (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalPolynomialBoundary D Sc cutoff p i v t f = 0 ↔
      ∀ d ∈ f.support, d + endpointQPDegree D cutoff i v < outputSDegree D i v :=
  OddMath.Algebra.DegreeShiftRow.eq_zero_iff
    (offDiagonalPolynomialBoundary D Sc cutoff p i v t)
    (fun _ => evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t)
    (outputSDegree D i v) (endpointQPDegree D cutoff i v)
    (offDiagonalBoundary_even_above D Sc cutoff p i hi v t)
    (offDiagonalBoundary_even_top D Sc cutoff p i hi v t) f

/-- Even nonnegative-height polynomial boundary injection. -/
theorem offDiagonalPolynomialBoundary_even_injective (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I)
    (h : outputSDegree D i v ≤ endpointQPDegree D cutoff i v) :
    Function.Injective (offDiagonalPolynomialBoundary D Sc cutoff p i v t) :=
  OddMath.Algebra.DegreeShiftRow.injective
    (offDiagonalPolynomialBoundary D Sc cutoff p i v t)
    (fun _ => evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t)
    (outputSDegree D i v) (endpointQPDegree D cutoff i v)
    (offDiagonalBoundary_even_above D Sc cutoff p i hi v t)
    (offDiagonalBoundary_even_top D Sc cutoff p i hi v t) h

/-- Even nonpositive-height polynomial boundary surjection. -/
theorem offDiagonalPolynomialBoundary_even_surjective (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I)
    (h : endpointQPDegree D cutoff i v ≤ outputSDegree D i v) :
    Function.Surjective (offDiagonalPolynomialBoundary D Sc cutoff p i v t) :=
  OddMath.Algebra.DegreeShiftRow.surjective
    (offDiagonalPolynomialBoundary D Sc cutoff p i v t)
    (fun _ => evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t)
    (outputSDegree D i v) (endpointQPDegree D cutoff i v)
    (offDiagonalBoundary_even_above D Sc cutoff p i hi v t)
    (offDiagonalBoundary_even_top D Sc cutoff p i hi v t) h

/-- Allowed quotient coefficients outside the low kernel. -/
abbrev evenBoundaryRowHigh (i : I) (v t : List I) :=
  OddMath.Algebra.DegreeShiftRow.high (k := k) (M := Old D Sc cutoff v t)
    (outputSDegree D i v) (endpointQPDegree D cutoff i v)

/-- Literal output window below the nonnegative height. -/
abbrev evenBoundaryRowWindow (i : I) (v t : List I) :=
  OddMath.Algebra.DegreeShiftRow.window (k := k) (M := Old D Sc cutoff v t)
    (outputSDegree D i v) (endpointQPDegree D cutoff i v)

/-- Unique even boundary-row division on arbitrary old Hom coefficients. -/
def evenBoundaryRowDivisionEquiv (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v t : List I) :
    (evenBoundaryRowHigh D Sc cutoff i v t × evenBoundaryRowWindow D Sc cutoff i v t) ≃ₗ[k]
      (ℕ →₀ Old D Sc cutoff v t) :=
  OddMath.Algebra.DegreeShiftRow.divisionEquiv
    (offDiagonalPolynomialBoundary D Sc cutoff p i v t)
    (fun _ => evenOffDiagonalBoundaryLeadingEquiv D Sc cutoff p i v t)
    (outputSDegree D i v) (endpointQPDegree D cutoff i v)
    (offDiagonalBoundary_even_above D Sc cutoff p i hi v t)
    (offDiagonalBoundary_even_top D Sc cutoff p i hi v t)

@[simp] theorem evenBoundaryRowDivisionEquiv_apply (p : ZMod 2) (i : I)
    (hi : D.parity i = 0) (v t : List I)
    (x : evenBoundaryRowHigh D Sc cutoff i v t × evenBoundaryRowWindow D Sc cutoff i v t) :
    evenBoundaryRowDivisionEquiv D Sc cutoff p i hi v t x =
      offDiagonalPolynomialBoundary D Sc cutoff p i v t x.1 + x.2 := rfl

end OddMath.QuiverHecke.ELVOld
