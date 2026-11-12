import OddMath.QuiverHecke.BWWEvenSpecialization
import NonVacuity.BWWNondegeneracy

/-! # The Brundan–Wang–Webster headline at parity zero, on a concrete datum

The datum of `NonVacuity.BWWScalars` (two vertices, Cartan entries `-3`) is purely even. The
graded parameters `u³ + v³ + h⁶` over `ℚ[h]` of `NonVacuity.BWWNondegeneracy`, written as
Brundan–Wang–Webster polynomials, satisfy every hypothesis of
`QuiverHecke.bwwPolynomials_evenNondegeneracy`.
-/

noncomputable section
namespace NonVacuity.BWWEvenSpecialization
open OddMath OddMath.SKM OddMath.QuiverHecke
open NonVacuity.BWWScalars NonVacuity.BWWGradedParameters NonVacuity.BWWReesParameters

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isEven : EvenBridge.IsEven datum := fun _ => rfl

/-- The graded parameters as Brundan–Wang–Webster polynomials. -/
abbrev polys : BWWPolynomials datum (MvPolynomial Unit ℚ) :=
  (BWWReesParameters.scalars symmetrizer constantTerm).toPolynomials

theorem polys_eq :
    bwwPolynomialsEquiv isEven polys = BWWReesParameters.scalars symmetrizer constantTerm :=
  bwwPolynomialsEquiv_toPolynomials isEven _

theorem polys_gradedHomogeneous :
    polys.GradedHomogeneous symmetrizer (MvPolynomial.homogeneousSubmodule Unit ℚ) :=
  (polys.gradedHomogeneous_toBWWScalars_iff symmetrizer _ isEven).1
    (by
      rw [show polys.toBWWScalars isEven = _ from polys_eq]
      exact BWWReesParameters.gradedHomogeneous symmetrizer constantTerm_lowerDegree)

/-- The normalization, transported along `polys_eq`. -/
def cs : CScalars (bwwPolynomialsEquiv isEven polys).toScalars :=
  polys_eq ▸ BWWReesParameters.cScalars symmetrizer BWWNondegeneracy.cScalars

example : NondegeneracyConjecture cs :=
  bwwPolynomials_evenNondegeneracy datum symmetrizer isEven (MvPolynomial Unit ℚ)
    (MvPolynomial.homogeneousSubmodule Unit ℚ) BWWNondegeneracy.isUnit_two_rees polys
    polys_gradedHomogeneous cs

/-- The quadratic relation of the presentation is `Qᵢⱼ(x, y)` pinned on `Eᵢ Eⱼ 1_ν`. -/
example (i j : Bool) (ν : Bool → ℤ) :
    SKM.quadSum datum (bwwPolynomialsEquiv isEven polys).c i j ν =
      pinQuad datum i j ν (polys.Q i j) :=
  quadSum_bwwPolynomials isEven polys i j ν

#print axioms bwwPolynomials_evenNondegeneracy
#print axioms quadSum_bwwPolynomials

end NonVacuity.BWWEvenSpecialization
