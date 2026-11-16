import OddMath.SKM.BWWReesParameters
import NonVacuity.BWWGradedParameters

/-! # Lower-degree Brundan–Wang–Webster parameters and their Rees parameters

On the datum of `NonVacuity.BWWScalars` with symmetrizer `(1, 1)`: the parameters
`Qᵢⱼ(u, v) = u³ + v³ + 1` over `ℚ` are lower-degree (they have no interior monomials), although
they are not graded homogeneous for `ℚ` concentrated in degree `0`
(`NonVacuity.BWWGradedParameters`). Their Rees parameters `u³ + v³ + h⁶` over `ℚ[h]` are graded
homogeneous and specialize to them at `h = 1`.
-/

noncomputable section
namespace NonVacuity.BWWReesParameters
open OddMath OddMath.SKM NonVacuity.BWWScalars NonVacuity.BWWGradedParameters

theorem constantTerm_lowerDegree : constantTerm.LowerDegree symmetrizer := by
  rw [BWWScalars.lowerDegree_iff_interior]
  intro i j p q hij hp hp' hq hq' hs
  rw [d_ne hij] at hp'
  rw [d_ne (Ne.symm hij)] at hq'
  have : ¬support p q := by unfold support; omega
  exact absurd (by simp [constantTerm, this]) hs

example : (BWWReesParameters.scalars symmetrizer constantTerm).GradedHomogeneous symmetrizer
    (MvPolynomial.homogeneousSubmodule Unit ℚ) :=
  BWWReesParameters.gradedHomogeneous symmetrizer constantTerm_lowerDegree

example : (BWWReesParameters.scalars symmetrizer constantTerm).map ReesParameters.specialize =
    constantTerm :=
  BWWReesParameters.map_specialize symmetrizer constantTerm

/-- The pure coefficient `1` of `Qᵢⱼ` becomes `h⁶` in the Rees parameters. -/
example : (BWWReesParameters.scalars symmetrizer constantTerm).c true false 0 0 =
    MvPolynomial.X () ^ 6 := by
  have h : BWWReesParameters.exponent symmetrizer true false 0 0 = 6 := by
    rw [BWWReesParameters.exponent_of_lt symmetrizer (by rw [d_ne (by decide)]; norm_num)
      (by rw [d_ne (by decide)]; norm_num)]
    simp only [coefficientDegree, symmetrizer, d_ne (show true ≠ false by decide)]
    norm_num
  simp [BWWReesParameters.scalars, h, constantTerm, support]

/-- The Brundan–Ellis conjecture on the interior part is a `BWWParameterProperty`. -/
example (cs : CScalars constantTerm.toScalars) :
    (BWWParameterProperty.interiorNondegeneracy.{0, 0, 0} datum).holds constantTerm cs ↔
      NondegeneracyConjecture cs :=
  Iff.rfl

end NonVacuity.BWWReesParameters
