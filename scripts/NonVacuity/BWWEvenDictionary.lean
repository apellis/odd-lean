import OddMath.SKM.BWWEvenDictionary
import NonVacuity.BWWScalars

/-! # The even dictionary for Brundan–Wang–Webster polynomials

On the datum of `NonVacuity.BWWScalars` (two even vertices, Cartan entries `-3`), the
coefficient function of `Qᵢⱼ(u, v) = u³ + v³ + 1` gives polynomials of the shape (2.7), the
dictionary recovers the coefficient function, and (2.7) holds for `Qₜᵣᵤₑ,fₐₗₛₑ`.
-/

noncomputable section
namespace NonVacuity.BWWEvenDictionary
open OddMath OddMath.SKM NonVacuity.BWWScalars

theorem even : ∀ i, datum.parity i = 0 := fun _ => rfl

/-- The polynomials of `u³ + v³ + 1`. -/
def polys : BWWPolynomials datum ℚ := constantTerm.toPolynomials

example : (bwwPolynomialsEquiv even) polys = constantTerm :=
  (bwwPolynomialsEquiv even).right_inv constantTerm

theorem coeff_constant : (polys.Q true false).coeff (bwwExp 0 0) = 1 := by
  rw [polys, BWWScalars.toPolynomials_Q, BWWScalars.coeff_poly]
  simp [constantTerm, support]

example : polys.Q true false =
    MvPolynomial.monomial (bwwExp (datum.dn true false) 0) (polys.t true false : ℚ) +
      ∑ r ∈ Finset.range (datum.dn true false), ∑ s ∈ Finset.range (datum.dn false true),
        MvPolynomial.monomial (bwwExp r s) ((polys.Q true false).coeff (bwwExp r s)) +
      MvPolynomial.monomial (bwwExp 0 (datum.dn false true)) (polys.t false true : ℚ) :=
  polys.eq_form (by decide) (by rw [dn_ne (by decide)]; norm_num)

end NonVacuity.BWWEvenDictionary
