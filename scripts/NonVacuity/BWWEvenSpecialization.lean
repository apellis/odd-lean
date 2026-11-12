import OddMath.QuiverHecke.BWWEvenSpecialization
import OddMath.QuiverHecke.BWWEvenGradedBasis
import NonVacuity.BWWNondegeneracy

/-! # The Brundan–Wang–Webster headline at parity zero, on a concrete datum

The datum of `NonVacuity.BWWScalars` (two vertices, Cartan entries `-3`) is purely even. The
graded parameters `u³ + v³ + h⁶` over `ℚ[h]` of `NonVacuity.BWWNondegeneracy`, written as
Brundan–Wang–Webster polynomials, satisfy every hypothesis of
`QuiverHecke.bwwPolynomials_evenNondegeneracy`. The normalization is `1`, of degree `0`, so the
graded form `QuiverHecke.bwwPolynomials_evenGradedNondegeneracy` applies as well: the basis
elements are homogeneous for the total grading.
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

/-- The transported normalization is `1`. -/
theorem cs_c (μ : Bool → ℤ) (i : Bool) : (cs.c μ i : MvPolynomial Unit ℚ) = 1 := by
  have key : ∀ (S : BWWScalars datum (MvPolynomial Unit ℚ))
      (h : S = BWWReesParameters.scalars symmetrizer constantTerm),
      ((h ▸ BWWReesParameters.cScalars symmetrizer BWWNondegeneracy.cScalars :
        CScalars S.toScalars).c μ i : MvPolynomial Unit ℚ) = 1 := by
    rintro S rfl
    simp [BWWReesParameters.cScalars, BWWNondegeneracy.cScalars]
  exact key _ polys_eq

theorem cs_mem_zero (μ : Bool → ℤ) (i : Bool) :
    (cs.c μ i : MvPolynomial Unit ℚ) ∈ MvPolynomial.homogeneousSubmodule Unit ℚ 0 := by
  rw [cs_c]
  exact SetLike.GradedOne.one_mem

/-- The relations are homogeneous for the total grading. -/
example : Diagrams.CoefficientGrading.IsHomogeneous
    (natIntGrading (MvPolynomial.homogeneousSubmodule Unit ℚ)) (SKM.gdeg datum symmetrizer)
    (SKM.pres datum (bwwPolynomialsEquiv isEven polys).toScalars) :=
  bwwPolynomials_isHomogeneous datum symmetrizer isEven (MvPolynomial Unit ℚ)
    (MvPolynomial.homogeneousSubmodule Unit ℚ) polys polys_gradedHomogeneous

/-- The graded form: a basis of decorated matchings times bubble monomials, each element in
its total degree. -/
example : ∀ (a b : List (Letter Bool)), SKM.wt datum 0 a = SKM.wt datum 0 b →
    ∀ (μ : Bool → ℤ) (F : MatchingBasisChoice a b), ∃ hF : F.IsBasis cs μ,
      ∀ x, F.homogeneousBasis cs μ hF x ∈
        Diagrams.CoefficientGrading.presentedPart
          (natIntGrading (MvPolynomial.homogeneousSubmodule Unit ℚ)) (SKM.gdeg datum symmetrizer)
          (SKM.pres datum (bwwPolynomialsEquiv isEven polys).toScalars) (SKM.ob datum μ a)
          (SKM.ob datum μ b)
          (SYM.coefficientDegree datum symmetrizer x.2 +
            SKM.tableDegree datum symmetrizer μ (F.layers x.1)) :=
  bwwPolynomials_evenGradedNondegeneracy datum symmetrizer isEven (MvPolynomial Unit ℚ)
    (MvPolynomial.homogeneousSubmodule Unit ℚ) BWWNondegeneracy.isUnit_two_rees polys
    polys_gradedHomogeneous cs cs_mem_zero

/-- The graded direct-sum decomposition of every morphism space, for the
`MvPolynomial Unit ℚ`-valued polynomials, through the `GradedAlgebra` instance of
`natIntGrading`. -/
example (a b : StringDiagrams.Obj (SKM.sig datum)) :
    iSupIndep (Diagrams.CoefficientGrading.presentedPart
        (natIntGrading (MvPolynomial.homogeneousSubmodule Unit ℚ)) (SKM.gdeg datum symmetrizer)
        (SKM.pres datum (bwwPolynomialsEquiv isEven polys).toScalars) a b) ∧
      ⨆ d, Diagrams.CoefficientGrading.presentedPart
        (natIntGrading (MvPolynomial.homogeneousSubmodule Unit ℚ)) (SKM.gdeg datum symmetrizer)
        (SKM.pres datum (bwwPolynomialsEquiv isEven polys).toScalars) a b d = ⊤ :=
  bwwPolynomials_evenDirectSum datum symmetrizer isEven (MvPolynomial Unit ℚ)
    (MvPolynomial.homogeneousSubmodule Unit ℚ) polys polys_gradedHomogeneous a b

#print axioms bwwPolynomials_evenNondegeneracy
#print axioms bwwPolynomials_evenDirectSum
#print axioms natIntGrading_gradedAlgebra
#print axioms bwwPolynomials_isHomogeneous
#print axioms bwwPolynomials_evenGradedNondegeneracy
#print axioms natIntGrading_gradedMonoid
#print axioms inv_mem_zero_of_mem_zero
#print axioms SKM.isHomogeneous_coefficientGraded
#print axioms SKM.iSupIndep_coefficientGraded
#print axioms SKM.MatchingBasisChoice.homogeneousBasis_mem
#print axioms SKM.expansion_single_smul_coefficientBasis_mem
#print axioms SKM.betaSYM_coefficientBasis_mem
#print axioms quadSum_bwwPolynomials

end NonVacuity.BWWEvenSpecialization
