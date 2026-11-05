import OddMath.QuiverHecke.CyclotomicAction.ELVScalarSpecializationFunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVOldRightContext

/-! # Scalar images of the actual ELV dot polynomials

The polynomial below records the chosen scalar coefficient images. This module
computes the actual signed specialization on every strand. Identifying these
coefficients with the prescribed binomial probe remains a separate calculation.
-/
noncomputable section
open CategoryTheory StringDiagrams
open OddMath.SKM.SYM
open scoped Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (values : I × ℕ → k)
  (hvalues : ∀ i r, elvElementaryRank D cutoff i ≤ r → values (i,r) = 0)

/-- The ordinary polynomial whose coefficients are the chosen scalar images. -/
def scalarCoefficientPolynomial (N : ℕ) (c : Fin (N+1) → SKM.SYM D k) :
    Polynomial k :=
  ∑ j, Polynomial.C (scalarEvaluation D values (c j)) * Polynomial.X ^ j.val

theorem elvAffineScalarSpecialization_dotPolynomial
    (w : List I) (r N : ℕ) (c : Fin (N+1) → SKM.SYM D k) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _ (coefficientDotPolynomial D Sc w r N c)) =
        Polynomial.aeval (dotE D Sc w r)
          (scalarCoefficientPolynomial D values N c) := by
  simp only [coefficientDotPolynomial, scalarCoefficientPolynomial, map_sum, Functor.map_sum,
    elvAffineScalarSpecialization_source, map_mul, Polynomial.aeval_C, map_pow,
    Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

/-- The odd first-strand generator maps to its literal ordinary scalar polynomial. -/
theorem elvAffineScalarSpecialization_elvCyclotomic
    (i : {i : I // D.parity i = 1}) (tail : List I) (N : ℕ) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _ (elvCyclotomic D Sc i tail N)) =
        Polynomial.aeval (dotE D Sc (i.1 :: tail) 0)
          (scalarCoefficientPolynomial D values N (elvMonicCoefficient D k i N)) := by
  rw [← elvDotPolynomial_first]
  exact elvAffineScalarSpecialization_dotPolynomial D Sc cutoff values hvalues
    (i.1 :: tail) 0 N (elvMonicCoefficient D k i N)

/-- The same scalar polynomial formula for the original first-dot presentation. -/
theorem elvAffineScalarSpecialization_deformedCyclotomic
    (w : List I) (N : ℕ) (c : Fin (N+1) → SKM.SYM D k) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _ (deformedCyclotomic D Sc w N c)) =
        Polynomial.aeval (dotE D Sc w 0)
          (scalarCoefficientPolynomial D values N c) := by
  have hp : deformedCyclotomic D Sc w N c = coefficientDotPolynomial D Sc w 0 N c := by
    unfold deformedCyclotomic coefficientDotPolynomial
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simp only [dotE_pow, firstDotPower, List.map_replicate]
  rw [hp]
  exact elvAffineScalarSpecialization_dotPolynomial D Sc cutoff values hvalues w 0 N c

/-- The actual even-colour first-strand relation has the corresponding scalar image. -/
theorem elvAffineScalarSpecialization_evenCyclotomic
    (i : I) (tail : List I) (N : ℕ) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _ (evenCyclotomic D Sc i tail N)) =
        Polynomial.aeval (dotE D Sc (i :: tail) 0)
          (scalarCoefficientPolynomial D values N (evenMonicCoefficient D k i N)) :=
  elvAffineScalarSpecialization_deformedCyclotomic D Sc cutoff values hvalues
    (i :: tail) N (evenMonicCoefficient D k i N)

/-- Appending spectator strands commutes with actual scalar specialization.
This supplies the append-range compatibility before quotient descent. -/
theorem elvAffineScalarSpecialization_rightContext
    (σ v w : List I) (f : ELVOld.hom D Sc cutoff v w) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (ELVOld.rightContext D Sc cutoff σ v w f) =
        ELVOld.affineRightContext D Sc σ v w
          ((elvAffineScalarSpecialization D Sc cutoff values hvalues).map f) := by
  let F : ELVOld.hom D Sc cutoff v w →ₗ[k]
      ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :=
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).toFunctor.mapLinearMap k
  let G : ELVOld.hom D Sc cutoff (v ++ σ) (w ++ σ) →ₗ[k]
      ((pres D Sc).obj (ob D (v ++ σ)) ⟶ (pres D Sc).obj (ob D (w ++ σ))) :=
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).toFunctor.mapLinearMap k
  change G (ELVOld.rightContext D Sc cutoff σ v w f) =
    ELVOld.affineRightContext D Sc σ v w (F f)
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => simp only [map_add, hf, hg]
  | tmul a f =>
    change (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (BoxProd.tmulHom
        (X := ELVOld.obj D Sc cutoff (v ++ σ))
        (Y := ELVOld.obj D Sc cutoff (w ++ σ))
        (SuperalgebraCat.ofElem a) (ELVOld.affineRightContext D Sc σ v w f)) =
      ELVOld.affineRightContext D Sc σ v w
        ((elvAffineScalarSpecialization D Sc cutoff values hvalues).map
          (BoxProd.tmulHom
            (X := ELVOld.obj D Sc cutoff v) (Y := ELVOld.obj D Sc cutoff w)
            (SuperalgebraCat.ofElem a) f))
    rw [elvAffineScalarSpecialization_tmul, elvAffineScalarSpecialization_tmul]
    exact (map_smul (ELVOld.affineRightContext D Sc σ v w) _ _).symm

end OddMath.QuiverHecke
