import OddMath.QuiverHecke.CyclotomicCoefficients
import OddMath.SKM.BubbleAlgebra

/-! The abstract full coefficient algebra is retained without specializing odd parameters. -/
noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke OddMath.SKM
open scoped TensorProduct Classical

variable {I X k : Type} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k)

/-- The descended detector returns the entire mixed exterior coefficient. -/
example {t t' : List I} {N : ℕ} (b : NFIdx t t') (ht : 0 < t.length)
    (hb : b.1.1.length + 2 * t.length.choose 2 < N)
    (i j : {i : I // D.parity i = 1}) :
    tensorQuotientCoordinate D Sc (SYM D k) b ht hb
      ((SYM.delta D k i * SYM.delta D k j) ⊗ₜ[k]
        (CyclotomicSpan D Sc t t' N).mkQ b.nf) =
      SYM.delta D k i * SYM.delta D k j := by
  simpa using tensorQuotientCoordinate_nf D Sc (SYM D k) b b ht hb
    (SYM.delta D k i * SYM.delta D k j)

#print axioms quotientCoordinate
#print axioms tensorQuotientCoordinate_nf
#print axioms tensor_cyclotomic_coefficients_eq_zero
#print axioms tensor_cyclotomic_jointly_detects
