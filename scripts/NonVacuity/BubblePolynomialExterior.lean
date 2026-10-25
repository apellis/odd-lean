import OddMath.SKM.BubblePolynomialExterior

noncomputable section
open OddMath.SKM
open scoped TensorProduct
variable {I X k : Type} [AddCommGroup X] [CommRing k] (D : Datum I X)

/-- The full presentation retains an elementary generator multiplied by two odd generators. -/
example (a : I) (r : ℕ) (i j : {i : I // D.parity i = 1}) :
    SYM.polynomialExteriorEquiv D k
      (SYM.e D k a r * (SYM.delta D k i * SYM.delta D k j)) =
      MvPolynomial.X (a, r) ⊗ₜ[k]
        (ExteriorAlgebra.ι k (Finsupp.single i 1 : SYM.OddModule D k) *
          ExteriorAlgebra.ι k (Finsupp.single j 1 : SYM.OddModule D k)) := by
  change SYM.polynomialExteriorProjection D k _ = _
  simp [Algebra.TensorProduct.tmul_mul_tmul]

#print axioms SYM.polynomialExteriorInclude_comp_projection
#print axioms SYM.polynomialExteriorProjection_comp_include
#print axioms SYM.polynomialExteriorEquiv
