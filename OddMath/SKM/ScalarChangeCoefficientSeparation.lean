/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ScalarChangeBubbleFamily
import OddMath.SKM.BubbleCoefficientBasis

/-!
# Scalar change of coefficient monomials

Brundan–Ellis, *Super Kac–Moody 2-categories*, (1.21)–(1.22).
The full polynomial/exterior basis is preserved by arbitrary scalar maps,
including maps with nonzero kernel. This does not assert injectivity of
bubble evaluation or decorated matching expansions. Coefficientwise joint
separation remains to be proved from this basis formula.
-/
noncomputable section
open scoped Classical TensorProduct
namespace OddMath.SKM.ScalarChange
universe u v w w'
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {R : Type w} {S : Type w'} [CommRing R] [CommRing S] (f : R →+* S)

private theorem polynomial_monomial (m : (I × ℕ) →₀ ℕ) :
    symMap (D := D) f (SYM.polynomialInclude D R (MvPolynomial.monomial m 1)) =
      SYM.polynomialInclude D S (MvPolynomial.monomial m 1) := by
  simp only [MvPolynomial.monic_monomial_eq, Finsupp.prod]
  suffices h : ∀ s : Finset (I × ℕ),
      symMap (D := D) f (SYM.polynomialInclude D R (s.prod fun x => MvPolynomial.X x ^ m x)) =
        SYM.polynomialInclude D S (s.prod fun x => MvPolynomial.X x ^ m x) from h _
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.prod_insert hx, map_mul, map_pow, SYM.polynomialInclude_X,
        symMap_e, ih]

private theorem exterior_basis (s : Finset {i : I // D.parity i = 1}) :
    symMap (D := D) f (SYM.exteriorInclude D R (SYM.oddExteriorBasis D R s)) =
      SYM.exteriorInclude D S (SYM.oddExteriorBasis D S s) := by
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  let bR : Module.Basis _ R (SYM.OddModule D R) := Finsupp.basisSingleOne
  let bS : Module.Basis _ S (SYM.OddModule D S) := Finsupp.basisSingleOne
  rw [show SYM.oddExteriorBasis D R s = bR.ExteriorAlgebra s by rfl,
      show SYM.oddExteriorBasis D S s = bS.ExteriorAlgebra s by rfl]
  rw [ExteriorAlgebra.basis_apply bR, ExteriorAlgebra.basis_apply bS]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    map_list_prod, List.map_ofFn, Function.comp_def]
  simp [bR, bS, SYM.exteriorInclude_ι, SYM.oddLinear_single, symMap_delta]

/-- Scalar change preserves every full coefficient monomial, with the same
well-order fixing signs of products of distinct odd generators. -/
theorem symMap_coefficientBasis (a : SYM.CoefficientIndex D) :
    symMap (D := D) f (SYM.coefficientBasis D R a) =
      SYM.coefficientBasis D S a := by
  apply (SYM.polynomialExteriorEquiv D S).injective
  rw [SYM.coefficientBasis_projection]
  have hR := SYM.coefficientBasis_projection D R a
  have heq : SYM.coefficientBasis D R a =
      SYM.polynomialInclude D R (MvPolynomial.monomial a.1 1) *
        SYM.exteriorInclude D R (SYM.oddExteriorBasis D R a.2) := by
    rw [← SYM.polynomialExteriorInclude_tmul]
    change SYM.coefficientBasis D R a =
      (SYM.polynomialExteriorEquiv D R).symm
        (MvPolynomial.monomial a.1 1 ⊗ₜ[R] SYM.oddExteriorBasis D R a.2)
    rw [← hR, AlgEquiv.symm_apply_apply]
  rw [heq, map_mul, polynomial_monomial, exterior_basis,
    ← SYM.polynomialExteriorInclude_tmul]
  change SYM.polynomialExteriorProjection D S
    (SYM.polynomialExteriorInclude D S _) = _
  exact DFunLike.congr_fun (SYM.polynomialExteriorProjection_comp_include D S) _

end OddMath.SKM.ScalarChange
