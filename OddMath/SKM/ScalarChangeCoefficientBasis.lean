/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ScalarChangeBubbleFamily
import OddMath.SKM.BubbleCoefficientGenerators

/-!
# Coefficient change preserves the polynomial/exterior coefficient basis

`GroundRingDescent.md` §7, item 3, supporting Brundan–Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, (1.21)–(1.22) and §8. Every basis vector of
`SYM.coefficientBasis` is an ordered product of elementary generators `e i r`
and odd generators `δ_i`, in an order that does not depend on the coefficient
ring (`coefficientBasis_eq_prod`). Hence the coefficient change `symMap f`
sends the basis over `R` to the basis over `S` with the same index
(`symMap_coefficientBasis`), and acts on coordinates by applying `f`
(`repr_symMap`). Exterior generators are retained; no even quotient is taken.
-/

noncomputable section
open scoped Classical TensorProduct

namespace OddMath.SKM.SYM

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)

/-- The odd colours of a finite set, listed in the fixed well-order used by
`oddExteriorBasis`. The list does not depend on any coefficient ring. -/
def oddOrdered (s : Finset {i : I // D.parity i = 1}) :
    Fin s.card → {i : I // D.parity i = 1} := by
  letI : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  exact Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (rfl : s.card = s.card))

variable (k : Type w) [CommRing k]

/-- An exterior basis vector is the ordered product of its odd generators. -/
theorem oddExteriorBasis_eq_prod (s : Finset {i : I // D.parity i = 1}) :
    oddExteriorBasis D k s =
      (List.ofFn fun j : Fin s.card =>
        ExteriorAlgebra.ι k (Finsupp.single (oddOrdered D s j) (1 : k))).prod := by
  letI : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  let b : Module.Basis _ k (OddModule D k) := Finsupp.basisSingleOne
  change b.ExteriorAlgebra s = _
  rw [ExteriorAlgebra.basis_apply_ofCard b (rfl : s.card = s.card)]
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply, b, oddOrdered]

/-- A coefficient basis vector is a product of elementary powers followed by
an ordered product of odd generators. -/
theorem coefficientBasis_eq_prod (a : CoefficientIndex D) :
    coefficientBasis D k a =
      (a.1.prod fun x n => e D k x.1 x.2 ^ n) *
        (List.ofFn fun j : Fin a.2.card => delta D k (oddOrdered D a.2 j)).prod := by
  let E := (polynomialExteriorEquiv D k).symm.toAlgHom
  let φ : MvPolynomial (I × ℕ) k →ₐ[k] SYM D k :=
    E.comp Algebra.TensorProduct.includeLeft
  let ψ : ExteriorAlgebra k (OddModule D k) →ₐ[k] SYM D k :=
    E.comp Algebra.TensorProduct.includeRight
  have hφ : φ = MvPolynomial.aeval fun x => e D k x.1 x.2 := by
    apply MvPolynomial.algHom_ext
    intro x
    apply (polynomialExteriorEquiv D k).injective
    simp [φ, E, polynomialExteriorEquiv]
  have hψ (i : {i : I // D.parity i = 1}) :
      ψ (ExteriorAlgebra.ι k (Finsupp.single i 1)) = delta D k i := by
    apply (polynomialExteriorEquiv D k).injective
    simp [ψ, E, polynomialExteriorEquiv]
  have hsplit : coefficientBasis D k a =
      φ (MvPolynomial.monomial a.1 1) * ψ (oddExteriorBasis D k a.2) := by
    apply (polynomialExteriorEquiv D k).injective
    rw [coefficientBasis_projection, map_mul]
    simp [φ, ψ, E, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hsplit, hφ, MvPolynomial.aeval_monomial, map_one, one_mul,
    oddExteriorBasis_eq_prod, map_list_prod, List.map_ofFn]
  congr 2
  funext j
  exact hψ _

end OddMath.SKM.SYM

namespace OddMath.SKM.ScalarChange

universe u v w w'
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {R : Type w} {S : Type w'} [CommRing R] [CommRing S] (f : R →+* S)

/-- Coefficient change sends each coefficient basis vector to the basis vector
with the same index, including all exterior monomials. -/
@[simp] theorem symMap_coefficientBasis (a : SYM.CoefficientIndex D) :
    symMap (D := D) f (SYM.coefficientBasis D R a) = SYM.coefficientBasis D S a := by
  rw [SYM.coefficientBasis_eq_prod, SYM.coefficientBasis_eq_prod, map_mul,
    map_list_prod, List.map_ofFn, Finsupp.prod, Finsupp.prod, map_prod]
  simp only [map_pow, symMap_e]
  congr 2
  funext j
  exact symMap_delta f _

/-- Coefficient change acts on basis coordinates by the ring map itself. -/
theorem repr_symMap (x : SYM D R) (a : SYM.CoefficientIndex D) :
    (SYM.coefficientBasis D S).repr (symMap (D := D) f x) a =
      f ((SYM.coefficientBasis D R).repr x a) := by
  conv_lhs => rw [← (SYM.coefficientBasis D R).sum_repr x]
  rw [map_sum]
  have hterm (b : SYM.CoefficientIndex D) :
      symMap (D := D) f ((SYM.coefficientBasis D R).repr x b • SYM.coefficientBasis D R b) =
        f ((SYM.coefficientBasis D R).repr x b) • SYM.coefficientBasis D S b := by
    rw [Algebra.smul_def, map_mul, symMap_algebraMap, symMap_coefficientBasis,
      ← Algebra.smul_def]
  simp only [hterm, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.mp h, map_zero]

/-- A coefficient that vanishes under a family of ring maps jointly detecting
zero in `R` is itself zero. -/
theorem eq_zero_of_symMap_eq_zero {J : Type*} {K : J → Type w'} [∀ j, CommRing (K j)]
    (g : ∀ j, R →+* K j) (hg : ∀ r : R, (∀ j, g j r = 0) → r = 0)
    (x : SYM D R) (hx : ∀ j, symMap (D := D) (g j) x = 0) : x = 0 := by
  apply (SYM.coefficientBasis D R).ext_elem
  intro a
  rw [map_zero, Finsupp.zero_apply]
  apply hg
  intro j
  rw [← repr_symMap, hx j, map_zero, Finsupp.zero_apply]

end OddMath.SKM.ScalarChange
