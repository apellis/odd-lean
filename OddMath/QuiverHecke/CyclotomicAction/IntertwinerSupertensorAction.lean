/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerSkewAction
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.Algebra.Ring.TransferInstance

/-!
# Scalar-balanced polynomial supertensor actions

The polynomial supertensor in KKO I, arXiv:1206.5933v2, Proposition 8.4.
The scalar-balanced tensor product is identified linearly with the parity-skew
polynomial ring by sending `t^m ⊗ c` to `φ^m(c) X^m`. Transported multiplication
has the Koszul sign `(-1)^(s p(i) q)` on `(t^r ⊗ b)(t^s ⊗ c)` for homogeneous
`b` of parity `q`. Associativity is inherited from the skew ring, with all
natural powers retained. The induced quotient carriers and target shift are unchanged.

`polynomialSupertensorRing` is a named structure, not a global instance.
Its `Mul` and `NonAssocSemiring` projections are selected explicitly where used:
Mathlib's ordinary tensor-product instances would otherwise select unsigned
multiplication. No instances are disabled. This supplies the balanced ring
comparison and actions, not the graded-supermodule packaging of Proposition 8.4.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

/-- The parity twist is linear over the purely even ground ring. -/
def coefficientParityLinear (p : ZMod 2) :
    CyclotomicAlgebra D Sc a n →ₗ[k] CyclotomicAlgebra D Sc a n :=
  (cyclotomicSuperspace D Sc a ha n).sgn p

@[simp] theorem coefficientParityLinear_twice (p : ZMod 2)
    (c : CyclotomicAlgebra D Sc a n) :
    coefficientParityLinear D Sc a ha n p (coefficientParityLinear D Sc a ha n p c) = c :=
  SVec.sgn_sgn_apply _ _ _

private def orderMap : (ℕ →₀ CyclotomicAlgebra D Sc a n) →ₗ[k]
    _root_.SkewPolynomial (CyclotomicAlgebra D Sc a n) :=
  Finsupp.lsum k fun m =>
    ((_root_.SkewPolynomial.monomial m).restrictScalars k).comp
      (coefficientParityLinear D Sc a ha n ((m : ZMod 2) * D.parity i))

private def unorderMap : _root_.SkewPolynomial (CyclotomicAlgebra D Sc a n) →ₗ[k]
    (ℕ →₀ CyclotomicAlgebra D Sc a n) :=
  (Finsupp.lsum k fun m : Multiplicative ℕ =>
    (Finsupp.lsingle m.toAdd).comp
      (coefficientParityLinear D Sc a ha n ((m.toAdd : ZMod 2) * D.parity i))).comp
        SkewMonoidAlgebra.coeffLinearEquiv.toLinearMap

private theorem orderMap_single (m : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    orderMap D Sc i a ha n (Finsupp.single m c) =
      _root_.SkewPolynomial.monomial m
        (coefficientParityLinear D Sc a ha n ((m : ZMod 2) * D.parity i) c) := by
  simp [orderMap]

private theorem unorderMap_monomial (m : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    unorderMap D Sc i a ha n (_root_.SkewPolynomial.monomial m c) =
      Finsupp.single m
        (coefficientParityLinear D Sc a ha n ((m : ZMod 2) * D.parity i) c) := by
  change (Finsupp.lsum k fun m : Multiplicative ℕ =>
    (Finsupp.lsingle m.toAdd).comp
      (coefficientParityLinear D Sc a ha n ((m.toAdd : ZMod 2) * D.parity i)))
        (Finsupp.single (Multiplicative.ofAdd m) c) = _
  simp

/-- Conversion from dot-first finite coefficients to coefficient-first skew polynomials. -/
def polynomialOrderEquiv : (ℕ →₀ CyclotomicAlgebra D Sc a n) ≃ₗ[k]
    _root_.SkewPolynomial (CyclotomicAlgebra D Sc a n) :=
  LinearEquiv.ofLinearMap (orderMap D Sc i a ha n) (unorderMap D Sc i a ha n)
    (by
      apply LinearMap.ext
      intro f
      induction f using SkewMonoidAlgebra.induction_on with
      | zero => simp
      | single m c =>
        change orderMap D Sc i a ha n (unorderMap D Sc i a ha n
          (_root_.SkewPolynomial.monomial m.toAdd c)) = _
        rw [unorderMap_monomial, orderMap_single, coefficientParityLinear_twice]
        rfl
      | add f g hf hg => simpa only [map_add] using congrArg₂ (· + ·) hf hg)
    (by
      apply LinearMap.ext
      intro f
      induction f using Finsupp.induction_linear with
      | zero => simp
      | single m c =>
        change unorderMap D Sc i a ha n (orderMap D Sc i a ha n (Finsupp.single m c)) = _
        simp [orderMap_single, unorderMap_monomial]
      | add f g hf hg => simpa only [map_add] using congrArg₂ (· + ·) hf hg)

/-- Scalar-balanced normal order; the variable is first in the tensor product. -/
def polynomialTensorSkewEquiv :
    (_root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) ≃ₗ[k]
      _root_.SkewPolynomial (CyclotomicAlgebra D Sc a n) :=
  ((PolynomialModule.polynomialTensorProductLEquivPolynomialModule k
    (CyclotomicAlgebra D Sc a n)).restrictScalars k).trans
      ((PolynomialModule.coeffLinearEquiv k k).trans (polynomialOrderEquiv D Sc i a ha n))

/-- The balanced comparison sends a pure tensor to its twisted normal form. -/
theorem polynomialTensorSkewEquiv_tmul (m : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    polynomialTensorSkewEquiv D Sc i a ha n
      (((_root_.Polynomial.X : _root_.Polynomial k) ^ m) ⊗ₜ[k] c) =
      _root_.SkewPolynomial.monomial m
        (coefficientParityHom D Sc a ha n ((m : ZMod 2) * D.parity i) c) := by
  simp [polynomialTensorSkewEquiv, PolynomialModule.polynomialTensorProductLEquivPolynomialModule,
    ← Polynomial.monomial_one_right_eq_X_pow, PolynomialModule.coeffLinearEquiv,
    polynomialOrderEquiv, PolynomialModule.lsingle, orderMap_single, coefficientParityHom,
    coefficientParityLinear]
  rfl

/-- The normal-order comparison has the inverse required by dot-first tensors. -/
theorem polynomialTensorSkewEquiv_symm_monomial (m : ℕ)
    (c : CyclotomicAlgebra D Sc a n) :
    (polynomialTensorSkewEquiv D Sc i a ha n).symm (_root_.SkewPolynomial.monomial m c) =
      ((_root_.Polynomial.X : _root_.Polynomial k) ^ m) ⊗ₜ[k]
        (coefficientParityHom D Sc a ha n ((m : ZMod 2) * D.parity i) c) := by
  apply (polynomialTensorSkewEquiv D Sc i a ha n).injective
  rw [LinearEquiv.apply_symm_apply, polynomialTensorSkewEquiv_tmul]
  change _ = _root_.SkewPolynomial.monomial m
    (coefficientParityLinear D Sc a ha n _ (coefficientParityLinear D Sc a ha n _ c))
  rw [coefficientParityLinear_twice]

private abbrev linearEquivRing {R A B : Type*} [CommRing R] [AddCommGroup A]
    [Ring B] [Module R A] [Module R B] (e : A ≃ₗ[R] B) : Ring A := by
  letI : Mul A := ⟨fun f g => e.symm (e f * e g)⟩
  letI : One A := ⟨e.symm 1⟩
  letI : Pow A ℕ := ⟨fun f m => e.symm (e f ^ m)⟩
  letI : NatCast A := ⟨fun m => e.symm m⟩
  letI : IntCast A := ⟨fun m => e.symm m⟩
  exact Function.Injective.ring e e.injective e.map_zero (e.apply_symm_apply 1) e.map_add
    (fun _ _ => e.apply_symm_apply _) e.map_neg e.map_sub
    (fun m f => map_nsmul e m f) (fun m f => map_zsmul e m f)
    (fun _ _ => e.apply_symm_apply _) (fun _ => e.apply_symm_apply _)
    (fun _ => e.apply_symm_apply _)

private def linearEquivRingEquiv {R A B : Type*} [CommRing R] [AddCommGroup A]
    [Ring B] [Module R A] [Module R B] (e : A ≃ₗ[R] B) :
    letI := linearEquivRing e
    A ≃+* B := by
  letI := linearEquivRing e
  exact { e.toAddEquiv with map_mul' := fun _ _ => e.apply_symm_apply _ }

private def linearEquivRingHom {R A B C : Type*} [CommRing R] [AddCommGroup A]
    [Ring B] [Ring C] [Module R A] [Module R B] (e : A ≃ₗ[R] B) (f : B →+* C) :
    letI := linearEquivRing e
    A →+* C := by
  letI := linearEquivRing e
  exact f.comp (linearEquivRingEquiv e).toRingHom

private theorem linearEquivRing_mul {R A B : Type*} [CommRing R] [AddCommGroup A]
    [Ring B] [Module R A] [Module R B] (e : A ≃ₗ[R] B) (f g : A) :
    letI := linearEquivRing e
    e (f * g) = e f * e g := e.apply_symm_apply _

/-- Super multiplication on the scalar-balanced tensor product. This named structure
is used locally, never as the ordinary tensor-product ring instance. -/
@[instance_reducible] def polynomialSupertensorRing :
    Ring (_root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) := by
  letI := coefficientParityAction D Sc i a ha n
  exact linearEquivRing (polynomialTensorSkewEquiv D Sc i a ha n)

/-- The scalar-balanced supertensor ring is the parity-skew polynomial ring. -/
def polynomialSupertensorSkewRingEquiv :
    letI := coefficientParityAction D Sc i a ha n
    letI := polynomialSupertensorRing D Sc i a ha n
    letI : Mul (_root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) :=
      (polynomialSupertensorRing D Sc i a ha n).toMul
    (_root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) ≃+*
      _root_.SkewPolynomial (CyclotomicAlgebra D Sc a n) := by
  letI := coefficientParityAction D Sc i a ha n
  letI := polynomialSupertensorRing D Sc i a ha n
  letI : Mul (_root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) :=
    (polynomialSupertensorRing D Sc i a ha n).toMul
  exact linearEquivRingEquiv (polynomialTensorSkewEquiv D Sc i a ha n)

private theorem parityHom_comp (p q : ZMod 2) (c : CyclotomicAlgebra D Sc a n) :
    coefficientParityHom D Sc a ha n p (coefficientParityHom D Sc a ha n q c) =
      coefficientParityHom D Sc a ha n (p + q) c := by
  change ((cyclotomicSuperspace D Sc a ha n).sgn p).comp
    ((cyclotomicSuperspace D Sc a ha n).sgn q) c = _
  rw [SVec.sgn_comp_sgn]
  rfl

private theorem dotFirst_mul (r s : ℕ) (b c : CyclotomicAlgebra D Sc a n) :
    letI := coefficientParityAction D Sc i a ha n
    _root_.SkewPolynomial.monomial r (coefficientParityHom D Sc a ha n (r * D.parity i) b) *
      _root_.SkewPolynomial.monomial s (coefficientParityHom D Sc a ha n (s * D.parity i) c) =
      _root_.SkewPolynomial.monomial (r + s)
        (coefficientParityHom D Sc a ha n ((r + s : ℕ) * D.parity i)
          (coefficientParityHom D Sc a ha n (s * D.parity i) b * c)) := by
  let := coefficientParityAction D Sc i a ha n
  rw [_root_.SkewPolynomial.monomial_mul_monomial, _root_.SkewPolynomial.φ_iterate_apply,
    coefficientParityAction_smul, (coefficientParityHom D Sc a ha n ((r + s : ℕ) * D.parity i)).map_mul,
    parityHom_comp, parityHom_comp]
  have h : ((r + s : ℕ) : ZMod 2) * D.parity i + s * D.parity i = r * D.parity i := by
    rw [Nat.cast_add, add_mul, add_assoc]
    have hz : s * D.parity i + s * D.parity i = (0 : ZMod 2) := CharTwo.add_self_eq_zero _
    rw [hz, add_zero]
  rw [h, Nat.cast_add, add_mul]

/-- Signed pure-tensor multiplication; no exterior relation is imposed on the variable. -/
theorem polynomialSupertensor_mul_tmul (r s : ℕ) (q : ZMod 2)
    (b c : CyclotomicAlgebra D Sc a n) (hb : b ∈ cyclotomicParity D Sc a ha n q) :
    letI := polynomialSupertensorRing D Sc i a ha n
    letI : Mul (_root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) :=
      (polynomialSupertensorRing D Sc i a ha n).toMul
    (((_root_.Polynomial.X : _root_.Polynomial k) ^ r) ⊗ₜ[k] b) * (((_root_.Polynomial.X : _root_.Polynomial k) ^ s) ⊗ₜ[k] c) =
      sign k ((s : ZMod 2) * D.parity i * q) •
        (((_root_.Polynomial.X : _root_.Polynomial k) ^ (r + s)) ⊗ₜ[k] (b * c)) := by
  let := coefficientParityAction D Sc i a ha n
  let := polynomialSupertensorRing D Sc i a ha n
  let : Mul (_root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) :=
    (polynomialSupertensorRing D Sc i a ha n).toMul
  apply (polynomialTensorSkewEquiv D Sc i a ha n).injective
  rw [linearEquivRing_mul, (polynomialTensorSkewEquiv D Sc i a ha n).map_smul, polynomialTensorSkewEquiv_tmul,
    polynomialTensorSkewEquiv_tmul, polynomialTensorSkewEquiv_tmul, dotFirst_mul]
  have hb' : coefficientParityHom D Sc a ha n ((s : ZMod 2) * D.parity i) b =
      sign k ((s : ZMod 2) * D.parity i * q) • b := by
    exact (SVec.sgn_apply_of_mem _ hb).trans (by rw [mul_comm q])
  rw [hb', smul_mul_assoc]
  change _root_.SkewPolynomial.monomial (r + s)
    (coefficientParityLinear D Sc a ha n _ (_ • (b * c))) = _
  rw [(coefficientParityLinear D Sc a ha n _).map_smul, _root_.SkewPolynomial.smul_monomial]
  rfl

/-- The transported unit is the tensor of the two units. -/
theorem polynomialSupertensor_one :
    (polynomialSupertensorRing D Sc i a ha n).one =
      (1 : _root_.Polynomial k) ⊗ₜ[k] (1 : CyclotomicAlgebra D Sc a n) := by
  change (polynomialTensorSkewEquiv D Sc i a ha n).symm
    (_root_.SkewPolynomial.monomial 0 1) = _
  rw [polynomialTensorSkewEquiv_symm_monomial, map_one, pow_zero]

/-- The balanced polynomial supertensor acts on the unchanged source quotient. -/
def sourceRightSupertensor :
    letI : NonAssocSemiring (_root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) :=
      (polynomialSupertensorRing D Sc i a ha n).toNonAssocSemiring
    (_root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) →+*
      (Module.End k (qSourceSpace D Sc i a ha n))ᵐᵒᵖ := by
  letI := coefficientParityAction D Sc i a ha n
  letI : NonAssocSemiring (_root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) :=
    (polynomialSupertensorRing D Sc i a ha n).toNonAssocSemiring
  exact linearEquivRingHom (polynomialTensorSkewEquiv D Sc i a ha n)
    (sourceRightSkew D Sc i a ha n)

/-- The balanced polynomial supertensor acts on the unchanged shifted target. -/
def targetRightSupertensor (β : Multiset I) :
    letI : NonAssocSemiring (_root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) :=
      (polynomialSupertensorRing D Sc i a ha n).toNonAssocSemiring
    (_root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) →+*
      (Module.End k (qTargetSpace D Sc i β a ha n))ᵐᵒᵖ := by
  letI := coefficientParityAction D Sc i a ha n
  letI : NonAssocSemiring (_root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) :=
    (polynomialSupertensorRing D Sc i a ha n).toNonAssocSemiring
  exact linearEquivRingHom (polynomialTensorSkewEquiv D Sc i a ha n)
    (targetRightSkew D Sc i β a ha n)

/-- Pure tensors act in dot-first order on the source. -/
theorem sourceRightSupertensor_tmul (m : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    (sourceRightSupertensor D Sc i a ha n
      (((_root_.Polynomial.X : _root_.Polynomial k) ^ m) ⊗ₜ[k] c)).unop =
      sourceRightMonomial D Sc i a ha n m c := by
  change (sourceRightSkew D Sc i a ha n (polynomialTensorSkewEquiv D Sc i a ha n _)).unop = _
  rw [polynomialTensorSkewEquiv_tmul, sourceRightSkew_dotFirst]

/-- Pure tensors act in dot-first order on the shifted target. -/
theorem targetRightSupertensor_tmul (β : Multiset I) (m : ℕ)
    (c : CyclotomicAlgebra D Sc a n) :
    (targetRightSupertensor D Sc i a ha n β
      (((_root_.Polynomial.X : _root_.Polynomial k) ^ m) ⊗ₜ[k] c)).unop =
      targetRightMonomial D Sc i β a ha n m c := by
  change (targetRightSkew D Sc i β a ha n (polynomialTensorSkewEquiv D Sc i a ha n _)).unop = _
  rw [polynomialTensorSkewEquiv_tmul, targetRightSkew_dotFirst]

/-- Q is equivariant for every scalar-balanced supertensor, with the target shift retained. -/
theorem rightSupertensor_Q (β : Multiset I)
    (f : _root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) :
    (targetRightSupertensor D Sc i a ha n β f).unop.comp
        (parityCyclotomicContentQLinear D Sc i β a ha n) =
      (parityCyclotomicContentQLinear D Sc i β a ha n).comp
        (sourceRightSupertensor D Sc i a ha n f).unop :=
  rightSkew_Q D Sc i β a ha n (polynomialTensorSkewEquiv D Sc i a ha n f)

end OddMath.QuiverHecke
