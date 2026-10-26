/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerSupertensorAction
/-!
# Ground-ring compatibility of the right supertensor actions

The source and shifted-target actions preserve the existing ground-ring module
structures on the integral balanced induction quotients. The proof transfers a
scalar through the coefficient balancing relation, then identifies the ambient
algebra action with the scalar action already used by the quotient superspaces.
No quotient carrier or scalar structure is replaced.

This supplies scalar compatibility for the right actions associated to KKO I
Proposition 8.4, not the full proposition, a super-bimodule packaging, a QP
identity, or nonzero action and nondegeneracy assertions.
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
private theorem ind_tmul_smul {R : Type*} {A B : Type u} {N : Type*} [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] (φ : A →ₙₐ[R] B) (r : R)
    (x : InductionAlong.Corner (φ : A →ₙ+* B)) (b : N) :
    InductionAlong.Ind.tmul x (r • b) =
      algebraMap R B r • InductionAlong.Ind.tmul x b := by
  rw [← IsScalarTower.algebraMap_smul A r b, ← InductionAlong.Ind.op_smul_tmul,
    InductionAlong.Ind.smul_tmul]
  congr 1
  apply Subtype.ext
  change x.val * φ (algebraMap R A r) = algebraMap R B r * x.val
  have hx : x.val * φ 1 = x.val := x.property
  rw [Algebra.algebraMap_eq_smul_one, map_smul, mul_smul_comm, hx, Algebra.smul_def]

/-- Scalar coefficients act by the existing scalar multiplication on the source quotient. -/
theorem sourceRightCoefficientLinear_smul (r : k) (c : CyclotomicAlgebra D Sc a n) :
    sourceRightCoefficientLinear D Sc i a ha n (r • c) =
      r • sourceRightCoefficientLinear D Sc i a ha n c := by
  let : Module (Hn D Sc (n + 1)) (cyclotomicSuperspace D Sc a ha n) :=
    inferInstanceAs (Module (Hn D Sc (n + 1)) (CyclotomicAlgebra D Sc a n))
  let : Module k (InductionAlong.Ind (CyclotomicAlgebra D Sc a n)
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
    inferInstanceAs (Module k (qSourceSpace D Sc i a ha n))
  let : IsScalarTower k (Hn D Sc (n + 1 + 1))
      (InductionAlong.Ind (CyclotomicAlgebra D Sc a n)
        (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
    inferInstanceAs (IsScalarTower k (Hn D Sc (n + 1 + 1))
      ((InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
        Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)) ⊗[ℤ] (CyclotomicAlgebra D Sc a n)) ⧸
        BalancedTensor.rel ℤ (Hn D Sc (n + 1 + 1)) (Hn D Sc (n + 1)) _ _))
  ext z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add, smul_add] using congrArg₂ (· + ·) hz hw
  | tmul x b =>
    change CyclotomicAlgebra D Sc a n at b
    change InductionAlong.Ind.tmul x (b * (r • c)) = _
    rw [mul_smul_comm, ind_tmul_smul (appendAlgebra D Sc i (n + 1))]
    rw [IsScalarTower.algebraMap_smul]
    rfl

/-- Scalar coefficients act by the existing scalar multiplication on the shifted target. -/
theorem targetRightCoefficientLinear_smul (β : Multiset I) (r : k)
    (c : CyclotomicAlgebra D Sc a n) :
    targetRightCoefficientLinear D Sc i β a ha n (r • c) =
      r • targetRightCoefficientLinear D Sc i β a ha n c := by
  let := qCoefficientScalarTower D Sc i a ha n β
  let : Module k (InductionAlong.Ind ((qCoefficient D Sc i β a ha n).toSVec)
      (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
    inferInstanceAs (Module k (qTargetSpace D Sc i β a ha n))
  let : IsScalarTower k (Hn D Sc (n + 1 + 1))
      (InductionAlong.Ind ((qCoefficient D Sc i β a ha n).toSVec)
        (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
    inferInstanceAs (IsScalarTower k (Hn D Sc (n + 1 + 1))
      ((InductionAlong.Corner (prependAlgebra D Sc i (n + 1) :
        Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)) ⊗[ℤ] ((qCoefficient D Sc i β a ha n).toSVec)) ⧸
        BalancedTensor.rel ℤ (Hn D Sc (n + 1 + 1)) (Hn D Sc (n + 1)) _ _))
  ext z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add, smul_add] using congrArg₂ (· + ·) hz hw
  | tmul x b =>
    change InductionAlong.Ind.tmul x ((qCoefficient D Sc i β a ha n).ract (r • c) b) = _
    rw [(qCoefficient D Sc i β a ha n).ract.map_smul]
    change InductionAlong.Ind.tmul x (r • (qCoefficient D Sc i β a ha n).ract c b) = _
    rw [ind_tmul_smul (prependAlgebra D Sc i (n + 1))]
    rw [IsScalarTower.algebraMap_smul]
    rfl



/-- Ground-ring scalars pass through the source skew-polynomial action. -/
theorem sourceRightSkew_smul (r : k)
    (f : _root_.SkewPolynomial (CyclotomicAlgebra D Sc a n)) :
    (sourceRightSkew D Sc i a ha n (r • f)).unop =
      r • (sourceRightSkew D Sc i a ha n f).unop := by
  induction f using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single m c =>
    change (sourceRightSkew D Sc i a ha n (r • _root_.SkewPolynomial.monomial m.toAdd c)).unop =
      r • (sourceRightSkew D Sc i a ha n (_root_.SkewPolynomial.monomial m.toAdd c)).unop
    rw [_root_.SkewPolynomial.smul_monomial, sourceRightSkew_monomial,
      sourceRightSkew_monomial, sourceRightCoefficientLinear_smul, mul_smul_comm]
  | add f g hf hg =>
    rw [smul_add, (sourceRightSkew D Sc i a ha n).map_add,
      (sourceRightSkew D Sc i a ha n).map_add]
    simp only [MulOpposite.unop_add, hf, hg, smul_add]

/-- The source right supertensor action preserves the existing ground-ring scalar action. -/
theorem sourceRightSupertensor_smul (r : k)
    (f : _root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) :
    (sourceRightSupertensor D Sc i a ha n (r • f)).unop =
      r • (sourceRightSupertensor D Sc i a ha n f).unop := by
  change (sourceRightSkew D Sc i a ha n (polynomialTensorSkewEquiv D Sc i a ha n (r • f))).unop = _
  rw [(polynomialTensorSkewEquiv D Sc i a ha n).map_smul, sourceRightSkew_smul]
  rfl

/-- Ground-ring scalars pass through the target skew-polynomial action. -/
theorem targetRightSkew_smul (β : Multiset I) (r : k)
    (f : _root_.SkewPolynomial (CyclotomicAlgebra D Sc a n)) :
    (targetRightSkew D Sc i β a ha n (r • f)).unop =
      r • (targetRightSkew D Sc i β a ha n f).unop := by
  induction f using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single m c =>
    change (targetRightSkew D Sc i β a ha n (r • _root_.SkewPolynomial.monomial m.toAdd c)).unop =
      r • (targetRightSkew D Sc i β a ha n (_root_.SkewPolynomial.monomial m.toAdd c)).unop
    rw [_root_.SkewPolynomial.smul_monomial, targetRightSkew_monomial,
      targetRightSkew_monomial, targetRightCoefficientLinear_smul, mul_smul_comm]
  | add f g hf hg =>
    rw [smul_add, (targetRightSkew D Sc i β a ha n).map_add,
      (targetRightSkew D Sc i β a ha n).map_add]
    simp only [MulOpposite.unop_add, hf, hg, smul_add]

/-- The target right supertensor action preserves the existing ground-ring scalar action. -/
theorem targetRightSupertensor_smul (β : Multiset I) (r : k)
    (f : _root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) :
    (targetRightSupertensor D Sc i a ha n β (r • f)).unop =
      r • (targetRightSupertensor D Sc i a ha n β f).unop := by
  change (targetRightSkew D Sc i β a ha n (polynomialTensorSkewEquiv D Sc i a ha n (r • f))).unop = _
  rw [(polynomialTensorSkewEquiv D Sc i a ha n).map_smul, targetRightSkew_smul]
  rfl

/-- Scalar multiples of Q retain equivariance for the ground-ring-linear right actions. -/
theorem rightSupertensor_scalarQ (β : Multiset I) (r : k)
    (f : _root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) :
    (targetRightSupertensor D Sc i a ha n β f).unop.comp
        (r • parityCyclotomicContentQLinear D Sc i β a ha n) =
      (r • parityCyclotomicContentQLinear D Sc i β a ha n).comp
        (sourceRightSupertensor D Sc i a ha n f).unop := by
  rw [LinearMap.comp_smul, LinearMap.smul_comp, rightSupertensor_Q]

end OddMath.QuiverHecke
