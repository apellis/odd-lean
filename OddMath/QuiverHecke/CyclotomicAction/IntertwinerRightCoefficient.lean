/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerDotGrading

/-!
# Right cyclotomic coefficients on the moving-strand quotients

The coefficient portion of KKO I, arXiv:1206.5933v2, Proposition 8.4.
Right multiplication descends on the existing integral balanced quotients.
The target uses the right action of the parity-shifted regular superbimodule;
its canonical insertion is right-linear without an additional sign.
Composition of right operators reverses multiplication. The dot/coefficient
relation is the supertensor relation, not square-zero for an odd variable.
The finite-colour, positive-height and polynomial-parity restrictions remain;
this does not assert the full content-corner statement of Proposition 8.4.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Right multiplication commutes with the affine action on the coefficient quotient. -/
def sourceCoefficientRight (a : I → _root_.Polynomial k) (n : ℕ)
    (c : CyclotomicAlgebra D Sc a n) :
    Module.End (Hn D Sc (n + 1)) (CyclotomicAlgebra D Sc a n) where
  toFun b := b * c
  map_add' b b' := add_mul b b' c
  map_smul' r b := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact congrArg (cyclotomicMk D Sc a n) (mul_assoc r b c)

/-- The shifted coefficient right action still commutes with its twisted left action. -/
def targetCoefficientRight (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    Module.End (Hn D Sc (n + 1)) (qCoefficient D Sc i β a ha n).toSVec where
  toFun := (qCoefficient D Sc i β a ha n).ract c
  map_add' := SVec.hom_map_add _
  map_smul' r b := congrArg (fun f => f b)
    ((qCoefficient D Sc i β a ha n).lact_ract (cyclotomicMk D Sc a n r) c)

/-- No right-action sign is inserted by the canonical parity shift. -/
theorem qCoefficientInsert_mul (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (b c : CyclotomicAlgebra D Sc a n) :
    qCoefficientInsert D Sc i β a ha n (b * c) =
      (qCoefficient D Sc i β a ha n).ract c (qCoefficientInsert D Sc i β a ha n b) := by
  exact congrArg (fun f => f b)
    ((Envelope.ζPow k (D.parity i * contentSumParity D β)
      (SuperBimodule.regular (cyclotomicParity D Sc a ha n))).inv.2.2 c)

/-- Descended coefficient multiplication on the source quotient. -/
def sourceRightCoefficient (i : I) (a : I → _root_.Polynomial k) (n : ℕ)
    (c : CyclotomicAlgebra D Sc a n) :=
  InductionAlong.Ind.map (φ := (appendAlgebra D Sc i (n + 1) :
    Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) (sourceCoefficientRight D Sc a n c)

/-- Descended shifted right action on the target quotient. -/
def targetRightCoefficient (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (c : CyclotomicAlgebra D Sc a n) :=
  InductionAlong.Ind.map (φ := (prependAlgebra D Sc i (n + 1) :
    Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) (targetCoefficientRight D Sc i β a ha n c)

@[simp] theorem sourceRightCoefficient_tmul (i : I) (a : I → _root_.Polynomial k) (n : ℕ)
    (c : CyclotomicAlgebra D Sc a n)
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) (b : CyclotomicAlgebra D Sc a n) :
    sourceRightCoefficient D Sc i a n c (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul x (b * c) := rfl

@[simp] theorem targetRightCoefficient_tmul (i : I) (β : Multiset I)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (c : CyclotomicAlgebra D Sc a n)
    (x : InductionAlong.Corner (prependAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : (qCoefficient D Sc i β a ha n).toSVec) :
    targetRightCoefficient D Sc i β a ha n c (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul x ((qCoefficient D Sc i β a ha n).ract c b) := rfl

/-- Q is right-linear for every cyclotomic coefficient on the induced quotients. -/
theorem rightCoefficient_Q (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    (targetRightCoefficient D Sc i β a ha n c).comp (parityCyclotomicContentQ D Sc i β a ha n) =
      (parityCyclotomicContentQ D Sc i β a ha n).comp (sourceRightCoefficient D Sc i a n c) := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x b => simp only [LinearMap.comp_apply, parityCyclotomicContentQ_tmul,
      sourceRightCoefficient_tmul, targetRightCoefficient_tmul, qCoefficientInsert_mul]

/-- The descended right action satisfies the one law. -/
theorem sourceRightCoefficient_one (i : I) (a : I → _root_.Polynomial k)
    (n : ℕ) :
    sourceRightCoefficient D Sc i a n 1 = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x d => simp only [LinearMap.id_apply,
      sourceRightCoefficient_tmul, mul_one]

/-- The descended right action satisfies the mul law. -/
theorem sourceRightCoefficient_mul (i : I) (a : I → _root_.Polynomial k)
    (n : ℕ) (b c : CyclotomicAlgebra D Sc a n) :
    sourceRightCoefficient D Sc i a n (b * c) =
      (sourceRightCoefficient D Sc i a n c).comp (sourceRightCoefficient D Sc i a n b) := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x d => simp only [LinearMap.comp_apply,
      sourceRightCoefficient_tmul, mul_assoc]

/-- The descended right action satisfies the one law. -/
theorem targetRightCoefficient_one (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    targetRightCoefficient D Sc i β a ha n 1 = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x d => simp only [LinearMap.id_apply,
      targetRightCoefficient_tmul, SuperBimodule.ract_one, SVec.id_apply]

/-- The descended right action satisfies the mul law. -/
theorem targetRightCoefficient_mul (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (b c : CyclotomicAlgebra D Sc a n) :
    targetRightCoefficient D Sc i β a ha n (b * c) =
      (targetRightCoefficient D Sc i β a ha n c).comp (targetRightCoefficient D Sc i β a ha n b) := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x d => simp only [LinearMap.comp_apply,
      targetRightCoefficient_tmul, SuperBimodule.ract_mul, SVec.comp_apply]

/-- Scalar restriction of the existing source right coefficient action. -/
def sourceRightCoefficientLinear (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    qSourceSpace D Sc i a ha n →ₗ[k] qSourceSpace D Sc i a ha n :=
    letI : Module k (InductionAlong.Ind (CyclotomicAlgebra D Sc a n)
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
      inferInstanceAs (Module k (qSourceSpace D Sc i a ha n))
    letI : IsScalarTower k (Hn D Sc (n + 1 + 1))
      (InductionAlong.Ind (CyclotomicAlgebra D Sc a n)
        (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
      inferInstanceAs (IsScalarTower k (Hn D Sc (n + 1 + 1))
        ((InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
          Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)) ⊗[ℤ] CyclotomicAlgebra D Sc a n) ⧸
          BalancedTensor.rel ℤ (Hn D Sc (n + 1 + 1)) (Hn D Sc (n + 1)) _ _))
    (sourceRightCoefficient D Sc i a n c).restrictScalars k

/-- Scalar restriction of the existing target right coefficient action. -/
def targetRightCoefficientLinear (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    qTargetSpace D Sc i β a ha n →ₗ[k] qTargetSpace D Sc i β a ha n :=
    letI : Module k (InductionAlong.Ind (qCoefficient D Sc i β a ha n).toSVec
      (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
      inferInstanceAs (Module k (qTargetSpace D Sc i β a ha n))
    letI : IsScalarTower k (Hn D Sc (n + 1 + 1))
      (InductionAlong.Ind (qCoefficient D Sc i β a ha n).toSVec
        (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
      inferInstanceAs (IsScalarTower k (Hn D Sc (n + 1 + 1))
        ((InductionAlong.Corner (prependAlgebra D Sc i (n + 1) :
          Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)) ⊗[ℤ] (qCoefficient D Sc i β a ha n).toSVec) ⧸
          BalancedTensor.rel ℤ (Hn D Sc (n + 1 + 1)) (Hn D Sc (n + 1)) _ _))
    (targetRightCoefficient D Sc i β a ha n c).restrictScalars k


/-- A homogeneous coefficient acts with its own degree on the source. -/
theorem sourceRightCoefficient_parity (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (q : ZMod 2)
    (c : CyclotomicAlgebra D Sc a n) (hc : c ∈ cyclotomicParity D Sc a ha n q) :
    SVec.ofHom (sourceRightCoefficientLinear D Sc i a ha n c) ∈
      SVec.parityHom (qSourceSpace D Sc i a ha n) (qSourceSpace D Sc i a ha n) q := by
  let : Module (Hn D Sc (n + 1)) (cyclotomicSuperspace D Sc a ha n) :=
    inferInstanceAs (Module (Hn D Sc (n + 1)) (CyclotomicAlgebra D Sc a n))
  apply InducedParity.ind_map_mem (cyclotomicSuperspace D Sc a ha n)
    (affineParity D Sc (n + 1)) (affineParity D Sc (n + 1 + 1))
    (appendAlgebra D Sc i (n + 1))
    (fun _ _ h => appendAlgebra_parity D Sc i (n + 1) h)
    (cyclotomicCoefficient_smul_mem D Sc a ha n)
  intro p r x b hx hb
  change InductionAlong.Ind.tmul x ((show CyclotomicAlgebra D Sc a n from b) * c) ∈ _
  simpa only [add_assoc] using qSourceSpace_tmul_mem D Sc i a ha n hx
    (SetLike.GradedMul.mul_mem hb hc)

/-- The shifted right action has the coefficient degree, without an extra shift. -/
theorem targetRightCoefficient_parity (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (q : ZMod 2)
    (c : CyclotomicAlgebra D Sc a n) (hc : c ∈ cyclotomicParity D Sc a ha n q) :
    SVec.ofHom (targetRightCoefficientLinear D Sc i β a ha n c) ∈
      SVec.parityHom (qTargetSpace D Sc i β a ha n) (qTargetSpace D Sc i β a ha n) q := by
  apply InducedParity.ind_map_mem (qCoefficient D Sc i β a ha n).toSVec
    (affineParity D Sc (n + 1)) (affineParity D Sc (n + 1 + 1))
    (prependAlgebra D Sc i (n + 1))
    (fun _ _ h => prependAlgebra_parity D Sc i (n + 1) h)
    (qCoefficient_smul_mem D Sc i β a ha n)
  intro p r x b hx hb
  change InductionAlong.Ind.tmul x ((qCoefficient D Sc i β a ha n).ract c b) ∈ _
  simpa only [add_assoc] using qTargetSpace_tmul_mem D Sc i β a ha n hx
    (SVec.apply_mem_part ((qCoefficient D Sc i β a ha n).ract_mem q c hc) hb)

/-- The coefficient involution produces the supertensor sign on the source. -/
theorem rightDotCoefficient_mul (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (q : ZMod 2)
    (c : CyclotomicAlgebra D Sc a n) (hc : c ∈ cyclotomicParity D Sc a ha n q)
    (b : CyclotomicAlgebra D Sc a n) :
    rightDotCoefficient D Sc i a ha n (b * c) =
      sign k (D.parity i * q) • (rightDotCoefficient D Sc i a ha n b * c) := by
  have h := LinearMap.congr_fun (SVec.sgn_comp_of_mem
    ((SuperBimodule.regular (cyclotomicParity D Sc a ha n)).ract_mem q c hc) (D.parity i)) b
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, mul_comm q (D.parity i)] at h
  convert h using 1 <;> rfl

/-- The same involution identity retains the shifted target right action. -/
theorem targetDotCoefficient_ract (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (q : ZMod 2)
    (c : CyclotomicAlgebra D Sc a n) (hc : c ∈ cyclotomicParity D Sc a ha n q)
    (b : (qCoefficient D Sc i β a ha n).toSVec) :
    (qCoefficient D Sc i β a ha n).toSVec.sgn (D.parity i)
        ((qCoefficient D Sc i β a ha n).ract c b) =
      sign k (D.parity i * q) • (qCoefficient D Sc i β a ha n).ract c
        ((qCoefficient D Sc i β a ha n).toSVec.sgn (D.parity i) b) := by
  have h := LinearMap.congr_fun (SVec.sgn_comp_of_mem
    ((qCoefficient D Sc i β a ha n).ract_mem q c hc) (D.parity i)) b
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, mul_comm q (D.parity i)] at h
  convert h using 1 <;> rfl

/-- Right dot and right coefficient satisfy the supertensor relation on the source quotient.
Here composition applies the coefficient first and the dot second. -/
theorem sourceRightDot_coefficient (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (q : ZMod 2)
    (c : CyclotomicAlgebra D Sc a n) (hc : c ∈ cyclotomicParity D Sc a ha n q) :
    (sourceRightDotLinear D Sc i a ha n).comp (sourceRightCoefficientLinear D Sc i a ha n c) =
      sign k (D.parity i * q) •
        (sourceRightCoefficientLinear D Sc i a ha n c).comp (sourceRightDotLinear D Sc i a ha n) := by
  apply LinearMap.ext
  intro z
  have hcoeff := rightDotCoefficient_mul D Sc i a ha n q c hc
  rcases parity_eq_zero_or_one (D.parity i * q) with he | he
  · simp only [he, sign_zero, one_smul] at hcoeff ⊢
    induction z using InductionAlong.Ind.induction_on with
    | zero => simp
    | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
    | tmul x b =>
      change sourceRightDot D Sc i a ha n (sourceRightCoefficient D Sc i a n c
        (InductionAlong.Ind.tmul x b)) = sourceRightCoefficient D Sc i a n c
        (sourceRightDot D Sc i a ha n (InductionAlong.Ind.tmul x b))
      simp only [sourceRightCoefficient_tmul, sourceRightDot_tmul, hcoeff]
  · simp only [he, sign_one, neg_one_smul] at hcoeff ⊢
    induction z using InductionAlong.Ind.induction_on with
    | zero => simp
    | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
    | tmul x b =>
      change sourceRightDot D Sc i a ha n (sourceRightCoefficient D Sc i a n c
        (InductionAlong.Ind.tmul x b)) = -(sourceRightCoefficient D Sc i a n c
        (sourceRightDot D Sc i a ha n (InductionAlong.Ind.tmul x b)))
      simp only [sourceRightCoefficient_tmul, sourceRightDot_tmul, hcoeff]
      exact BalancedTensor.tmul_neg _ _

/-- Right dot and right coefficient satisfy the supertensor relation on the target quotient.
Here composition applies the coefficient first and the dot second. -/
theorem targetRightDot_coefficient (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (q : ZMod 2)
    (c : CyclotomicAlgebra D Sc a n) (hc : c ∈ cyclotomicParity D Sc a ha n q) :
    (targetRightDotLinear D Sc i β a ha n).comp (targetRightCoefficientLinear D Sc i β a ha n c) =
      sign k (D.parity i * q) •
        (targetRightCoefficientLinear D Sc i β a ha n c).comp (targetRightDotLinear D Sc i β a ha n) := by
  apply LinearMap.ext
  intro z
  have hcoeff := targetDotCoefficient_ract D Sc i β a ha n q c hc
  rcases parity_eq_zero_or_one (D.parity i * q) with he | he
  · simp only [he, sign_zero, one_smul] at hcoeff ⊢
    induction z using InductionAlong.Ind.induction_on with
    | zero => simp
    | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
    | tmul x b =>
      change targetRightDot D Sc i β a ha n (targetRightCoefficient D Sc i β a ha n c
        (InductionAlong.Ind.tmul x b)) = targetRightCoefficient D Sc i β a ha n c
        (targetRightDot D Sc i β a ha n (InductionAlong.Ind.tmul x b))
      simp only [targetRightCoefficient_tmul, targetRightDot_tmul, hcoeff]
  · simp only [he, sign_one, neg_one_smul] at hcoeff ⊢
    induction z using InductionAlong.Ind.induction_on with
    | zero => simp
    | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
    | tmul x b =>
      change targetRightDot D Sc i β a ha n (targetRightCoefficient D Sc i β a ha n c
        (InductionAlong.Ind.tmul x b)) = -(targetRightCoefficient D Sc i β a ha n c
        (targetRightDot D Sc i β a ha n (InductionAlong.Ind.tmul x b)))
      simp only [targetRightCoefficient_tmul, targetRightDot_tmul, hcoeff]
      exact BalancedTensor.tmul_neg _ _


/-- Additive coefficient law for the descended source action. -/
theorem sourceRightCoefficient_zero (i : I) (a : I → _root_.Polynomial k)
    (n : ℕ) :
    sourceRightCoefficient D Sc i a n 0 = 0 := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x d => simp only [LinearMap.zero_apply,
      sourceRightCoefficient_tmul, mul_zero, InductionAlong.Ind.tmul_zero]

/-- Additive coefficient law for the descended source action. -/
theorem sourceRightCoefficient_add (i : I) (a : I → _root_.Polynomial k)
    (n : ℕ) (b c : CyclotomicAlgebra D Sc a n) :
    sourceRightCoefficient D Sc i a n (b + c) =
      sourceRightCoefficient D Sc i a n b + sourceRightCoefficient D Sc i a n c := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x d => simp only [LinearMap.add_apply,
      sourceRightCoefficient_tmul, mul_add, InductionAlong.Ind.tmul_add]

/-- Additive coefficient law for the descended target action. -/
theorem targetRightCoefficient_zero (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    targetRightCoefficient D Sc i β a ha n 0 = 0 := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x d => simp only [LinearMap.zero_apply,
      targetRightCoefficient_tmul, map_zero, SVec.zero_apply, InductionAlong.Ind.tmul_zero]

/-- Additive coefficient law for the descended target action. -/
theorem targetRightCoefficient_add (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (b c : CyclotomicAlgebra D Sc a n) :
    targetRightCoefficient D Sc i β a ha n (b + c) =
      targetRightCoefficient D Sc i β a ha n b + targetRightCoefficient D Sc i β a ha n c := by
  apply LinearMap.ext
  intro z
  induction z using InductionAlong.Ind.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul x d => simp only [LinearMap.add_apply,
      targetRightCoefficient_tmul, map_add, SVec.add_apply, InductionAlong.Ind.tmul_add]

end OddMath.QuiverHecke
