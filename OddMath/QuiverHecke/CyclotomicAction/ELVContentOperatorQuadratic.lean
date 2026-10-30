/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentOperatorPolynomial

/-! # The content induction quadratic polynomial

`DeformedActionAssembly.md` §6 (9): the normalized crossing square equals
the ordered polynomial in the two positioned induction dot operators. The
affine source uses `parameterTwist Sc`, while the operator polynomial has
exactly `Sc`. Its powers are reversed relative to End multiplication on the
affine source, without commuting any dots or coefficients.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Evaluation of an appended source endomorphism on a balanced generator. -/
def contentTensorEval {β : Multiset I} {σ : List I}
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    End ((pres D Sc).obj (ob D σ)) →ₗ[k]
      BalancedInduction.Obj (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor w where
  toFun a := BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v
    (contentAppendToLinear D Sc cutoff N rfl rfl v a ≫ h) m
  map_add' a b := by
    simp only [map_add, Preadditive.add_comp, BalancedInduction.tensor, TensorProduct.add_tmul]
  map_smul' c a := by
    simp only [map_smul, Linear.smul_comp, BalancedInduction.tensor,
      ← TensorProduct.smul_tmul']
    rfl

/-- A supported dot power has no residual twist on the input coefficient. -/
theorem contentInductionEndLinear_supported_power {β : Multiset I} {σ : List I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D σ))} (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (n : ℕ) (hn : (n : ZMod 2) * p = 0) (c : k)
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    (c • (contentInductionEndLinear D Sc cutoff N ha M w ^ n))
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
    contentTensorEval D Sc cutoff N M w v h m
      ((SKM.zsign k (p * (n / 2 : ℕ)) * c) • (a ^ n)) := by
  rw [LinearMap.smul_apply, contentInductionEndLinear_pow_tensor, hn, twist_zero,
    map_smul, smul_smul]
  change _ = _ • BalancedInduction.tensor _ M.toFunctor v
    (contentAppendToComponent D Sc cutoff N rfl rfl (a ^ n) v ≫ h) m
  rw [sign_eq_zsign, mul_comm c]

/-- Ordered polynomial: the first-position power acts before the second-position power. -/
def contentInductionPairPolynomial (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I))) :=
  let A := contentInductionEndLinear D (parameterTwist D Sc) cutoff N
    (firstDot_parity D (parameterTwist D Sc) i [j]) M w
  let B := contentInductionEndLinear D (parameterTwist D Sc) cutoff N
    (contentPairDot_one_parity D (parameterTwist D Sc) i j) M w
  if D.d i j = 0 then (Sc.t i j : k) • (1 : Module.End k _) else
    ∑ r ∈ Finset.Ioo 0 (D.dn i j), ∑ s ∈ Finset.Ioo 0 (D.dn j i),
      Sc.s i j r s • (B ^ s * A ^ r) +
    ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i)

/-- The ordered polynomial in the induction dots evaluates to the specified source polynomial. -/
theorem contentInductionPairPolynomial_tensor (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I)))
    (v : ContentCategory D (parameterTwist D Sc) cutoff N β)
    (h : (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl).obj v ⟶ w)
    (m : M.obj v) :
    contentInductionPairPolynomial D Sc cutoff N β i j M w
      (BalancedInduction.tensor (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl)
        M.toFunctor v h m) =
    contentTensorEval D (parameterTwist D Sc) cutoff N M w v h m
      (elvSignedPairQuadEval D Sc (R := End ((pres D (parameterTwist D Sc)).obj (ob D [i,j])))
        i j (dotE D (parameterTwist D Sc) [i,j] 0) (dotE D (parameterTwist D Sc) [i,j] 1)) := by
  unfold contentInductionPairPolynomial elvSignedPairQuadEval
  split_ifs with hd
  · simp [contentTensorEval, contentAppendToLinear_apply, contentAppendToComponent_id]
  · simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      exact contentInduction_dot_monomial D Sc cutoff N β i j r s M w v h m
    · congr 1
      · exact contentInductionEndLinear_supported_power D _ cutoff N _ M w _
          (CyclotomicAction.dn_cast_mul_parity D hij) _ v h m
      · exact contentInductionEndLinear_supported_power D _ cutoff N _ M w _
          (CyclotomicAction.dn_cast_mul_parity D hij.symm) _ v h m

/-- The crossing square equals the ordered polynomial in the induction dot operators. -/
theorem contentInduction_quadratic_linear (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I))) :
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N rfl
        (content_pair_swap β i j) (contentCrossAffine_mem D (parameterTwist D Sc) i j)) M w).comp
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N
          (content_pair_swap β i j) rfl (contentCrossAffine_mem D (parameterTwist D Sc) j i)) M w) =
      contentInductionPairPolynomial D Sc cutoff N β i j M w := by
  apply BalancedInduction.hom_ext
  intro v h m
  rw [LinearMap.comp_apply, contentInductionPairPolynomial_tensor D Sc cutoff N β hij M w v h m]
  exact contentInduction_quadratic_tensor D Sc cutoff N β hij M v w h m

end OddMath.QuiverHecke.ELVOld
