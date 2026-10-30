/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleQuadratic

/-! # Ordered polynomials in content induction operators

`DeformedActionAssembly.md` §5 (8) and §6 (9): powers of the induced dot
operators evaluate on balanced tensors with the total-parity twist. Each
interior coefficient of the specified parameter polynomial is identified
with its ordered source evaluation. The leading terms and the sum forming
the crossing square, and the corrected mixed braid, remain to be assembled.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
namespace BalancedInduction
variable {k : Type u} [CommRing k]
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
variable {J : C ⥤ B} [J.Additive] [J.Linear k] [IsSuperfunctor k J]

private theorem half_succ_parity (n : ℕ) :
    (((n + 1) / 2 : ℕ) : ZMod 2) = (n : ZMod 2) + (n / 2 : ℕ) := by
  have h : (n + 1) / 2 + n / 2 = n := by omega
  have he := congrArg (Nat.cast : ℕ → ZMod 2) h
  push_cast at he
  have hz : (2 : ZMod 2) = 0 := rfl
  linear_combination he - (n / 2 : ℕ) * hz

/-- Powers retain the twist of the entire kernel morphism, including odd coefficients. -/
theorem transformLinear_pow_tensor {p : ZMod 2} {a : ∀ v, End (J.obj v)}
    (ha : IsSupernatural k p a) (M : Superfunctor k C (SVec k))
    (w : B) (n : ℕ) (v : C) (h : J.obj v ⟶ w) (m : M.obj v) :
    (transformLinear ha M w ^ n) (tensor J M.toFunctor v h m) =
      sign k (p * (n / 2 : ℕ)) •
        tensor J M.toFunctor v ((a v ^ n) ≫ twist k ((n : ZMod 2) * p) h) m := by
  induction n generalizing h with
  | zero => simp [twist_zero, sign_zero]
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, transformLinear_tensor, ih, twist_comp,
      twist_of_mem _ (ha.mem v), ← twist_add]
    simp only [Linear.smul_comp, Linear.comp_smul, tensor,
      ← TensorProduct.smul_tmul', map_smul, smul_smul]
    have hp : p * p = p := by
      rcases parity_eq_zero_or_one p with rfl | rfl <;> decide
    rw [← sign_add]
    have he : p * (n / 2 : ℕ) + (n : ZMod 2) * p * p =
        p * ((n + 1) / 2 : ℕ) := by
      rw [half_succ_parity, mul_add, mul_assoc, hp]
      ring
    rw [he]
    congr 2
    rw [pow_succ', End.mul_def, Category.assoc]
    congr 2
    push_cast
    ring
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Append preserves powers without moving any coefficient across a dot. -/
theorem contentAppendToComponent_pow {β : Multiset I} {σ : List I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D σ))} (ha : a ∈ parity (R := k) _ _ p)
    (v : ContentCategory D Sc cutoff N β) (n : ℕ) :
    contentAppendToComponent D Sc cutoff N rfl rfl (a ^ n) v =
      ((show End ((contentAppendTo D Sc cutoff N β σ _ rfl).obj v) from
        contentAppendToComponent D Sc cutoff N rfl rfl a v) ^ n :
        End ((contentAppendTo D Sc cutoff N β σ _ rfl).obj v)) := by
  induction n with
  | zero => exact contentAppendToComponent_id D Sc cutoff N v
  | succ n ih =>
    rw [pow_succ', End.mul_def, ← contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _ ha,
      ih, pow_succ', End.mul_def]

/-- The polynomial powers are powers of the induced linear operator, not source-dot notation. -/
theorem contentInductionEndLinear_pow_tensor {β : Multiset I} {σ : List I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D σ))} (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) (n : ℕ)
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    (contentInductionEndLinear D Sc cutoff N ha M w ^ n)
        (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
      sign k (p * (n / 2 : ℕ)) •
        BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v
          (contentAppendToComponent D Sc cutoff N rfl rfl (a ^ n) v ≫
            twist k ((n : ZMod 2) * p) h) m := by
  rw [contentAppendToComponent_pow D Sc cutoff N ha]
  exact BalancedInduction.transformLinear_pow_tensor _ M w n v h m

theorem contentEnd_pow_parity {σ : List I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D σ))} (ha : a ∈ parity (R := k) _ _ p)
    (n : ℕ) : a ^ n ∈ parity (R := k) _ _ ((n : ZMod 2) * p) := by
  induction n with
  | zero => simpa using id_mem (R := k) ((pres D Sc).obj (ob D σ))
  | succ n ih =>
    rw [pow_succ', End.mul_def]
    simpa [add_mul] using comp_mem ih ha

/-- Ordered powers on admissible support; the second operator acts first. -/
theorem contentInductionEndLinear_ordered_tensor {β : Multiset I} {σ : List I}
    {p q : ZMod 2} {a b : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ q)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) (r s : ℕ)
    (hr : (r : ZMod 2) * p = 0) (hs : (s : ZMod 2) * q = 0)
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionEndLinear D Sc cutoff N ha M w ^ r) *
      (contentInductionEndLinear D Sc cutoff N hb M w ^ s))
        (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
      sign k (p * (r / 2 : ℕ) + q * (s / 2 : ℕ)) •
        BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v
          ((contentAppendToComponent D Sc cutoff N rfl rfl (a ^ r) v ≫
            contentAppendToComponent D Sc cutoff N rfl rfl (b ^ s) v) ≫ h) m := by
  rw [Module.End.mul_apply, contentInductionEndLinear_pow_tensor, map_smul,
    contentInductionEndLinear_pow_tensor, hr, hs, twist_zero, twist_zero,
    smul_smul, ← sign_add, add_comm (q * _) (p * _), Category.assoc]

/-- The second positioned dot on a two-colour block. -/
theorem contentPairDot_one_parity (i j : I) :
    dotE D Sc [i,j] 1 ∈ parity (R := k) _ _ (D.parity j) := by
  simpa using positionedDot_parity D Sc [i] [] j

/-- Each specified interior coefficient acts by the ordered powers of the two
induction dots. No support assumption is added: it follows from `Sc.s_eq_zero`. -/
theorem contentInduction_dot_monomial (β : Multiset I) (i j : I) (r s : ℕ)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I)))
    (v : ContentCategory D (parameterTwist D Sc) cutoff N β)
    (h : (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl).obj v ⟶ w)
    (m : M.obj v) :
    (Sc.s i j r s •
      ((contentInductionEndLinear D (parameterTwist D Sc) cutoff N
          (contentPairDot_one_parity D (parameterTwist D Sc) i j) M w ^ s) *
       (contentInductionEndLinear D (parameterTwist D Sc) cutoff N
          (firstDot_parity D (parameterTwist D Sc) i [j]) M w ^ r)))
      (BalancedInduction.tensor
        (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v h m) =
    BalancedInduction.tensor
      (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v
      (contentAppendToComponent D (parameterTwist D Sc) cutoff N rfl rfl
        ((SKM.zsign k (D.parity i * (r / 2 : ℕ) + D.parity j * (s / 2 : ℕ)) *
          Sc.s i j r s) •
          (dotE D (parameterTwist D Sc) [i,j] 0 ^ r *
           dotE D (parameterTwist D Sc) [i,j] 1 ^ s)) v ≫ h) m := by
  by_cases hc : Sc.s i j r s = 0
  · simp [hc, contentAppendToComponent_zero, BalancedInduction.tensor]
  · obtain ⟨hr, hs⟩ := elvParameter_support D Sc hc
    rw [LinearMap.smul_apply, contentInductionEndLinear_ordered_tensor D _ cutoff N _ _ M w s r hs hr,
      contentAppendToComponent_comp D _ cutoff N rfl rfl rfl _
        (contentEnd_pow_parity D _ (firstDot_parity D _ i [j]) r),
      contentAppendToComponent_smul, Linear.smul_comp]
    simp only [BalancedInduction.tensor, ← TensorProduct.smul_tmul', map_smul, smul_smul,
      ← End.mul_def, sign_eq_zsign]
    rw [add_comm (D.parity j * _) (D.parity i * _), mul_comm (Sc.s i j r s)]

end OddMath.QuiverHecke.ELVOld
