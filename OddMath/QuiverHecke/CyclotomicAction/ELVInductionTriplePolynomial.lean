/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionPairPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVTripleCorrectionPolynomial

/-! # Ordered three-dot corrections in arbitrary balanced induction

Brundan–Ellis (1.9): keep the superopposite three-power signs and the
reflection of the correction summation index on arbitrary source/target
categories. No coefficient-power truncation is assumed. The scalar
support and parameter involution retain the original-Sc correction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]

private theorem triple_end_pow_mem {V : E} {p : ZMod 2} {a : End V}
    (ha : a ∈ parity (R := k) _ _ p) (n : ℕ) :
    a ^ n ∈ parity (R := k) _ _ ((n : ZMod 2) * p) := by
  induction n with
  | zero => simpa using id_mem (R := k) V
  | succ n ih =>
    rw [pow_succ', End.mul_def]
    simpa [add_mul] using comp_mem ih ha

/-- Full ordered three-power evaluation, including the twist of every kernel coefficient. -/
theorem transformLinear_three_powers
    {p q t : ZMod 2} {a b c : ∀ s, End (F.obj s)}
    (ha : IsSupernatural k p a) (hb : IsSupernatural k q b) (hc : IsSupernatural k t c)
    (N : Superfunctor k C (SVec k)) (w : E) (l s n : ℕ)
    (v : C) (g : F.obj v ⟶ w) (z : N.obj v) :
    ((transformLinear hc N w ^ n) * (transformLinear hb N w ^ s) *
        (transformLinear ha N w ^ l)) (tensor F N.toFunctor v g z) =
      sign k (p * (l / 2 : ℕ) + q * (s / 2 : ℕ) + t * (n / 2 : ℕ) +
        (s : ZMod 2) * q * ((l : ZMod 2) * p) +
        (n : ZMod 2) * t * ((s : ZMod 2) * q + (l : ZMod 2) * p)) •
      inductionEndTensorEval F N w v
        (twist k ((n : ZMod 2) * t + ((s : ZMod 2) * q + (l : ZMod 2) * p)) g) z
        (a v ^ l * b v ^ s * c v ^ n) := by
  rw [Module.End.mul_apply, Module.End.mul_apply,
    transformLinear_pow_tensor, map_smul, transformLinear_pow_tensor,
    map_smul, map_smul, transformLinear_pow_tensor]
  dsimp only [inductionEndTensorEval, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [twist_comp, twist_of_mem _ (triple_end_pow_mem (ha.mem v) l),
    twist_of_mem _ (triple_end_pow_mem (hb.mem v) s), ← twist_add,
    Linear.smul_comp, Linear.comp_smul, tensor, ← TensorProduct.smul_tmul',
    map_smul, smul_smul, ← sign_add]
  congr 1
  · congr 1
    ring
  congr 2
  simp only [End.mul_def, Category.assoc]

/-- Supported three-power summands reflect to the twisted source coefficient. -/
theorem transformLinear_three_supported
    {p q : ZMod 2} {a b c : ∀ v, End (F.obj v)}
    (ha : IsSupernatural k p a) (hb : IsSupernatural k q b) (hc : IsSupernatural k p c)
    (N : Superfunctor k C (SVec k)) (w : E)
    (r s l : ℕ) (hr : (r : ZMod 2) * p = 0) (hs : (s : ZMod 2) * q = 0)
    (hl : l < r) (d : k) (v : C) (g : F.obj v ⟶ w) (z : N.obj v) :
    ((sign k (p * (q + (l : ZMod 2))) * d) •
      ((transformLinear hc N w ^ (r - 1 - l)) *
        (transformLinear hb N w ^ s) * (transformLinear ha N w ^ l)))
        (tensor F N.toFunctor v g z) =
      sign k (p * q) • inductionEndTensorEval F N w v (twist k p g) z
        ((sign k (p * (q + ((r - 1 - l : ℕ) : ZMod 2))) *
          (sign k (p * q + p * (r / 2 : ℕ) + q * (s / 2 : ℕ)) * d)) •
          (a v ^ l * b v ^ s * c v ^ (r - 1 - l))) := by
  rw [LinearMap.smul_apply, transformLinear_three_powers,
    mixed_braid_total_parity p q r s l hr hs hl, map_smul, smul_smul, smul_smul]
  congr 1
  let n := r - 1 - l
  have hp : p * p = p := by
    rcases parity_eq_zero_or_one p with hp | hp <;> simp [hp]
  have he := mixed_braid_sign_identity p q r s l n hr hs hl rfl
  have hsign : sign k (p * (q + (l : ZMod 2))) *
      sign k (p * (l / 2 : ℕ) + q * (s / 2 : ℕ) + p * (n / 2 : ℕ) +
        (s : ZMod 2) * q * ((l : ZMod 2) * p) +
        (n : ZMod 2) * p * ((s : ZMod 2) * q + (l : ZMod 2) * p)) =
      sign k (p * q) * (sign k (p * (q + (n : ZMod 2))) *
        sign k (p * q + p * (r / 2 : ℕ) + q * (s / 2 : ℕ))) := by
    simp only [← sign_add]
    congr 1
    have hz : (2 : ZMod 2) = 0 := rfl
    linear_combination he + (n : ZMod 2) * (l : ZMod 2) * hp - p * q * hz
  calc
    _ = (sign k (p * (q + (l : ZMod 2))) *
      sign k (p * (l / 2 : ℕ) + q * (s / 2 : ℕ) + p * (n / 2 : ℕ) +
        (s : ZMod 2) * q * ((l : ZMod 2) * p) +
        (n : ZMod 2) * p * ((s : ZMod 2) * q + (l : ZMod 2) * p))) * d := by ring
    _ = _ := by rw [hsign]; ring

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b c : ∀ v, End (F.obj v)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)
  (hc : IsSupernatural k (D.parity i) c)

/-- Reflection of the summation index retains the exact parameter involution. -/
theorem transformLinear_tripleSum_tensor
    (r s : ℕ) (d : k)
    (hd : d ≠ 0 → (r : ZMod 2) * D.parity i = 0 ∧ (s : ZMod 2) * D.parity j = 0)
    (N : Superfunctor k C (SVec k)) (w : E) (v : C) (g : F.obj v ⟶ w) (z : N.obj v) :
    tripleDotCorrectionSum D i j r s d (transformLinear ha N w) (transformLinear hb N w)
        (transformLinear hc N w) (tensor F N.toFunctor v g z) =
      sign k (D.parity i * D.parity j) •
        inductionEndTensorEval F N w v (twist k (D.parity i) g) z
          (tripleDotCorrectionSum D i j r s
            (SKM.zsign k (parameterSignExponent D i j r s) * d) (c v) (b v) (a v)) := by
  by_cases hd0 : d = 0
  · simp [tripleDotCorrectionSum, hd0]
  obtain ⟨hr, hs⟩ := hd hd0
  unfold tripleDotCorrectionSum
  rw [← Finset.sum_range_reflect (fun l =>
    (SKM.zsign k (D.parity i * (D.parity j + l)) *
      (SKM.zsign k (parameterSignExponent D i j r s) * d)) •
      (a v ^ (r - 1 - l) * b v ^ s * c v ^ l)) r]
  simp only [LinearMap.sum_apply, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hl' := Finset.mem_range.mp hl
  have he : r - 1 - (r - 1 - l) = l := by omega
  rw [he]
  simpa only [sign_eq_zsign, parameterSignExponent] using
    transformLinear_three_supported F ha hb hc N w r s l hr hs hl' d v g z

/-- The ordered original-Sc correction is the full parameter-twisted source evaluation. -/
theorem transformLinear_triplePolynomial_tensor (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) (w : E) (v : C) (g : F.obj v ⟶ w) (z : N.obj v) :
    tripleDotCorrectionPolynomial D Sc i j
        (transformLinear ha N w) (transformLinear hb N w) (transformLinear hc N w)
        (tensor F N.toFunctor v g z) =
      sign k (D.parity i * D.parity j) •
        inductionEndTensorEval F N w v (twist k (D.parity i) g) z
          (tripleDotCorrectionPolynomial D (parameterTwist D Sc) i j (c v) (b v) (a v)) := by
  have ht := transformLinear_tripleSum_tensor F D i j ha hb hc (D.dn i j) 0 (Sc.t i j : k)
    (fun _ => ⟨CyclotomicAction.dn_cast_mul_parity D hij, by simp⟩) N w v g z
  have hs (r s : ℕ) := transformLinear_tripleSum_tensor F D i j ha hb hc
    r s (Sc.s i j r s) (fun hz => elvParameter_support D Sc hz) N w v g z
  unfold tripleDotCorrectionPolynomial
  simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum, smul_add,
    Finset.smul_sum, ht, hs, CyclotomicAction.parameterTwist_t_of_ne D Sc hij,
    CyclotomicAction.parameterTwist_s]

/-- Whole ordered operators realize the same correction when its source naturality is proved. -/
theorem transformLinear_triplePolynomial (hij : i ≠ j)
    (hP : IsSupernatural k (D.parity i) (fun v =>
      tripleDotCorrectionPolynomial D (parameterTwist D Sc) (R := End (F.obj v))
        i j (c v) (b v) (a v)))
    (N : Superfunctor k C (SVec k)) (w : E) :
    tripleDotCorrectionPolynomial D Sc i j
        (transformLinear ha N w) (transformLinear hb N w) (transformLinear hc N w) =
      sign k (D.parity i * D.parity j) • transformLinear hP N w := by
  apply hom_ext
  intro v g z
  rw [LinearMap.smul_apply, transformLinear_tensor,
    transformLinear_triplePolynomial_tensor F D Sc i j ha hb hc hij N w v g z]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction
