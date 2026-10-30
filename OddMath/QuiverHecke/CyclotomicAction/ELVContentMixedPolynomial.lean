/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMixedBraid

/-! # Ordered dotted correction for common-content mixed braid

`DeformedMixedBraid.md` §3, equations (6)–(10), and the mixed relation needed
by `DeformedActionAssembly.md` §6. Three arbitrary dot powers retain their
full residual twist. On the support forced by Sc the scalar signs agree
with parameterTwist Sc after reflecting the correction index. No dots are
commuted. The resulting linear-map identity has the original Sc leading
and interior coefficients and the order X₃^(r-1-l) X₂^s X₁^l.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Ordered three-power evaluation, with no even-block assumptions. -/
theorem contentInduction_three_powers {β : Multiset I} {σ : List I}
    {p q t : ZMod 2} {a b c : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ q)
    (hc : c ∈ parity (R := k) _ _ t)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (l s n : ℕ) (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionEndLinear D Sc cutoff N hc M w ^ n) *
      (contentInductionEndLinear D Sc cutoff N hb M w ^ s) *
      (contentInductionEndLinear D Sc cutoff N ha M w ^ l))
        (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
    sign k (p*(l/2 : ℕ) + q*(s/2 : ℕ) + t*(n/2 : ℕ) +
      (s : ZMod 2)*q*((l : ZMod 2)*p) +
      (n : ZMod 2)*t*((s : ZMod 2)*q + (l : ZMod 2)*p)) •
      contentTensorEval D Sc cutoff N M w v
        (twist k ((n : ZMod 2)*t + ((s : ZMod 2)*q + (l : ZMod 2)*p)) h) m
        (a ^ l * b ^ s * c ^ n) := by
  rw [Module.End.mul_apply, Module.End.mul_apply,
    contentInductionEndLinear_pow_tensor, map_smul, contentInductionEndLinear_pow_tensor,
    map_smul, map_smul, contentInductionEndLinear_pow_tensor]
  unfold contentTensorEval
  simp only [contentAppendToLinear_apply]
  simp only [twist_comp,
    twist_of_mem _ ((contentAppendTo_supernatural D Sc cutoff N rfl rfl
      (contentEnd_pow_parity D Sc ha l)).mem v),
    twist_of_mem _ ((contentAppendTo_supernatural D Sc cutoff N rfl rfl
      (contentEnd_pow_parity D Sc hb s)).mem v), map_smul, ← twist_add,
    Linear.smul_comp, Linear.comp_smul, BalancedInduction.tensor,
    ← TensorProduct.smul_tmul', smul_smul, ← sign_add]
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  · congr 1
    ring
  congr 2
  change _ = contentAppendToComponent D Sc cutoff N rfl rfl (a^l*b^s*c^n) v ≫ _
  rw [← Category.assoc, contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _
    (contentEnd_pow_parity D Sc hb s), ← Category.assoc,
    contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _ (contentEnd_pow_parity D Sc ha l)]
  simp only [End.mul_def, Category.assoc]

/-- Arbitrary-exponent sign identity on the prescribed separate parity support. -/
theorem mixed_braid_sign_identity
    (p q : ZMod 2) (r s l a : ℕ)
    (hr : (r : ZMod 2) * p = 0)
    (hs : (s : ZMod 2) * q = 0)
    (hl : l < r) (ha : a = r - 1 - l) :
    p*q + p*(l : ZMod 2) +
      (p*(l/2 : ℕ) + q*(s/2 : ℕ) + p*(a/2 : ℕ) +
        p*q*(s : ZMod 2)*((l : ZMod 2)+(a : ZMod 2)) + p*(l : ZMod 2)*(a : ZMod 2)) =
    p*(a : ZMod 2) + (p*q + p*(r/2 : ℕ) + q*(s/2 : ℕ)) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp
  · have hz : (2 : ZMod 2) = 0 := rfl
    have hr0 : (r : ZMod 2) = 0 := by simpa using hr
    have hrmod : r % 2 = 0 := by
      simpa using (ZMod.natCast_eq_natCast_iff' r 0 2).mp hr0
    have hsum : l + a + 1 = r := by omega
    have hh : l / 2 + a / 2 + 1 = r / 2 := by omega
    have hadd := congrArg (Nat.cast : ℕ → ZMod 2) hsum
    push_cast at hadd
    rw [hr0] at hadd
    have hhalf := congrArg (Nat.cast : ℕ → ZMod 2) hh
    push_cast at hhalf
    have hprod : (l : ZMod 2) * (a : ZMod 2) = 0 := by
      rcases parity_eq_zero_or_one (l : ZMod 2) with hl0 | hl1
      · simp [hl0]
      · rw [hl1, one_mul]
        rw [hl1] at hadd
        linear_combination hadd - hz
    have hcross : q*(s : ZMod 2)*((l : ZMod 2)+(a : ZMod 2)) = 0 := by
      rw [mul_comm q (s : ZMod 2), hs, zero_mul]
    simp only [one_mul, hcross, hprod, add_zero]
    linear_combination hadd + hhalf - ((a : ZMod 2) + 1) * hz

theorem mixed_braid_total_parity (p q : ZMod 2) (r s l : ℕ)
    (hr : (r : ZMod 2)*p = 0) (hs : (s : ZMod 2)*q = 0) (hl : l < r) :
    ((r-1-l : ℕ) : ZMod 2)*p + ((s : ZMod 2)*q + (l : ZMod 2)*p) = p := by
  have he : r - 1 - l + l + 1 = r := by omega
  have he' := congrArg (Nat.cast : ℕ → ZMod 2) he
  push_cast at he'
  have hz : (2 : ZMod 2) = 0 := rfl
  linear_combination p * he' + hr + hs - p * hz

/-- Supported intermediate calculation; support is derived from Sc in the polynomial theorem. -/
theorem contentInduction_three_supported {β : Multiset I} {σ : List I}
    {p q : ZMod 2} {a b c : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ q)
    (hc : c ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (r s l : ℕ) (hr : (r : ZMod 2)*p = 0) (hs : (s : ZMod 2)*q = 0) (hl : l < r)
    (d : k) (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    ((sign k (p*(q+(l : ZMod 2))) * d) •
      ((contentInductionEndLinear D Sc cutoff N hc M w ^ (r-1-l)) *
        (contentInductionEndLinear D Sc cutoff N hb M w ^ s) *
        (contentInductionEndLinear D Sc cutoff N ha M w ^ l)))
        (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
    sign k (p*q) • contentTensorEval D Sc cutoff N M w v (twist k p h) m
      ((sign k (p*(q+((r-1-l : ℕ) : ZMod 2))) *
        (sign k (p*q+p*(r/2 : ℕ)+q*(s/2 : ℕ)) * d)) •
        (a^l*b^s*c^(r-1-l))) := by
  rw [LinearMap.smul_apply, contentInduction_three_powers,
    mixed_braid_total_parity p q r s l hr hs hl, map_smul, smul_smul, smul_smul]
  congr 1
  let n := r-1-l
  have hp : p*p = p := by
    rcases parity_eq_zero_or_one p with hp | hp <;> simp [hp]
  have he := mixed_braid_sign_identity p q r s l n hr hs hl rfl
  have hsign : sign k (p*(q+(l : ZMod 2))) *
      sign k (p*(l/2 : ℕ)+q*(s/2 : ℕ)+p*(n/2 : ℕ)+
        (s : ZMod 2)*q*((l : ZMod 2)*p)+(n : ZMod 2)*p*((s : ZMod 2)*q+(l : ZMod 2)*p)) =
      sign k (p*q) * (sign k (p*(q+(n : ZMod 2))) *
        sign k (p*q+p*(r/2 : ℕ)+q*(s/2 : ℕ))) := by
    simp only [← sign_add]
    congr 1
    have hz : (2 : ZMod 2) = 0 := rfl
    linear_combination he + (n : ZMod 2)*(l : ZMod 2)*(hp) - p*q*hz
  calc
    _ = (sign k (p*(q+(l : ZMod 2))) *
      sign k (p*(l/2 : ℕ)+q*(s/2 : ℕ)+p*(n/2 : ℕ)+
        (s : ZMod 2)*q*((l : ZMod 2)*p)+(n : ZMod 2)*p*((s : ZMod 2)*q+(l : ZMod 2)*p))) * d := by ring
    _ = _ := by rw [hsign]; ring

theorem contentTripleDot_one_parity (i j : I) :
    dotE D Sc [i,j,i] 1 ∈ parity (R := k) _ _ (D.parity j) := by
  simpa using positionedDot_parity D Sc [i] [i] j

theorem contentTripleDot_two_parity (i j : I) :
    dotE D Sc [i,j,i] 2 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa using positionedDot_parity D Sc [i,j] [] i

def contentMixedDotSum (β : Multiset I) (i j : I) (r s : ℕ) (d : k)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :=
  let A := contentInductionEndLinear D Sc cutoff N (firstDot_parity D Sc i [j,i]) M w
  let B := contentInductionEndLinear D Sc cutoff N (contentTripleDot_one_parity D Sc i j) M w
  let C := contentInductionEndLinear D Sc cutoff N (contentTripleDot_two_parity D Sc i j) M w
  ∑ l ∈ Finset.range r, (SKM.zsign k (D.parity i*(D.parity j+l))*d) • (C^(r-1-l)*B^s*A^l)

def contentMixedSourceSum (i j : I) (r s : ℕ) (d : k) : End ((pres D Sc).obj (ob D [i,j,i])) :=
  ∑ l ∈ Finset.range r, (SKM.zsign k (D.parity i*(D.parity j+l))*d) •
    (dotE D Sc [i,j,i] 0 ^ (r-1-l) * dotE D Sc [i,j,i] 1 ^ s * dotE D Sc [i,j,i] 2 ^ l)

theorem contentMixedDotSum_tensor (β : Multiset I) (i j : I) (r s : ℕ) (d : k)
    (hd : d ≠ 0 → (r : ZMod 2)*D.parity i = 0 ∧ (s : ZMod 2)*D.parity j = 0)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl).obj v ⟶ w) (m : M.obj v) :
    contentMixedDotSum D Sc cutoff N β i j r s d M w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl) M.toFunctor v h m) =
    sign k (D.parity i*D.parity j) •
      contentTensorEval D Sc cutoff N M w v (twist k (D.parity i) h) m
        (contentMixedSourceSum D Sc i j r s
          (SKM.zsign k (parameterSignExponent D i j r s)*d)) := by
  by_cases hd0 : d = 0
  · simp [contentMixedDotSum, contentMixedSourceSum, hd0]
  obtain ⟨hr,hs⟩ := hd hd0
  unfold contentMixedDotSum contentMixedSourceSum
  rw [← Finset.sum_range_reflect (fun l =>
    (SKM.zsign k (D.parity i*(D.parity j+l)) *
      (SKM.zsign k (parameterSignExponent D i j r s)*d)) •
      (dotE D Sc [i,j,i] 0 ^ (r-1-l) * dotE D Sc [i,j,i] 1 ^ s * dotE D Sc [i,j,i] 2 ^ l)) r]
  simp only [LinearMap.sum_apply, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hl' := Finset.mem_range.mp hl
  have he : r-1-(r-1-l) = l := by omega
  rw [he]
  simpa only [sign_eq_zsign, parameterSignExponent] using
    contentInduction_three_supported D Sc cutoff N (firstDot_parity D Sc i [j,i])
      (contentTripleDot_one_parity D Sc i j) (contentTripleDot_two_parity D Sc i j)
      M w r s l hr hs hl' d v h m

theorem contentBraidCorrection_eq_sums (i j : I) :
    contentBraidCorrection D Sc i j =
      contentMixedSourceSum D Sc i j (D.dn i j) 0 (Sc.t i j : k) +
      ∑ r ∈ Finset.Ioo 0 (D.dn i j), ∑ s ∈ Finset.Ioo 0 (D.dn j i),
        contentMixedSourceSum D Sc i j r s (Sc.s i j r s) := by
  simp only [contentBraidCorrection, tripleBraidCorrection, contentMixedSourceSum,
    tripleWord, List.nil_append, List.length_nil, zero_add, pow_zero, mul_one]
  rfl

/-- The prescribed Sc correction, in ordered powers of the three induction dots. -/
def contentMixedBraidPolynomial (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :=
  contentMixedDotSum D (parameterTwist D Sc) cutoff N β i j (D.dn i j) 0 (Sc.t i j : k) M w +
    ∑ r ∈ Finset.Ioo 0 (D.dn i j), ∑ s ∈ Finset.Ioo 0 (D.dn j i),
      contentMixedDotSum D (parameterTwist D Sc) cutoff N β i j r s (Sc.s i j r s) M w

theorem contentMixedBraidPolynomial_tensor (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I)))
    (v : ContentCategory D (parameterTwist D Sc) cutoff N β)
    (h : (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j,i] _ rfl).obj v ⟶ w)
    (m : M.obj v) :
    contentMixedBraidPolynomial D Sc cutoff N β i j M w
      (BalancedInduction.tensor (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j,i] _ rfl)
        M.toFunctor v h m) =
    sign k (D.parity i*D.parity j) •
      contentTensorEval D (parameterTwist D Sc) cutoff N M w v (twist k (D.parity i) h) m
        (contentBraidCorrection D (parameterTwist D Sc) i j) := by
  have ht := contentMixedDotSum_tensor D (parameterTwist D Sc) cutoff N β i j
    (D.dn i j) 0 (Sc.t i j : k)
    (fun _ => ⟨CyclotomicAction.dn_cast_mul_parity D hij, by simp⟩) M w v h m
  have hs (r s : ℕ) := contentMixedDotSum_tensor D (parameterTwist D Sc) cutoff N β i j
    r s (Sc.s i j r s) (fun hc => elvParameter_support D Sc hc) M w v h m
  unfold contentMixedBraidPolynomial
  rw [contentBraidCorrection_eq_sums]
  simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum, smul_add,
    Finset.smul_sum, ht, hs, CyclotomicAction.parameterTwist_t_of_ne D Sc hij,
    CyclotomicAction.parameterTwist_s]

/-- The normalized mixed braid equals the prescribed ordered dotted polynomial. -/
theorem contentMixedBraid_polynomial_linear (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    contentMixedBraid D (parameterTwist D Sc) cutoff N β i j M w =
      contentMixedBraidPolynomial D Sc cutoff N β i j M w := by
  apply BalancedInduction.hom_ext
  intro v h m
  rw [contentMixedBraid_tensor D _ cutoff N β hij,
    contentMixedBraidPolynomial_tensor D Sc cutoff N β hij]

end OddMath.QuiverHecke.ELVOld
