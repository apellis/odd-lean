/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOneStrand
import OddMath.QuiverHecke.CyclotomicAction.ELVRelationRegularity

/-!
# Inverse first-dot transport over full ELV coefficients

The local first-dot step of `DeformedIdealSum.md`. In diagram order the inverse
normalizer translates by +2 delta at even cutoff and -2 delta at odd cutoff.
The coefficient boundary relation is used, including at cutoff zero.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def c (j : {j : I // D.parity j = 1}) (N r : ℕ) :=
  SKM.SYM.elvCoefficientQuotient (k := k) D cutoff
    (((-1 : k) ^ (N * (r + 1))) • SKM.SYM.elvCoefficient D k j (N-r))

private theorem c_form (j : {j : I // D.parity j = 1}) (N r : ℕ) (hr : r ≤ N) :
    c (k := k) D cutoff j N r =
      if (N-r)%2=0 then SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.elvChi D k j ((N-r)/2))
      else (-1 : k)^N • (SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j) *
        SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.elvChi D k j ((N-r)/2))) := by
  unfold c SKM.SYM.elvCoefficient
  rw [map_smul]
  by_cases h : (N-r)%2=0
  · rw [ite_eq_left h, ite_eq_left h]
    have hp : (N*(r+1))%2=0 := by
      rw [Nat.mul_mod]
      rcases Nat.mod_two_eq_zero_or_one N with hn | hn
      · simp [hn]
      · have h' : (r+1)%2=0 := by omega
        simp [h']
    rw [neg_one_pow_eq_pow_mod_two, hp, pow_zero, one_smul]
  · rw [ite_eq_right h, ite_eq_right h, map_mul]
    have hp : (N*(r+1))%2=N%2 := by
      rw [Nat.mul_mod]
      rcases Nat.mod_two_eq_zero_or_one N with hn | hn
      · simp [hn]
      · have h' : (r+1)%2=1 := by omega
        simp [hn, h']
    rw [neg_one_pow_eq_pow_mod_two (N*(r+1)), hp, ← neg_one_pow_eq_pow_mod_two N]

private theorem delta_c_step (j : {j : I // D.parity j = 1}) (N r : ℕ) (hr : r < N) :
    (if (N-r)%2=0 then 0 else (2 : k) • c D cutoff j N r) =
      (2 * (-1 : k)^N) •
        (SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j) * c D cutoff j N (r+1)) := by
  have hd : SKM.SYM.elvCoefficientQuotient (k := k) D cutoff (SKM.SYM.delta D k j) *
      SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j) = 0 := by
    rw [← map_mul, ← pow_two, SKM.SYM.delta_sq, map_zero]
  rw [c_form D cutoff j N r (by omega), c_form D cutoff j N (r+1) (by omega)]
  by_cases h : (N-r)%2=0
  · have h' : (N-(r+1))%2≠0 := by omega
    simp [h, h', ← mul_assoc, hd]
  · have h' : (N-(r+1))%2=0 := by omega
    have he : (N-r)/2=(N-(r+1))/2 := by omega
    simp [h, h', he, smul_smul]

private theorem delta_c_zero (j : {j : I // D.parity j = 1}) :
    SKM.SYM.elvCoefficientQuotient (k := k) D cutoff (SKM.SYM.delta D k j) *
      c D cutoff j (cutoff j.1) 0 = 0 := by
  rw [c_form D cutoff j _ 0 (Nat.zero_le _)]
  simp only [Nat.sub_zero]
  split_ifs with h
  · rw [← map_mul]
    exact SKM.SYM.elvCoefficientQuotient_top D cutoff j h
  · rw [mul_smul_comm, ← mul_assoc, ← map_mul, ← pow_two, SKM.SYM.delta_sq, map_zero,
      zero_mul, smul_zero]

private def term (w : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    hom D Sc cutoff w w := a ⊗ₜ[k] (dotE D Sc w 0 ^ n : End _)

private theorem term_pre (w : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m n : ℕ) :
    term D Sc cutoff w 1 m ≫ term D Sc cutoff w a n = term D Sc cutoff w a (n+m) := by
  change BoxProd.tmulHom (X := obj D Sc cutoff w) (Y := obj D Sc cutoff w)
    (𝟙 _) (dotE D Sc w 0 ^ m) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff w) (Y := obj D Sc cutoff w) a (dotE D Sc w 0 ^ n) = _
  dsimp only [obj, elvQuotientObj, coefficientObj]
  rw [BoxProd.tmulHom_comp_tmulHom_eq]
  simp only [proj_id, ↓reduceIte, one_ne_zero, Category.id_comp, Limits.zero_comp,
    BoxProd.tmulHom_def, TensorProduct.zero_tmul]
  change a ⊗ₜ[k] ((dotE D Sc w 0 ^ n) * (dotE D Sc w 0 ^ m)) = _
  rw [← pow_add]
  rfl

private theorem term_post (w : List I)
    (a b : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    term D Sc cutoff w b n ≫ term D Sc cutoff w a 0 = term D Sc cutoff w (a*b) n := by
  change BoxProd.tmulHom (X := obj D Sc cutoff w) (Y := obj D Sc cutoff w)
    b (dotE D Sc w 0 ^ n) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff w) (Y := obj D Sc cutoff w) a (𝟙 _) = _
  dsimp only [obj, elvQuotientObj, coefficientObj]
  rw [BoxProd.tmulHom_comp_tmulHom_eq]
  simp only [twist_id, Category.comp_id, ← BoxProd.tmulHom_add_left,
    ← Preadditive.add_comp, proj_add_proj]
  rfl

private theorem term_smul (w : List I) (s : k)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    term D Sc cutoff w (s • a) n = s • term D Sc cutoff w a n :=
  TensorProduct.smul_tmul' _ _ _

private theorem term_zero (w : List I) (n : ℕ) : term D Sc cutoff w 0 n = 0 :=
  TensorProduct.zero_tmul _ _

private theorem c_mem (j : {j : I // D.parity j = 1}) (N r : ℕ) :
    c (k := k) D cutoff j N r ∈ SKM.SYM.elvCoefficientParity D cutoff ((N-r : ℕ) : ZMod 2) := by
  have h := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.elvCoefficient_mem_parity (k := k) D j (N-r))
  have h' := (SKM.SYM.elvCoefficientParity (k := k) D cutoff ((N-r : ℕ) : ZMod 2)).smul_mem
    ((-1 : k)^(N*(r+1))) h
  simpa [SKM.SYM.elvModelQuotient, c] using h'

private theorem term_dot (j : {j : I // D.parity j = 1}) (v : List I) (N r : ℕ) :
    term D Sc cutoff (j.1::v) (c D cutoff j N r) r ≫ term D Sc cutoff (j.1::v) 1 1 =
      if (N-r)%2=0 then term D Sc cutoff (j.1::v) (c D cutoff j N r) (r+1)
      else -term D Sc cutoff (j.1::v) (c D cutoff j N r) (r+1) := by
  have hx : dotE D Sc (j.1::v) 0 ∈ parity (R := k) _ _ 1 := by
    simpa only [List.nil_append, List.length_nil, j.property] using positionedDot_parity D Sc [] v j.1
  change BoxProd.tmulHom (X := obj D Sc cutoff (j.1::v)) (Y := obj D Sc cutoff (j.1::v))
    (c D cutoff j N r) (dotE D Sc (j.1::v) 0 ^ r) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff (j.1::v)) (Y := obj D Sc cutoff (j.1::v))
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (dotE D Sc (j.1::v) 0 ^ 1) = _
  rw [pow_one, BoxProd.tmulHom_comp_tmulHom (c_mem D cutoff j N r) _ _ hx]
  change koszulSign ((N-r : ℕ) : ZMod 2) 1 •
    ((1 * c D cutoff j N r) ⊗ₜ[k] (dotE D Sc (j.1::v) 0 * dotE D Sc (j.1::v) 0 ^ r)) = _
  rw [one_mul, ← pow_succ']
  have hp : ((N-r : ℕ) : ZMod 2) = ((N-r)%2 : ℕ) := by
    simpa only [ZMod.val_natCast] using (ZMod.natCast_zmod_val ((N-r : ℕ) : ZMod 2)).symm
  rw [hp]
  by_cases he : (N-r)%2=0
  · simp [he, koszulSign, term]
  · have ho : (N-r)%2=1 := by omega
    simp [ho, koszulSign, term]

private theorem term_difference (j : {j : I // D.parity j = 1}) (v : List I)
    (N r : ℕ) (hr : r < N) :
    term D Sc cutoff (j.1::v) 1 1 ≫ term D Sc cutoff (j.1::v) (c D cutoff j N r) r -
      term D Sc cutoff (j.1::v) (c D cutoff j N r) r ≫ term D Sc cutoff (j.1::v) 1 1 =
    (2 * (-1 : k)^N) • term D Sc cutoff (j.1::v)
      (SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j) * c D cutoff j N (r+1)) (r+1) := by
  rw [term_pre, term_dot]
  have hc := congrArg (fun a => term D Sc cutoff (j.1::v) a (r+1)) (delta_c_step D cutoff j N r hr)
  by_cases he : (N-r)%2=0
  · simpa only [he, ite_eq_left, term_zero, term_smul, sub_self] using hc
  · simp only [he, ↓reduceIte, term_smul] at hc
    simpa only [he, ↓reduceIte, sub_neg_eq_add, two_smul] using hc

private theorem relation_expansion (j : {j : I // D.parity j = 1}) (v : List I) :
    relation D Sc cutoff j.1 v = ∑ r : Fin (cutoff j.1 + 1),
      term D Sc cutoff (j.1::v) (c D cutoff j (cutoff j.1) r.val) r.val := by
  unfold relation
  rw [dite_eq_left j.property]
  change elvQuotientMap D Sc cutoff _ _ (elvCyclotomic D Sc j v (cutoff j.1)) = _
  rw [← elvDotPolynomial_first]
  simp only [elvDotPolynomial, coefficientDotPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact elvQuotientMap_source D Sc cutoff _ _

/-- First-dot transport in diagrammatic order. The shift is +2 delta for
    even cutoff and -2 delta for odd cutoff, in the full coefficient quotient. -/
theorem firstDot_relation_transport (j : {j : I // D.parity j = 1}) (v : List I) :
    let x : hom D Sc cutoff (j.1::v) (j.1::v) :=
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] dotE D Sc (j.1::v) 0
    let d : hom D Sc cutoff (j.1::v) (j.1::v) :=
      SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j) ⊗ₜ[k] (𝟙 _)
    x ≫ relation D Sc cutoff j.1 v =
      relation D Sc cutoff j.1 v ≫ (x + (2 * (-1 : k)^(cutoff j.1)) • d) := by
  classical
  suffices ht : term D Sc cutoff (j.1::v) 1 1 ≫ relation D Sc cutoff j.1 v =
    relation D Sc cutoff j.1 v ≫ (term D Sc cutoff (j.1::v) 1 1 +
      (2 * (-1 : k)^(cutoff j.1)) • term D Sc cutoff (j.1::v)
        (SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j)) 0) by
    simpa only [term, pow_one, pow_zero, End.one_def, obj, elvQuotientObj, coefficientObj] using ht
  rw [Preadditive.comp_add, Linear.comp_smul]
  apply sub_eq_iff_eq_add'.mp
  rw [relation_expansion, Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.sum_comp,
    ← Finset.sum_sub_distrib]
  simp only [term_post]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, term_pre, term_dot, Nat.sub_self, Nat.zero_mod,
    ite_eq_left, sub_self, add_zero]
  rw [Fin.sum_univ_succ (f := fun r : Fin (cutoff j.1 + 1) =>
    term D Sc cutoff (j.1::v)
      (SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D k j) *
        c D cutoff j (cutoff j.1) r.val) r.val)]
  simp only [Fin.val_zero, delta_c_zero, term_zero, zero_add, Fin.val_succ, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simpa only [term_pre, term_dot] using term_difference D Sc cutoff j v (cutoff j.1) r.val r.isLt

/-- The even-cutoff boundary relation kills delta itself at cutoff zero. -/
theorem firstDot_delta_cutoff_zero (j : {j : I // D.parity j = 1}) (h : cutoff j.1 = 0) :
    SKM.SYM.elvCoefficientQuotient (k := k) D cutoff (SKM.SYM.delta D k j) = 0 := by
  have ht := SKM.SYM.elvCoefficientQuotient_top (k := k) D cutoff j (by simp [h])
  simpa only [h, Nat.zero_div, SKM.SYM.elvChi, mul_one] using ht

end OddMath.QuiverHecke.ELVOld
