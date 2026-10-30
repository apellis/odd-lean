/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVIndependentSBoundaryDivision
/-!
# Coefficient leading maps of the polynomial boundary row

The boundary of each corrected source vector has a prescribed invertible
leading coefficient map. The integer degree difference is the Cartan height.
These are the coefficient-sensitive inputs to row division and then to the
snake-sequence matrix argument; no balanced crossing-column inverse is asserted.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem row_twist_add (a b : ZMod 2) (v : List I) (c : Old D Sc cutoff v v) :
    oldTwist D Sc cutoff a v v (oldTwist D Sc cutoff b v v c) =
      oldTwist D Sc cutoff (a + b) v v c := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  change (ideal D Sc cutoff v v).mkQ (twist k a (twist k b c)) = _
  rw [← twist_add]
  rfl

private theorem row_twist_comp (q : ZMod 2) (v : List I) (b c : Old D Sc cutoff v v) :
    oldTwist D Sc cutoff q v v (oldComp D Sc cutoff v v v b c) =
      oldComp D Sc cutoff v v v (oldTwist D Sc cutoff q v v b)
        (oldTwist D Sc cutoff q v v c) := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  change (ideal D Sc cutoff v v).mkQ (twist k q (b ≫ c)) = _
  rw [twist_comp]
  rfl

private theorem row_precomp_comp (v : List I) (a : hom D Sc cutoff v v)
    (b c : Old D Sc cutoff v v) :
    oldPrecomp D Sc cutoff v v a (oldComp D Sc cutoff v v v b c) =
      oldComp D Sc cutoff v v v (oldPrecomp D Sc cutoff v v a b) c := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  change (ideal D Sc cutoff v v).mkQ (a ≫ (b ≫ c)) = _
  rw [← Category.assoc]
  rfl

theorem outputCoefficientRho_rightAction (p q : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (c : Old D Sc cutoff v v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputCoefficientRho D Sc cutoff p j v
      (outputCoefficientRightAction D Sc cutoff j.1 q v c f) =
    outputCoefficientRightAction D Sc cutoff j.1 q v c
      (outputCoefficientRho D Sc cutoff p j v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single n b =>
    simp only [outputCoefficientRightAction_single, outputCoefficientRho_single,
      map_add, map_smul, row_twist_comp, row_precomp_comp, row_twist_add]
    have he : D.parity j.1 + (q + n • D.parity j.1) = q + (n + 1) • D.parity j.1 := by
      rw [add_smul, one_smul]
      abel
    rw [he]

/-- Corrected source vectors carry the total coefficient twist. -/
theorem outputCorrectedLift_rightAction (p q : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ)
    (c : Old D Sc cutoff v v) :
    outputCoefficientRightAction D Sc cutoff j.1 q v c
      (outputLongExtraction D Sc cutoff p j.1 v
        (outputCorrectedLift D Sc cutoff p j v d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))) =
    outputLongExtraction D Sc cutoff p j.1 v
      (outputCorrectedLift D Sc cutoff p j v d (oldTwist D Sc cutoff q v v c)) := by
  simp only [outputLongExtraction_correctedLift]
  induction d with
  | zero =>
    simp only [Function.iterate_zero, id_eq, outputCoefficientRightAction_single,
      zero_smul, add_zero]
    congr 1
    obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
    change (ideal D Sc cutoff v v).mkQ (𝟙 _ ≫ twist k q c) = _
    rw [Category.id_comp]
    rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', ← outputCoefficientRho_rightAction, ih,
      Function.iterate_succ_apply']

/-- Full coefficient formula for the boundary of the corrected lift. -/
theorem outputBoundary_corrected_coefficient (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d n : ℕ)
    (c : Old D Sc cutoff v v) :
    outputPolynomialBoundary D Sc cutoff p j v
      (outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v d c)) n =
    oldComp D Sc cutoff v v v (outputBoundaryPhi D Sc cutoff p j v d n)
      (oldTwist D Sc cutoff
        (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v v c) := by
  have h := outputPolynomialBoundary_rightAction D Sc cutoff p j v
    (oldTwist D Sc cutoff (p + D.parity j.1 * wordSumParity D v) v v c)
    (outputLongExtraction D Sc cutoff p j.1 v
      (outputCorrectedLift D Sc cutoff p j v d ((ideal D Sc cutoff v v).mkQ (𝟙 _))))
  rw [outputCorrectedLift_rightAction, oldTwist_twice] at h
  rw [h, outputCoefficientRightAction_apply, zero_add, row_twist_add]
  rfl

/-- The row degree is the Cartan height, with integer subtraction. -/
theorem endpointQPDegree_sub_outputSDegree (i : I) (v : List I) :
    (endpointQPDegree D cutoff i v : ℤ) - outputSDegree D i v =
      (cutoff i : ℤ) - (v.map (fun j => D.h i (D.α j))).sum := by
  have hr : ∀ w : List I, (List.range w.length).map (fun b => w.getD b i) = w := by
    intro w
    induction w with
    | nil => rfl
    | cons a w ih =>
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.getD_cons_zero,
        List.map_map]
      exact congrArg (List.cons a) ih
  have he : endpointQPDegree D cutoff i v = cutoff i + (v.map (appendQPDegree D i)).sum := by
    unfold endpointQPDegree
    conv_rhs => rw [← hr v, List.map_map]
    rfl
  rw [he, Nat.cast_add]
  suffices hs : ((v.map (appendQPDegree D i)).sum : ℤ) - outputSDegree D i v =
      -(v.map (fun j => D.h i (D.α j))).sum by omega
  clear he hr
  induction v with
  | nil => simp [outputSDegree]
  | cons a v ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    by_cases h : a = i
    · subst a
      simp [outputSDegree, appendQPDegree, D.cd.coroot_root_self] at ih ⊢
      split_ifs at ih ⊢ <;> omega
    · have hni : i ≠ a := Ne.symm h
      simp [outputSDegree, h, appendQPDegree, D.dn_cast hni,
        SKM.Datum.d] at ih ⊢
      omega

/-- Coefficients above the integer height bound vanish for every old coefficient. -/
theorem outputBoundary_corrected_above (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d n : ℕ)
    (c : Old D Sc cutoff v v)
    (hn : d + endpointQPDegree D cutoff j.1 v < n + outputSDegree D j.1 v) :
    outputPolynomialBoundary D Sc cutoff p j v
      (outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v d c)) n = 0 := by
  rw [outputBoundary_corrected_coefficient]
  have h := outputBoundaryPhi_signed_above D Sc cutoff p j v d n hn
  have h' := congrArg (fun b : Old D Sc cutoff v v =>
    SKM.zsign k (D.parity j.1) ^ v.count j.1 • b) h
  simp only [Finsupp.smul_apply, smul_smul, ← mul_pow, SKM.zsign_mul_self',
    one_pow, one_smul, smul_zero] at h'
  rw [h', map_zero, LinearMap.zero_apply]

/-- The low corrected source window is killed by the boundary. -/
theorem outputBoundary_corrected_eq_zero (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ)
    (c : Old D Sc cutoff v v)
    (hd : d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v) :
    outputPolynomialBoundary D Sc cutoff p j v
      (outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v d c)) = 0 := by
  ext n
  exact outputBoundary_corrected_above D Sc cutoff p j v d n c (by omega)

/-- The leading coefficient map is the specified scalar times total parity twist. -/
theorem outputBoundary_corrected_signed_top (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d n : ℕ)
    (c : Old D Sc cutoff v v)
    (hn : n + outputSDegree D j.1 v = d + endpointQPDegree D cutoff j.1 v) :
    SKM.zsign k (D.parity j.1) ^ v.count j.1 •
      outputPolynomialBoundary D Sc cutoff p j v
        (outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v d c)) n =
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      ((appendQPProductUnit D Sc j.1 v : k) • oldTwist D Sc cutoff
        (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v v c) := by
  rw [outputBoundary_corrected_coefficient, ← LinearMap.smul_apply, ← map_smul]
  have he : n = d + endpointQPDegree D cutoff j.1 v - outputSDegree D j.1 v := by omega
  have ht := outputBoundaryPhi_signed_top D Sc cutoff p j v d (by omega)
  rw [← he] at ht
  simp only [Finsupp.smul_apply] at ht
  rw [ht, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply]
  congr 2
  obtain ⟨b, hb⟩ := (ideal D Sc cutoff v v).mkQ_surjective
    (oldTwist D Sc cutoff (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v v c)
  rw [← hb, oldComp_mk, Category.id_comp]

/-- The unit prescribed by the signed numerator and the independent S top. -/
def outputBoundaryLeadingUnit (j : {j : I // D.parity j = 1}) (v : List I) : kˣ :=
  (⟨SKM.zsign k (D.parity j.1), SKM.zsign k (D.parity j.1),
    SKM.zsign_mul_self' _, SKM.zsign_mul_self' _⟩ : kˣ) ^ v.count j.1 *
  (⟨sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)),
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)),
    Supercategory.sign_mul_self _, Supercategory.sign_mul_self _⟩ : kˣ) * appendQPProductUnit D Sc j.1 v

/-- The complete coefficient leading map, including total parity, is invertible. -/
def outputBoundaryLeadingEquiv (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (n : ℕ) :
    Old D Sc cutoff v v ≃ₗ[k] Old D Sc cutoff v v :=
  (LinearEquiv.ofInvolutive
    (oldTwist D Sc cutoff (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v v)
    (oldTwist_twice D Sc cutoff _ v v)).trans
      (LinearEquiv.smulOfUnit (outputBoundaryLeadingUnit D Sc cutoff j v))

/-- The leading equivalence is the coefficient of the boundary itself. -/
theorem outputBoundary_corrected_top (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d n : ℕ)
    (c : Old D Sc cutoff v v)
    (hn : n + outputSDegree D j.1 v = d + endpointQPDegree D cutoff j.1 v) :
    outputPolynomialBoundary D Sc cutoff p j v
      (outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v d c)) n =
    outputBoundaryLeadingEquiv D Sc cutoff p j v n c := by
  have h := outputBoundary_corrected_signed_top D Sc cutoff p j v d n c hn
  have h' := congrArg (fun b : Old D Sc cutoff v v =>
    SKM.zsign k (D.parity j.1) ^ v.count j.1 • b) h
  rw [smul_smul, ← mul_pow, SKM.zsign_mul_self', one_pow, one_smul] at h'
  exact h'.trans (by
    change _ = (SKM.zsign k (D.parity j.1) ^ v.count j.1 *
      sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) *
      (appendQPProductUnit D Sc j.1 v : k)) •
      oldTwist D Sc cutoff (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v v c
    rw [mul_smul, mul_smul])

end OddMath.QuiverHecke.ELVOld
