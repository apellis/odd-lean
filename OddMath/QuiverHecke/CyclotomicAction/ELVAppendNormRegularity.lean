/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendMovingSupport
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerNorm
import OddMath.QuiverHecke.CyclotomicAction.ELVRDescent
/-! # Append endpoint norm regularity and moving-chain injectivity

The independent endpoint polynomial is regular on the full append-old ELV
quotient. A largest moving exponent detects every nonzero coefficient. The
reverse chain then proves injectivity of G (`qMap`), without using P or QP
injectivity. This proves the cancellation required in DeformedBoundaryDivision §2;
the reverse boundary comparison of §3 is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem rightContext_sourceDotPower (i : I) (v : List I) (b d : ℕ) (hb : b < v.length) :
    rightContext D Sc cutoff [i] v v (sourceDotPower D Sc cutoff v b d) =
      affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) b ^ d) := by
  change rightContext D Sc cutoff [i] v v
    (affineUnit D Sc cutoff v v (dotE D Sc v b ^ d)) = _
  rw [rightContext_affineUnit]
  congr 1
  change whiskerWordRingHom D Sc v [i] (dotE D Sc v b ^ d) = _
  rw [map_pow, whiskerWordRingHom_apply, dotE_whiskerRight D Sc v [i] b hb]

theorem appendProjection_old_dotPower (i : I) (v w : List I) (b d : ℕ) (hb : b < v.length)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) b ^ d) ≫ h) =
      appendOldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v b d)
        (appendProjection D Sc cutoff i v w h) := by
  change _ = appendProjection D Sc cutoff i v w
    (rightContext D Sc cutoff [i] v v (sourceDotPower D Sc cutoff v b d) ≫ h)
  rw [rightContext_sourceDotPower D Sc cutoff i v b d hb]

theorem appendProjection_powerDifference_regular (i : I) (v w : List I) (b d : ℕ)
    (hb : b < v.length) (hd : d • D.parity i = 0) (hpos : 0 < d)
    (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        (dotE D Sc (v ++ [i]) v.length ^ d - dotE D Sc (v ++ [i]) b ^ d) ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  rw [map_sub, Preadditive.sub_comp, map_sub, appendProjection_old_dotPower D Sc cutoff i v w b d hb] at hh
  exact appendMovingPower_eq_oldSource D Sc cutoff 0 i v w d hd hpos
    (sourceDotPower D Sc cutoff v b d) _ (sub_eq_zero.mp hh)

theorem appendProjection_powerSum_regular (i : I) (v w : List I) (b d : ℕ)
    (hb : b < v.length) (hd : d • D.parity i = 0) (hpos : 0 < d)
    (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        (dotE D Sc (v ++ [i]) b ^ d + dotE D Sc (v ++ [i]) v.length ^ d) ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  rw [map_add, Preadditive.add_comp, map_add, appendProjection_old_dotPower D Sc cutoff i v w b d hb] at hh
  apply appendMovingPower_eq_oldSource D Sc cutoff 0 i v w d hd hpos
    (-sourceDotPower D Sc cutoff v b d)
  change _ = appendProjection D Sc cutoff i v w
    (rightContext D Sc cutoff [i] v v (-sourceDotPower D Sc cutoff v b d) ≫ h)
  rw [map_neg, Preadditive.neg_comp, map_neg]
  exact eq_neg_of_add_eq_zero_right hh

theorem appendProjection_qLeft_regular (i j : I) (hji : j ≠ i) (v w : List I)
    (b : ℕ) (hb : b < v.length) (hd : D.d j i ≠ 0)
    (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (IntertwinerMeet.qLeft (B := End ((pres D Sc).obj (ob D (v ++ [i]))))
        (dotE D Sc (v ++ [i]) b) (dotE D Sc (v ++ [i]) v.length)
        (D.dn j i) (D.dn i j) (Sc.t j i : k) (Sc.t i j : k) (Sc.s j i)) ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  let z := appendProjection D Sc cutoff i v w h
  let f := appendOldCoordinateEquiv D Sc cutoff 0 i v w z
  suffices hf : f = 0 by
    exact (appendOldCoordinateEquiv D Sc cutoff 0 i v w).injective
      (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  have hpos : 0 < D.dn i j := by
    have hc := D.dn_cast hji.symm
    have hz : D.d i j ≠ 0 := fun hz => hd ((D.d_eq_zero_iff j i).mpr hz)
    omega
  have hpar : D.dn i j • D.parity i = 0 := by
    simpa only [nsmul_eq_mul] using dn_mul_parity D i j
  have hbound (e : ℕ) (he : e < D.dn i j) :
      ∀ t ∈ f.support, e + t.1.1 < (q.representative.shift (D.dn i j)).1.1 := by
    intro t ht
    have hm := hmax t ht
    have hk := congrArg Prod.fst q.representative_tailKey
    change q.representative.1.1 = q.1.1 at hk
    change e + t.1.1 < D.dn i j + q.representative.1.1
    omega
  have hlow (a e : ℕ) (he : e < D.dn i j) (hep : e • D.parity i = 0) :
      appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
        (appendProjection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _
            (dotE D Sc (v ++ [i]) b ^ a * dotE D Sc (v ++ [i]) v.length ^ e) ≫ h)) = 0 := by
    rw [End.mul_def, affineUnit_comp]
    rw [← rightContext_sourceDotPower D Sc cutoff i v b a hb]
    change appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
      (appendProjection D Sc cutoff i v w
        ((appendMovingPower D Sc cutoff i v e ≫
          rightContext D Sc cutoff [i] v v (sourceDotPower D Sc cutoff v b a)) ≫ h)) = 0
    rw [appendMovingPower_rightContext_cross D Sc cutoff i e hep, Category.assoc]
    have H := appendOldSource_movingPower_above D Sc cutoff 0
      (q.representative.shift (D.dn i j)) e hep (sourceDotPower D Sc cutoff v b a) f
      (hbound e he)
    rw [appendOldReconstruct_coordinateEquiv] at H
    exact H
  have hold : appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) b ^ D.dn j i) ≫ h)) = 0 := by
    simpa only [pow_zero, mul_one] using hlow (D.dn j i) 0 hpos (by simp)
  rw [IntertwinerMeet.qLeft, map_add, map_add, Preadditive.add_comp,
    Preadditive.add_comp, map_add, map_add] at hh
  have he := congrArg (appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))) hh
  simp only [map_add, map_zero, map_sum, Preadditive.sum_comp, map_smul,
    Linear.smul_comp] at he
  have hl : (∑ a ∈ Finset.Ioo 0 (D.dn j i), ∑ e ∈ Finset.Ioo 0 (D.dn i j),
      Sc.s j i a e • appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
        (appendProjection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _
            (dotE D Sc (v ++ [i]) b ^ a * dotE D Sc (v ++ [i]) v.length ^ e) ≫ h))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro e he'
    by_cases hs : Sc.s j i a e = 0
    · rw [hs, zero_smul]
    · have hep : e • D.parity i = 0 := by
        rw [nsmul_eq_mul]
        apply zmod_two_eq_zero_of_ne_one
        intro hp
        apply hs
        rw [Sc.s_symm]
        exact Sc.s_eq_zero i j e a hp
      rw [hlow a e (Finset.mem_Ioo.mp he').2 hep, smul_zero]
  rw [hl, hold, smul_zero, zero_add, zero_add] at he
  have hm := appendMovingPower_coordinate_shift D Sc cutoff 0 q (D.dn i j) hpar f
  rw [appendOldReconstruct_coordinateEquiv] at hm
  change appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
    (appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) v.length ^ D.dn i j) ≫ h)) = f q at hm
  rw [hm] at he
  exact (DFinsupp.mem_support_iff.mp hq) ((Sc.t i j).isUnit.smul_eq_zero.mp he)

/-- Every append endpoint factor is regular on the full old-only quotient. -/
theorem appendProjection_endpointNormFactor_regular (i j : I) (v w : List I)
    (b : ℕ) (hb : b < v.length) (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (endpointNormFactor D Sc
        (B := End ((pres D Sc).obj (ob D (v ++ [i])))) j i
        (dotE D Sc (v ++ [i]) b) (dotE D Sc (v ++ [i]) v.length)) ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  unfold endpointNormFactor at hh
  split_ifs at hh with hji hp hd
  · subst j
    rw [map_neg, Preadditive.neg_comp, map_neg, neg_eq_zero,
      End.mul_def, affineUnit_comp, Category.assoc] at hh
    have hs := appendProjection_powerSum_regular D Sc cutoff i v w b 2 hb
      ((by decide : ∀ p : ZMod 2, (2 : ℕ) • p = 0) (D.parity i)) (by decide) _ hh
    rw [pow_two (dotE D Sc (v ++ [i]) v.length ^ 2 - dotE D Sc (v ++ [i]) b ^ 2),
      End.mul_def, affineUnit_comp, Category.assoc] at hs
    exact appendProjection_powerDifference_regular D Sc cutoff i v w b 2 hb
      ((by decide : ∀ p : ZMod 2, (2 : ℕ) • p = 0) (D.parity i)) (by decide) h
      (appendProjection_powerDifference_regular D Sc cutoff i v w b 2 hb ((by decide : ∀ p : ZMod 2, (2 : ℕ) • p = 0) (D.parity i)) (by decide) _ hs)
  · subst j
    have hp0 := parity_eq_zero_of_ne_one hp
    rw [map_neg, Preadditive.neg_comp, map_neg, neg_eq_zero,
      pow_two, End.mul_def, affineUnit_comp, Category.assoc] at hh
    have he := appendProjection_powerDifference_regular D Sc cutoff i v w b 1 hb
      (by simp [hp0]) (by decide)
    simp only [pow_one] at he
    exact he h (he _ hh)
  · rw [Algebra.algebraMap_eq_smul_one, map_smul, End.one_def, affineUnit_id,
      Linear.smul_comp, Category.id_comp, map_smul] at hh
    exact (Sc.t j i).isUnit.smul_eq_zero.mp hh
  · exact appendProjection_qLeft_regular D Sc cutoff i j hji v w b hb hd h hh

/-- Cancel the ordered norm recursively without changing its ambient word. -/
theorem appendProjection_endpointNormAux_regular (i : I) (v w ν : List I) (b : ℕ)
    (hb : b + ν.length ≤ v.length) (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (endpointNormAux D Sc i (v ++ [i]) v.length b ν) ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  induction ν generalizing b h with
  | nil => simpa only [endpointNormAux, End.one_def, affineUnit_id, Category.id_comp] using hh
  | cons j ν ih =>
    rw [endpointNormAux, End.mul_def, affineUnit_comp, Category.assoc] at hh
    have ht := ih (b + 1) (by simp only [List.length_cons] at hb; omega) _ hh
    exact appendProjection_endpointNormFactor_regular D Sc cutoff i j v w b
      (by simp only [List.length_cons] at hb; omega) h ht

/-- The independently defined append endpoint norm detects every old-only ELV class.
The proof uses finite append PBW support, including all exterior coefficients. -/
theorem appendProjection_endpointNorm_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (endpointNorm D Sc i [] v) ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  apply appendProjection_endpointNormAux_regular D Sc cutoff i v w v 0 (by simp) h
  simpa only [endpointNorm, List.nil_append, List.length_nil, zero_add] using hh

/-- The moving-chain map G is injective on the actual append-old quotient.
Only its reverse composite and independent append norm regularity are used. -/
theorem qMap_injective (i : I) (v w : List I) :
    Function.Injective (qMap D Sc cutoff i v w) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i v w z
  have he := congrArg (rMap D Sc cutoff i v w) hz
  rw [rMap_qMap_projection, map_zero,
    reverseMoveHom_comp_moveHom_eq_endpointNorm] at he
  exact appendProjection_endpointNorm_regular D Sc cutoff i v w h he

end OddMath.QuiverHecke.ELVOld
