/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RouquierHomPostMateUnits

/-! # Mixed inverse identities with contentwise denominator units

The even case needs the transposed source difference to be a unit.
The odd case needs the target square denominator and both transposed source
square norms. These are the literal finite-polynomial inputs to the mate
argument; no nilpotence exponent for a whole weight fibre is assumed.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section Conj
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)

/-- The even inverse identities need only the literal transposed source denominator unit. -/
theorem homDistinctMixedMateDot_isIso_of_inverse_units {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0)
    (α : End ((homParityShift (k := k) τ).obj
      ((E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫ E')))
    (h₁ : α ≫ (mixedPostJPostDot (k := k) E κ τ H (F' := F') y -
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x) = 𝟙 _)
    (h₂ : (mixedPostJPostDot (k := k) E κ τ H (F' := F') y -
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x) ≫ α = 𝟙 _)
    (hS : IsUnit (mixedPostSourcePreDot (k := k) E κ H (F' := F') x -
      mixedPostSourcePostDot (k := k) E κ H A y)) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      ((homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).hom ≫
        (-(α ≫ α ≫
          (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv)))) := by
  have hau : α * (mixedPostJPostDot (k := k) E κ τ H (F' := F') y -
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x) = 1 := h₂
  have hua : (mixedPostJPostDot (k := k) E κ τ H (F' := F') y -
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x) * α = 1 := h₁
  have hu : IsUnit (mixedPostJPostDot (k := k) E κ τ H (F' := F') y -
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x) := ⟨⟨_, α, hua, hau⟩, rfl⟩
  have hc := commute_mixedPostJPreDot_postDot (k := k) E κ τ H (F' := F') hx hy
  have hg := TwoSupercategory.whiskerLeft_mem ((homParityShift (k := k) κ).obj H)
    (SuperAdjunction.rightTranspose_mem A A hy)
  have hxg := commute_mixedPostJPreDot_midDot (k := k) E κ τ H (E' := E') x hg
  have hyg := commute_mixedPostJPostDot_midDot (k := k) E κ τ H y hg
  refine homDistinctMixedMateDot_isIso_of_conj_units E A κ τ H hx hy α ?_ ?_ 0 0 ?_
    (hS.pow 2) ?_
  · exact (commute_of_mul_eq_of_isUnit hu hau ((Commute.refl _).sub_right hc.symm)
      (Commute.one_right _)).symm
  · exact (commute_of_mul_eq_of_isUnit hu hau (hyg.symm.sub_right hxg.symm)
      (Commute.one_right _)).symm
  · generalize mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x = X at hau ⊢
    generalize mixedPostJPostDot (k := k) E κ τ H (F' := F') y = Y at hau ⊢
    rw [← neg_sub Y X, neg_mul_neg, pow_zero, zero_smul, add_zero]
    calc α * α * ((Y - X) * (Y - X)) = α * (α * (Y - X)) * (Y - X) := by
          simp only [mul_assoc]
      _ = 1 := by rw [hau, mul_one, hau]

  · simpa only [pow_zero, neg_zero, zero_smul, add_zero, neg_one_smul] using
      (isUnit_one : IsUnit (1 : End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F')))).neg

/-- The odd inverse identity uses target and transposed source norm units.
The transpose of an odd square carries the signed reversal explicitly. -/
theorem homDistinctMixedMateDot_isIso_of_inverse_odd_units {x : E ⟶ E}
    (hx : x ∈ parity (R := k) E E 1) {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 1)
    (hu : IsUnit (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ^ 2 -
      mixedPostJPostDot (k := k) E κ τ H (F' := F') y ^ 2))
    (hMinus : IsUnit (mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ 2 -
      mixedPostSourcePostDot (k := k) E κ H A y ^ 2))
    (hPlus : IsUnit (mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ 2 +
      mixedPostSourcePostDot (k := k) E κ H A y ^ 2))
    (α : End ((homParityShift (k := k) τ).obj
      ((E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫ E')))
    (h₂ : (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x ≫
        mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x -
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y ≫
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y) ≫ α =
      (show _ ⟶ _ from mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x) -
        (show _ ⟶ _ from mixedPostJPostDot (k := k) E κ τ H (F' := F') y)) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      ((homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).hom ≫
        (-(α ≫ α ≫
          (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv)))) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hx2 : x ≫ x ∈ parity (R := k) E E 0 := h11 ▸ Supercategory.comp_mem hx hx
  have hy2 : y ≫ y ∈ parity (R := k) E' E' 0 := h11 ▸ Supercategory.comp_mem hy hy
  have hX2 : mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') (x ≫ x) =
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x *
        mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x := by
    change (homParityShift (k := k) τ).map _ = _ ≫ _
    rw [TwoSupercategory.comp_whiskerRight (R := k), TwoSupercategory.comp_whiskerRight (R := k),
      Functor.map_comp]
  have hY2 : mixedPostJPostDot (k := k) E κ τ H (F' := F') (y ≫ y) =
      mixedPostJPostDot (k := k) E κ τ H (F' := F') y *
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y := by
    change (homParityShift (k := k) τ).map _ = _ ≫ _
    rw [TwoSupercategory.whiskerLeft_comp (R := k), Functor.map_comp]
  -- the odd dots anticommute
  have hac : mixedPostJPostDot (k := k) E κ τ H (F' := F') y *
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x =
      -(mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x *
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y) := by
    have h := homMixedInterchange_dot_exchange (k := k) E E' τ
      ((homParityShift (k := k) κ).obj H ≫ F') x y hx hy
    have hs : koszulSign (1 : ZMod 2) 1 = -1 := by simp [koszulSign]
    rw [hs, neg_one_zsmul] at h
    exact h
  have hg := TwoSupercategory.whiskerLeft_mem ((homParityShift (k := k) κ).obj H)
    (SuperAdjunction.rightTranspose_mem A A hy2)
  have hXg := commute_mixedPostJPreDot_midDot (k := k) E κ τ H (E' := E') x hg
  have hYg := commute_mixedPostJPostDot_midDot (k := k) E κ τ H y hg
  have hau : α * (mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x *
        mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x -
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y *
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y) =
      mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x -
        mixedPostJPostDot (k := k) E κ τ H (F' := F') y := h₂
  obtain ⟨G, hG⟩ : ∃ G, G = mixedPostJMidDot (k := k) E κ τ H (E' := E')
      ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A (y ≫ y)) :=
    ⟨_, rfl⟩
  rw [← hG] at hXg hYg
  set X := mixedPostJPreDot (k := k) E κ τ H (E' := E') (F' := F') x
  set Y := mixedPostJPostDot (k := k) E κ τ H (F' := F') y
  have hYYX : Commute (Y * Y) X := by
    change Y * Y * X = X * (Y * Y)
    rw [mul_assoc, hac, mul_neg, ← mul_assoc, hac, neg_mul, neg_neg, mul_assoc]
  have hXXY : Commute (X * X) Y := by
    change X * X * Y = Y * (X * X)
    rw [← mul_assoc Y X X, hac, neg_mul, mul_assoc X Y X, hac, mul_neg, neg_neg, mul_assoc]
  have hYY : Commute (Y * Y) Y := (Commute.refl Y).mul_left (Commute.refl Y)
  have hXX : Commute (X * X) X := (Commute.refl X).mul_left (Commute.refl X)
  have hs : IsUnit (X * X - Y * Y) := by
    simpa only [pow_two] using hu
  have hds : Commute (X - Y) (X * X - Y * Y) :=
    ((hXX.symm.sub_right hYYX.symm)).sub_left (hXXY.symm.sub_right hYY.symm)
  have hSX2 : mixedPostSourcePreDot (k := k) E κ H (F' := F') (x ≫ x) =
      mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ 2 := by
    unfold mixedPostSourcePreDot
    rw [pow_two, End.mul_def,
      TwoSupercategory.comp_whiskerRight (R := k)]
  have hSY2 : mixedPostSourcePostDot (k := k) E κ H A (y ≫ y) =
      -(mixedPostSourcePostDot (k := k) E κ H A y ^ 2) := by
    have hz : koszulSign (1 : ZMod 2) 1 = -1 := by simp [koszulSign]
    unfold mixedPostSourcePostDot
    rw [pow_two, End.mul_def,
      SuperAdjunction.rightTranspose_comp A A A hy hy,
      hz, neg_one_zsmul, TwoSupercategory.whiskerLeft_neg (R := k),
      TwoSupercategory.whiskerLeft_neg (R := k),
      TwoSupercategory.whiskerLeft_comp (R := k),
      TwoSupercategory.whiskerLeft_comp (R := k)]

  refine homDistinctMixedMateDot_isIso_of_conj_units E A κ τ H hx2 hy2 α ?_ ?_ 1 1 ?_ ?_ ?_
  · rw [hY2]
    exact (commute_of_mul_eq_of_isUnit hs hau ((hYYX.mul_right hYYX).sub_right (Commute.refl _))
      (hYYX.sub_right hYY)).symm
  · rw [← hG]
    exact (commute_of_mul_eq_of_isUnit hs hau
      ((hXg.symm.mul_right hXg.symm).sub_right (hYg.symm.mul_right hYg.symm))
      (hXg.symm.sub_right hYg.symm)).symm
  · rw [hX2, hY2, pow_one, one_smul]
    calc α * α * ((X * X - Y * Y) * (X * X - Y * Y)) =
          α * (α * (X * X - Y * Y)) * (X * X - Y * Y) := by simp only [mul_assoc]
      _ = α * ((X * X - Y * Y) * (X - Y)) := by rw [hau, mul_assoc, hds.eq]
      _ = (X - Y) * (X - Y) := by rw [← mul_assoc, hau]
      _ = X * X + Y * Y := by
          rw [sub_mul, mul_sub, mul_sub, hac]
          abel

  · rw [hSX2, hSY2, sub_neg_eq_add]
    exact hPlus.pow 2
  · rw [pow_one, hSX2, hSY2, neg_one_smul, neg_one_smul, neg_neg]
    simpa only [sub_eq_add_neg, neg_add, neg_neg] using hMinus.neg

end Conj
end OddMath.SKM

