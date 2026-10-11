/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleSlideRaw
import OddMath.SKM.BubbleSeriesStep
/-!
# Bubble slides for a Cartan entry minus one

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 7.3(iii), (7.11)–(7.12), in the complete case `dᵢⱼ = 1`.
Both orientations hold at every weight and every integer shifted degree,
including fake bubbles. The opposite entry `dⱼᵢ` and all scalars remain general.

Here `i` is necessarily even, but `j` need not be: the dot correction has
parity zero by the Cartan parity condition. The lower coefficient sum is empty.
Natural-dot slides follow from the pitchfork and quadratic relations of the
presented supercategory. The Grassmannian convolution then extends them to
all weights: clockwise natural dots cover `h ≤ 0`, counterclockwise ones
cover `h ≥ 1`. No intermediate integer weight is left over.

The cases `dᵢⱼ > 1`, Proposition 7.3(i)–(ii), Corollary 7.4 and Proposition 7.6
are not proved here. No bubble slide is added as a defining relation.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

theorem dn_eq_one_of_d_one {i j : I} (hij : i ≠ j) (hd : D.d i j = 1) : D.dn i j = 1 := by
  have := D.dn_cast hij
  omega
theorem parity_eq_zero_of_d_one {i j : I} (hij : i ≠ j) (hd : D.d i j = 1) : D.parity i = 0 := by
  have H := parity_mul_dn D i j
  simpa [dn_eq_one_of_d_one hij hd] using H

theorem bubbleR_slide_one_raw (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 1) (n : ℕ) :
    bubbleR_right cs i j μ n =
      (Sc.t i j : k) • bubbleR_left cs i j μ (n + 1) +
      (Sc.t j i : k) • (bubbleR_left cs i j μ n ≫
        cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i))) := by
  rw [bubbleR_slide_quad cs i j μ hij n]
  have het : SChain [up j] ((etaL i n).map (whL [] [up j])) [dn i, up i, up j] := by
    simpa using (sChain_etaL i n).whisk [] [up j]
  have hcc : SChain [dn i, up i, up j] (crossL [dn i] i j [] ++ crossL [dn i] j i [])
      [dn i, up i, up j] := by simp [crossL, Shape.dom, Shape.cod]
  have e0 : cl D Sc μ [up j] [dn i, up i, up j]
      ((etaL i n).map (whL [] [up j]) ++ crossL [dn i] i j [] ++ crossL [dn i] j i []) =
      cl D Sc μ [up j] [dn i, up i, up j] ((etaL i n).map (whL [] [up j])) ≫
        cl D Sc μ [dn i, up i, up j] [dn i, up i, up j]
          (crossL [dn i] i j [] ++ crossL [dn i] j i []) := by
    rw [cl_comp het hcc, List.append_assoc]
  rw [e0, Category.assoc]
  have hq := congrArg (plcL D Sc μ [dn i] [] [up i, up j] [up i, up j])
    (cl_quadNe (Sc := Sc) i j (wt D μ []) hij (by omega))
  simp only [dn_eq_one_of_d_one hij hd, show Ioo 0 1 = (∅ : Finset ℕ) by decide,
    sum_empty, add_zero, map_add, map_smul, plcL_cl] at hq
  erw [hq]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul]
  have hbub (m : ℕ) : cl D Sc μ [up j] [dn i, up i, up j] ((etaL i m).map (whL [] [up j])) ≫
      capAt cs i μ [] [up j] = bubbleR_left cs i j μ m := by
    rw [bubbleR_left, lbub, bubR_nat,
      plcL_comp_of_mem μ [] [up j] (cl_mem_homPar (sChain_etaL i m) rfl) (epsP_mem cs i _), plcL_cl]
    rfl
  have ei : (dotsL [] i [up j] 1).map (whL [dn i] []) = dotsL [dn i] i [up j] 1 := by
    simp [dotsL, whL]
  have ej : (dotsL [up i] j [] (D.dn j i)).map (whL [dn i] []) =
      (dotsL [] j [] (D.dn j i)).map (whL [dn i, up i] []) := by
    simp [dotsL, whL, List.map_replicate]
  rw [ei, ← Category.assoc]
  erw [cl_comp het (sChain_dotsL [dn i] i [up j] 1)]
  rw [etaL_dots]
  erw [hbub]
  congr 1
  congr 1
  have hB : SChain [dn i, up i, up j]
      ((dotsL [] j [] (D.dn j i)).map (whL [dn i, up i] [])) [dn i, up i, up j] := by
    simpa using (sChain_dotsL [] j [] (D.dn j i)).whisk [dn i, up i] []
  rw [ej, ← Category.assoc]
  erw [cl_comp het hB]
  change _ ≫ plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) = _
  rw [bub_factor cs i j μ n (sChain_dotsL [] j [] (D.dn j i)), parsum_dotsL,
    mul_comm (D.dn j i : ZMod 2), parity_mul_dn, mul_zero, zsign_zero, one_smul]
  rfl

theorem bubbleL_slide_one_raw (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 1) (n : ℕ) :
    bubbleL_left cs i j μ n =
      (Sc.t i j : k) • bubbleL_right cs i j μ (n + 1) +
      (Sc.t j i : k) • (cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i)) ≫
        bubbleL_right cs i j μ n) := by
  change plcL D Sc μ [] [up j] [] [] (bubL cs i (wt D μ [up j]) n) = _
  rw [bubL_nat, ← pcuR_b cs i j μ hij n, ← eq_7_5_b, pcuL_b_reduce cs i j μ hij n]
  have hc : SChain [up j, up i, dn i] (crossL [] j i [dn i] ++ crossL [] i j [dn i])
      [up j, up i, dn i] := by simp [crossL, Shape.dom, Shape.cod]
  have he : SChain [up j, up i, dn i] ((epsL i n).map (whL [up j] [])) [up j] := by
    simpa using (sChain_epsL i n).whisk [up j] []
  rw [← cl_comp hc he]
  have hq := congrArg (plcL D Sc μ [] [dn i] [up j, up i] [up j, up i])
    (cl_quadNe (Sc := Sc) j i (wt D μ [dn i]) hij.symm
      (fun h => by have := (D.d_eq_zero_iff j i).mp h; omega))
  simp only [dn_eq_one_of_d_one hij hd, show Ioo 0 1 = (∅ : Finset ℕ) by decide,
    sum_empty, sum_const_zero, add_zero, map_add, map_smul, plcL_cl] at hq
  erw [hq]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul]
  rw [add_comm]
  have ei : (dotsL [up j] i [] 1).map (whL [] [dn i]) = dotsL [up j] i [dn i] 1 := by
    simp [dotsL, whL]
  rw [ei]
  erw [pcu_bubble]
  rw [Nat.add_comm 1 n]
  congr 1
  congr 1
  have hj := plcL_right_interchange (Sc := Sc) μ [up j]
    (etaP_mem cs i (wt D μ [])) (sChain_dotsL [] j [] (D.dn j i))
  simp only [map_whL_nil_nil, parsum_dotsL, mul_comm (D.dn j i : ZMod 2),
    parity_mul_dn, mul_zero, zsign_zero, one_smul] at hj
  have ej : (dotsL [] j [up i] (D.dn j i)).map (whL [] [dn i]) =
      (dotsL [] j [] (D.dn j i)).map (whL [] [up i, dn i]) := by
    simp [dotsL, whL, List.map_replicate]
  rw [ej, ← Category.assoc]
  erw [hj]
  rw [Category.assoc]
  congr 1
  change _ = plcL D Sc μ [up j] [] [] [] (bubL cs i (wt D μ []) n)
  rw [bubL_nat, plcL_comp_of_mem μ [up j] [] (etaP_mem cs i _)
    (cl_mem_homPar (sChain_epsL i n) rfl), plcL_cl]
  rfl

/-- The degree-one correction on the neighbouring strand. -/
def bubbleEdgeDot (i j : I) (μ : X) :=
  ((↑(Sc.t i j)⁻¹ : k) * (Sc.t j i : k)) • cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i))

theorem bubbleCoeffR_one_nonpos (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 1)
    (hh : D.h i μ ≤ 0) (n : ℕ) :
    rbub j μ (bubbleCoeffR cs i (wt D μ []) (n + 1)) =
      lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) (n + 1)) +
        lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n) ≫ bubbleEdgeDot (Sc := Sc) i j μ := by
  have hm : 0 ≤ (n : ℤ) - D.h i μ := by omega
  have H := bubbleR_slide_one_raw cs i j μ hij hd ((n : ℤ) - D.h i μ).toNat
  have H' := congrArg (fun f => (cs.c μ i : k) • f) H
  simp only [bubbleR_right, bubbleR_left, rbub, lbub, wt_nil, Int.toNat_of_nonneg hm] at H'
  simp only [bubbleCoeffR, rbub, lbub, map_smul, bubRs, wt_nil, h_wt_upj, hd,
    Nat.cast_add, Nat.cast_one, bubbleEdgeDot, c_wt_upj, Units.val_mul, Linear.smul_comp,
    Linear.comp_smul, smul_smul]
  simp only [smul_add, smul_smul] at H'
  have hi : (n : ℤ) + 1 - D.h i μ - 1 = n - D.h i μ := by ring
  have hl : (n : ℤ) + 1 - (D.h i μ - 1) - 1 = n - D.h i μ + 1 := by ring
  have hl' : (n : ℤ) - (D.h i μ - 1) - 1 = n - D.h i μ := by ring
  rw [hi, hl, hl', H']
  congr 1
  · rw [mul_comm]
  · congr 1
    symm
    calc
      _ = (Sc.t i j : k) * (↑(Sc.t i j)⁻¹ : k) * (cs.c μ i : k) * (Sc.t j i : k) := by ring
      _ = _ := by rw [Units.mul_inv, one_mul]

theorem bubbleCoeffL_one_pos (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 1)
    (hh : 1 ≤ D.h i μ) (n : ℕ) :
    lbub j μ (bubbleCoeffL cs i (wt D μ [up j]) (n + 1)) =
      rbub j μ (bubbleCoeffL cs i (wt D μ []) (n + 1)) +
        bubbleEdgeDot (Sc := Sc) i j μ ≫ rbub j μ (bubbleCoeffL cs i (wt D μ []) n) := by
  have hm : 0 ≤ (n : ℤ) + D.h i μ - 1 := by omega
  have H := bubbleL_slide_one_raw cs i j μ hij hd ((n : ℤ) + D.h i μ - 1).toNat
  have H' := congrArg (fun f => (↑(cs.c (wt D μ [up j]) i)⁻¹ : k) • f) H
  simp only [bubbleL_right, bubbleL_left, rbub, lbub, wt_nil, Int.toNat_of_nonneg hm] at H'
  simp only [bubbleCoeffL, parity_eq_zero_of_d_one hij hd, isg, zero_mul, zsign_zero, one_mul,
    rbub, lbub, map_smul, bubLs, wt_nil, h_wt_upj, hd,
    Nat.cast_add, Nat.cast_one, bubbleEdgeDot, c_wt_upj, mul_inv, Units.val_mul, Linear.smul_comp,
    Linear.comp_smul, smul_smul]
  simp only [smul_add, smul_smul, c_wt_upj, mul_inv, Units.val_mul] at H'
  have hi : (n : ℤ) + 1 + (D.h i μ - 1) - 1 = n + D.h i μ - 1 := by ring
  have hl : (n : ℤ) + 1 + D.h i μ - 1 = n + D.h i μ - 1 + 1 := by ring
  rw [hi, hl, H']
  congr 1
  · rw [mul_assoc, mul_comm (↑(cs.c μ i)⁻¹ : k), ← mul_assoc, Units.inv_mul, one_mul]
  · congr 1
    ring

theorem bubbleCoeff_one (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 1) :
    (fun n => rbub j μ (bubbleCoeffR cs i (wt D μ []) n)) =
      bubbleStepR (fun n => lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n))
        (bubbleEdgeDot (Sc := Sc) i j μ) ∧
    (fun n => lbub j μ (bubbleCoeffL cs i (wt D μ [up j]) n)) =
      bubbleStepL (bubbleEdgeDot (Sc := Sc) i j μ)
        (fun n => rbub j μ (bubbleCoeffL cs i (wt D μ []) n)) := by
  have H := bubbleStep_inverse
    (fun n => rbub j μ (bubbleCoeffR cs i (wt D μ []) n))
    (fun n => lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n))
    (fun n => rbub j μ (bubbleCoeffL cs i (wt D μ []) n))
    (fun n => lbub j μ (bubbleCoeffL cs i (wt D μ [up j]) n))
    (bubbleEdgeDot (Sc := Sc) i j μ)
    (by simp only [rbub, bubbleCoeffR_zero, plcL_id]; rfl)
    (by simp only [lbub, bubbleCoeffR_zero, plcL_id]; rfl)
    (by simp only [rbub, bubbleCoeffL_zero, plcL_id]; rfl)
    (by simp only [lbub, bubbleCoeffL_zero, plcL_id]; rfl)
    (bubbleCoeff_key_place cs i μ [up j] []) (bubbleCoeff_key_place cs i μ [] [up j])
  by_cases hh : D.h i μ ≤ 0
  · have hR : (fun n => rbub j μ (bubbleCoeffR cs i (wt D μ []) n)) =
        bubbleStepR (fun n => lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n))
          (bubbleEdgeDot (Sc := Sc) i j μ) := by
      funext n
      cases n with
      | zero => simp only [bubbleStepR, bubbleCoeffR_zero, rbub, lbub, plcL_id]; rfl
      | succ n => exact bubbleCoeffR_one_nonpos cs i j μ hij hd hh n
    exact ⟨hR, H.mp hR⟩
  · have hL : (fun n => lbub j μ (bubbleCoeffL cs i (wt D μ [up j]) n)) =
        bubbleStepL (bubbleEdgeDot (Sc := Sc) i j μ)
          (fun n => rbub j μ (bubbleCoeffL cs i (wt D μ []) n)) := by
      funext n
      cases n with
      | zero => simp only [bubbleStepL, bubbleCoeffL_zero, rbub, lbub, plcL_id]; rfl
      | succ n => exact bubbleCoeffL_one_pos cs i j μ hij hd (by omega) n
    exact ⟨H.mpr hL, hL⟩

theorem bubbleR_one_succ (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 1) (n : ℕ) :
    rbub j μ (bubRs cs i (wt D μ []) (n + 1)) =
      (Sc.t i j : k) • lbub j μ (bubRs cs i (wt D μ [up j]) (n + 1)) +
        (Sc.t j i : k) • (lbub j μ (bubRs cs i (wt D μ [up j]) n) ≫
          cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i))) := by
  have H := congrFun (bubbleCoeff_one cs i j μ hij hd).1 (n + 1)
  simp only [bubbleStepR, bubbleCoeffR, rbub, lbub, map_smul, bubbleEdgeDot, c_wt_upj,
    Units.val_mul, wt_nil, Nat.cast_add, Nat.cast_one, Linear.smul_comp, Linear.comp_smul,
    smul_smul] at H
  apply (cs.c μ i).isUnit.smul_left_cancel.mp
  simp only [rbub, lbub, wt_nil, smul_add, smul_smul]
  convert H using 1
  congr 1
  · rw [mul_comm]
  · congr 1
    calc
      _ = (Sc.t i j : k) * (↑(Sc.t i j)⁻¹ : k) * (cs.c μ i : k) * (Sc.t j i : k) := by
        rw [Units.mul_inv, one_mul]
      _ = _ := by ring

theorem bubbleL_one_succ (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 1) (n : ℕ) :
    lbub j μ (bubLs cs i (wt D μ [up j]) (n + 1)) =
      (Sc.t i j : k) • rbub j μ (bubLs cs i (wt D μ []) (n + 1)) +
        (Sc.t j i : k) • (cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i)) ≫
          rbub j μ (bubLs cs i (wt D μ []) n)) := by
  have H := congrFun (bubbleCoeff_one cs i j μ hij hd).2 (n + 1)
  simp only [bubbleStepL, bubbleCoeffL, parity_eq_zero_of_d_one hij hd, isg, zero_mul,
    zsign_zero, one_mul, rbub, lbub, map_smul, bubbleEdgeDot, c_wt_upj, mul_inv,
    Units.val_mul, wt_nil, Nat.cast_add, Nat.cast_one, Linear.smul_comp, Linear.comp_smul,
    smul_smul] at H
  apply ((cs.c (wt D μ [up j]) i)⁻¹).isUnit.smul_left_cancel.mp
  simp only [rbub, lbub, wt_nil, smul_add, smul_smul, c_wt_upj, mul_inv, Units.val_mul]
  convert H using 1
  congr 1
  · rw [mul_assoc, mul_comm (↑(cs.c μ i)⁻¹ : k), ← mul_assoc, Units.inv_mul, one_mul]
  · congr 1
    ring
/-- Brundan–Ellis Proposition 7.3(iii), (7.11), for `dᵢⱼ = 1`.
The integer `n` is the shifted degree; negative and fake bubbles are included.
The opposite Cartan entry and all structure scalars are unrestricted. -/
theorem eq_7_11_of_d_one (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 1) (n : ℤ) :
    rbub j μ (bubRs cs i (wt D μ []) n) =
      (Sc.t i j : k) • lbub j μ (bubRs cs i (wt D μ [up j]) n) +
        (Sc.t j i : k) • (lbub j μ (bubRs cs i (wt D μ [up j]) (n - 1)) ≫
          cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i))) := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · simp only [bubRs_neg cs i _ hn, bubRs_neg cs i _ (show n - 1 < 0 by omega),
      rbub, lbub, map_zero, Limits.zero_comp, smul_zero, add_zero]
  · subst n
    simp only [bubRs_zero, bubRs_neg cs i _ (show (0 : ℤ) - 1 < 0 by omega),
      rbub, lbub, map_zero, map_smul, plcL_id, Limits.zero_comp, smul_zero, add_zero,
      c_wt_upj, wt_nil, mul_inv, Units.val_mul, smul_smul]
    erw [plcL_id]
    congr 1
    rw [← mul_assoc, Units.mul_inv, one_mul]
  · have H := bubbleR_one_succ cs i j μ hij hd (n - 1).toNat
    simpa only [Int.toNat_of_nonneg (show 0 ≤ n - 1 by omega),
      sub_add_cancel] using H

/-- Brundan–Ellis Proposition 7.3(iii), (7.12), for `dᵢⱼ = 1`.
This is the counterclockwise, left-to-right slide, at every weight and shifted degree. -/
theorem eq_7_12_of_d_one (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 1) (n : ℤ) :
    lbub j μ (bubLs cs i (wt D μ [up j]) n) =
      (Sc.t i j : k) • rbub j μ (bubLs cs i (wt D μ []) n) +
        (Sc.t j i : k) • (cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i)) ≫
          rbub j μ (bubLs cs i (wt D μ []) (n - 1))) := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · simp only [bubLs_neg cs i _ hn, bubLs_neg cs i _ (show n - 1 < 0 by omega),
      rbub, lbub, map_zero, Limits.comp_zero, smul_zero, add_zero]
  · subst n
    simp only [bubLs_zero, bubLs_neg cs i _ (show (0 : ℤ) - 1 < 0 by omega),
      rbub, lbub, map_zero, map_smul, plcL_id, Limits.comp_zero, smul_zero, add_zero,
      c_wt_upj, wt_nil, Units.val_mul, smul_smul]
    erw [plcL_id]
    rfl
  · have H := bubbleL_one_succ cs i j μ hij hd (n - 1).toNat
    simpa only [Int.toNat_of_nonneg (show 0 ≤ n - 1 by omega),
      sub_add_cancel] using H
end OddMath.SKM
