import OddMath.SKM.Rho.Entries

/-!
# Inversion for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoInversionKernel
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords RhoEvaluator RhoMixed
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem kernel_invP₁ (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (hh : 0 ≤ D.h i μ) :
    rhoLin (sy := sy) (hc := hc) t μ μ (wt_ud μ i) (wt_ud μ i)
      (relation D Sc (.invP₁ i μ hh)) = 0 := by
  apply kernel_of_norm
  change normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ (wt_ud μ i) (wt_ud μ i)
    (-dg D μ (t := [up i, dn i]) (t' := [up i, dn i]) (sigmaL i i ++ lcrossL i i)
        ((sChain_sigmaL i i).append (sChain_lcrossL i i)) +
      ∑ n ∈ Finset.range (D.h i μ).toNat,
        dg D μ (t := [up i, dn i]) (t' := [up i, dn i]) (epsL i n ++ dcupL i n)
          ((sChain_epsL i n).append (sChain_dcupL i n)) - idg D μ [up i, dn i]) = 0
  simp only [map_sub, map_add, map_neg, map_sum, norm_idg,
    norm_append (Sc := Sc) (sy := sy) (hc := hc) t μ μ (wt_ud μ i) (wt_du μ i) (wt_ud μ i),
    norm_append (Sc := Sc) (sy := sy) (hc := hc) t μ μ (m := []) (wt_ud μ i) rfl (wt_ud μ i),
    sChain_sigmaL, sChain_lcrossL, sChain_epsL, sChain_dcupL,
    norm_sigma, norm_lcross, norm_eps, norm_dcup]
  rw [matrixP₁ t ht μ i hh]
  exact sub_self _

theorem kernel_invP₂ (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (hh : 0 ≤ D.h i μ) :
    rhoLin (sy := sy) (hc := hc) t μ μ (s := [dn i, up i]) (r := [dn i, up i]) (wt_du μ i) (wt_du μ i)
      (relation D Sc (.invP₂ i μ hh)) = 0 := by
  apply kernel_of_norm
  change normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := [dn i, up i]) (r := [dn i, up i]) (wt_du μ i) (wt_du μ i)
    (dg D μ (t := [dn i, up i]) (t' := [dn i, up i]) (lcrossL i i ++ sigmaL i i) ((sChain_lcrossL i i).append (sChain_sigmaL i i)) + idg D μ [dn i, up i]) = 0
  simp only [map_add, norm_idg, norm_append (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := [dn i, up i]) (m := [up i, dn i]) (r := [dn i, up i]) (wt_du μ i) (wt_ud μ i) (wt_du μ i), sChain_lcrossL, sChain_sigmaL, norm_lcross, norm_sigma]
  rw [matrixP₂ t ht μ i hh]
  exact neg_add_cancel _

theorem kernel_invP₃ (t : k) (μ : X) (i : I) (m : ℕ) (hm : (m : ℤ) < D.h i μ) :
    rhoLin (sy := sy) (hc := hc) t μ μ (s := [dn i, up i]) (r := []) (wt_du μ i) rfl
      (relation D Sc (.invP₃ i μ m hm)) = 0 := by
  apply kernel_of_norm
  change normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := [dn i, up i]) (r := []) (wt_du μ i) rfl
    (dg D μ (t := [dn i, up i]) (t' := []) (lcrossL i i ++ epsL i m) ((sChain_lcrossL i i).append (sChain_epsL i m))) = 0
  simp only [norm_append (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := [dn i, up i]) (m := [up i, dn i]) (r := []) (wt_du μ i) (wt_ud μ i) rfl, sChain_lcrossL, sChain_epsL, norm_lcross, norm_eps]
  exact matrixP₃ t μ i m hm

theorem kernel_invP₄ (t : k) (μ : X) (i : I) (n : ℕ) (hn : (n : ℤ) < D.h i μ) :
    rhoLin (sy := sy) (hc := hc) t μ μ (s := []) (r := [dn i, up i]) rfl (wt_du μ i)
      (relation D Sc (.invP₄ i μ n hn)) = 0 := by
  apply kernel_of_norm
  change normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := []) (r := [dn i, up i]) rfl (wt_du μ i)
    (dg D μ (t := []) (t' := [dn i, up i]) (dcupL i n ++ sigmaL i i) ((sChain_dcupL i n).append (sChain_sigmaL i i))) = 0
  simp only [norm_append (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := []) (m := [up i, dn i]) (r := [dn i, up i]) rfl (wt_ud μ i) (wt_du μ i), sChain_dcupL, sChain_sigmaL, norm_dcup, norm_sigma]
  exact matrixP₄ t μ i n hn

theorem kernel_invP₅ (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (m n : ℕ) (hm : (m : ℤ) < D.h i μ) (hn : (n : ℤ) < D.h i μ) :
    rhoLin (sy := sy) (hc := hc) t μ μ (s := []) (r := []) rfl rfl
      (relation D Sc (.invP₅ i μ m n hm hn)) = 0 := by
  apply kernel_of_norm
  change normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := []) (r := []) rfl rfl
    (dg D μ (t := []) (t' := []) (dcupL i n ++ epsL i m) ((sChain_dcupL i n).append (sChain_epsL i m)) - if m = n then idg D μ [] else 0) = 0
  simp only [map_sub, apply_ite, map_zero, norm_idg, norm_append (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := []) (m := [up i, dn i]) (r := []) rfl (wt_ud μ i) rfl, sChain_dcupL, sChain_epsL, norm_dcup, norm_eps]
  rw [matrixP₅ t ht μ i m n hm hn]
  split_ifs <;> exact sub_self _

theorem kernel_invM₂ (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (hh : D.h i μ ≤ 0) :
    rhoLin (sy := sy) (hc := hc) t μ μ (s := [up i, dn i]) (r := [up i, dn i]) (wt_ud μ i) (wt_ud μ i)
      (relation D Sc (.invM₂ i μ hh)) = 0 := by
  apply kernel_of_norm
  change normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := [up i, dn i]) (r := [up i, dn i]) (wt_ud μ i) (wt_ud μ i)
    (dg D μ (t := [up i, dn i]) (t' := [up i, dn i]) (sigmaL i i ++ lcrossL i i) ((sChain_sigmaL i i).append (sChain_lcrossL i i)) + idg D μ [up i, dn i]) = 0
  simp only [map_add, norm_idg, norm_append (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := [up i, dn i]) (m := [dn i, up i]) (r := [up i, dn i]) (wt_ud μ i) (wt_du μ i) (wt_ud μ i), sChain_sigmaL, sChain_lcrossL, norm_sigma, norm_lcross]
  rw [matrixM₂ t ht μ i hh]
  exact neg_add_cancel _

theorem kernel_invM₃ (t : k) (μ : X) (i : I) (m : ℕ) (hm : (m : ℤ) < -D.h i μ) :
    rhoLin (sy := sy) (hc := hc) t μ μ (s := []) (r := [up i, dn i]) rfl (wt_ud μ i)
      (relation D Sc (.invM₃ i μ m hm)) = 0 := by
  apply kernel_of_norm
  change normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := []) (r := [up i, dn i]) rfl (wt_ud μ i)
    (dg D μ (t := []) (t' := [up i, dn i]) (etaL i m ++ lcrossL i i) ((sChain_etaL i m).append (sChain_lcrossL i i))) = 0
  simp only [norm_append (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := []) (m := [dn i, up i]) (r := [up i, dn i]) rfl (wt_du μ i) (wt_ud μ i), sChain_etaL, sChain_lcrossL, norm_eta, norm_lcross]
  exact matrixM₃ t μ i m hm

theorem kernel_invM₄ (t : k) (μ : X) (i : I) (n : ℕ) (hn : (n : ℤ) < -D.h i μ) :
    rhoLin (sy := sy) (hc := hc) t μ μ (s := [up i, dn i]) (r := []) (wt_ud μ i) rfl
      (relation D Sc (.invM₄ i μ n hn)) = 0 := by
  apply kernel_of_norm
  change normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := [up i, dn i]) (r := []) (wt_ud μ i) rfl
    (dg D μ (t := [up i, dn i]) (t' := []) (sigmaL i i ++ dcapL i n) ((sChain_sigmaL i i).append (sChain_dcapL i n))) = 0
  simp only [norm_append (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := [up i, dn i]) (m := [dn i, up i]) (r := []) (wt_ud μ i) (wt_du μ i) rfl, sChain_sigmaL, sChain_dcapL, norm_sigma, norm_dcap]
  exact matrixM₄ t μ i n hn

theorem kernel_invM₅ (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (m n : ℕ) (hm : (m : ℤ) < -D.h i μ) (hn : (n : ℤ) < -D.h i μ) :
    rhoLin (sy := sy) (hc := hc) t μ μ (s := []) (r := []) rfl rfl
      (relation D Sc (.invM₅ i μ m n hm hn)) = 0 := by
  apply kernel_of_norm
  change normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := []) (r := []) rfl rfl
    (dg D μ (t := []) (t' := []) (etaL i m ++ dcapL i n) ((sChain_etaL i m).append (sChain_dcapL i n)) - if m = n then idg D μ [] else 0) = 0
  simp only [map_sub, apply_ite, map_zero, norm_idg, norm_append (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := []) (m := [dn i, up i]) (r := []) rfl (wt_du μ i) rfl, sChain_etaL, sChain_dcapL, norm_eta, norm_dcap]
  rw [matrixM₅ t ht μ i m n hm hn]
  split_ifs <;> exact sub_self _

theorem kernel_invM₁ (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (hh : D.h i μ ≤ 0) :
    rhoLin (sy := sy) (hc := hc) t μ μ (wt_du μ i) (wt_du μ i)
      (relation D Sc (.invM₁ i μ hh)) = 0 := by
  apply kernel_of_norm
  change normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ (wt_du μ i) (wt_du μ i)
    (-dg D μ (t := [dn i, up i]) (t' := [dn i, up i]) (lcrossL i i ++ sigmaL i i)
        ((sChain_lcrossL i i).append (sChain_sigmaL i i)) +
      ∑ n ∈ Finset.range (-D.h i μ).toNat,
        dg D μ (t := [dn i, up i]) (t' := [dn i, up i]) (dcapL i n ++ etaL i n)
          ((sChain_dcapL i n).append (sChain_etaL i n)) - idg D μ [dn i, up i]) = 0
  simp only [map_sub, map_add, map_neg, map_sum, norm_idg,
    norm_append (Sc := Sc) (sy := sy) (hc := hc) t μ μ (wt_du μ i) (wt_ud μ i) (wt_du μ i),
    norm_append (Sc := Sc) (sy := sy) (hc := hc) t μ μ (m := []) (wt_du μ i) rfl (wt_du μ i),
    sChain_sigmaL, sChain_lcrossL, sChain_dcapL, sChain_etaL,
    norm_sigma, norm_lcross, norm_dcap, norm_eta]
  rw [matrixM₁ t ht μ i hh]
  exact sub_self _

theorem kernel_dcupZero (t : k) (μ : X) (i : I) (n : ℕ) (hn : D.h i μ ≤ n) :
    rhoLin (sy := sy) (hc := hc) t μ μ (s := []) (r := [up i, dn i]) rfl (wt_ud μ i)
      (relation D Sc (.dcupZero i μ n hn)) = 0 := by
  apply kernel_of_norm
  change normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := []) (r := [up i, dn i]) rfl (wt_ud μ i)
    (dg D μ (dcupL i n) (sChain_dcupL i n)) = 0
  rw [norm_dcup]
  exact cupDiamond_zero t μ i n hn

theorem kernel_dcapZero (t : k) (μ : X) (i : I) (n : ℕ) (hn : -D.h i μ ≤ n) :
    rhoLin (sy := sy) (hc := hc) t μ μ (s := [dn i, up i]) (r := []) (wt_du μ i) rfl
      (relation D Sc (.dcapZero i μ n hn)) = 0 := by
  apply kernel_of_norm
  change normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ (s := [dn i, up i]) (r := []) (wt_du μ i) rfl
    (dg D μ (dcapL i n) (sChain_dcapL i n)) = 0
  rw [norm_dcap]
  exact capDiamond_zero t μ i n hn

theorem kernel_invNe₁ (t : k) (ht : t ^ 2 = -1) (μ : X) (i j : I) (hij : i ≠ j) :
    rhoLin (sy := sy) (hc := hc) t (wt D μ [up j, dn i]) μ (s := [up j, dn i]) (r := [up j, dn i]) rfl rfl
      (relation D Sc (.invNe₁ i j μ hij)) = 0 := by
  apply kernel_of_norm
  change normLin (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up j, dn i]) μ
    (s := [up j, dn i]) (r := [up j, dn i]) rfl rfl
    (dg D μ (t := [up j, dn i]) (t' := [up j, dn i]) (sigmaL i j ++ lcrossL i j)
      ((sChain_sigmaL i j).append (sChain_lcrossL i j)) - idg D μ [up j, dn i]) = 0
  have hm : wt D μ [dn i, up j] = wt D μ [up j, dn i] := by simp [wt, sh, add_comm, add_left_comm, add_assoc]
  simp only [map_sub, norm_idg,
    norm_append (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up j, dn i]) μ
      (s := [up j, dn i]) (m := [dn i, up j]) (r := [up j, dn i]) rfl hm rfl,
    sChain_sigmaL, sChain_lcrossL, norm_sigma, norm_lcross]
  rw [mixed_invNe₁ t ht (wt D μ [up j, dn i]) i j hij]
  exact sub_self _

theorem kernel_invNe₂ (t : k) (ht : t ^ 2 = -1) (μ : X) (i j : I) (hij : i ≠ j) :
    rhoLin (sy := sy) (hc := hc) t (wt D μ [dn i, up j]) μ (s := [dn i, up j]) (r := [dn i, up j]) rfl rfl
      (relation D Sc (.invNe₂ i j μ hij)) = 0 := by
  apply kernel_of_norm
  change normLin (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [dn i, up j]) μ
    (s := [dn i, up j]) (r := [dn i, up j]) rfl rfl
    (dg D μ (t := [dn i, up j]) (t' := [dn i, up j]) (lcrossL i j ++ sigmaL i j)
      ((sChain_lcrossL i j).append (sChain_sigmaL i j)) - idg D μ [dn i, up j]) = 0
  have hm : wt D μ [up j, dn i] = wt D μ [dn i, up j] := by simp [wt, sh, add_comm, add_left_comm, add_assoc]
  simp only [map_sub, norm_idg,
    norm_append (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [dn i, up j]) μ
      (s := [dn i, up j]) (m := [up j, dn i]) (r := [dn i, up j]) rfl hm rfl,
    sChain_sigmaL, sChain_lcrossL, norm_sigma, norm_lcross]
  rw [mixed_invNe₂ t ht (wt D μ [dn i, up j]) i j hij]
  exact sub_self _

end OddMath.SKM.RhoInversionKernel
