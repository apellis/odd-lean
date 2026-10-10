/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyLeft
import OddMath.SKM.PlacementHom
/-!
# Chevalley images of homogeneous composites and left cups and caps

The normal-form Chevalley map respects homogeneous composition with its super
sign and respects placement. `Om_etaP` and `Om_epsP` compute the two left
adjunction generators as listed after Proposition 3.5 of Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2. These formulas transport
the upward pitchfork relations to the opposite orientations.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

@[simp] theorem Om_zero (μ : X) (s t : List (Letter I)) :
    Om D Sc μ s t 0 = 0 := by simp [Om]

theorem Om_comp_hom (μ : X) {s t r : List (Letter I)} {p q : ZMod 2}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    {g : (pres D Sc).obj (ob D μ t) ⟶ (pres D Sc).obj (ob D μ r)}
    (hf : f ∈ homPar D Sc μ s t p) (hg : g ∈ homPar D Sc μ t r q) :
    Om D Sc μ s r (f ≫ g) = zsign k (p * q) • (Om D Sc μ t r g ≫ Om D Sc μ s t f) := by
  refine homPar_induction₂ (P := fun f g => Om D Sc μ s r (f ≫ g) =
      zsign k (p * q) • (Om D Sc μ t r g ≫ Om D Sc μ s t f))
    (fun L M hL hp hM hq => ?_)
    (fun g => by simp only [Limits.zero_comp, Om_zero, Limits.comp_zero, smul_zero])
    (fun f => by simp only [Limits.comp_zero, Om_zero, Limits.zero_comp, smul_zero])
    (fun f₁ f₂ g h₁ h₂ => by
      simp only [Preadditive.add_comp, Om_add, Preadditive.comp_add, smul_add, h₁, h₂])
    (fun f g₁ g₂ h₁ h₂ => by
      simp only [Preadditive.comp_add, Om_add, Preadditive.add_comp, smul_add, h₁, h₂])
    (fun a f g h => by
      simp only [Linear.smul_comp, Om_smul, Linear.comp_smul, h, smul_comm a])
    (fun a f g h => by
      simp only [Linear.comp_smul, Om_smul, Linear.smul_comp, h, smul_comm a]) hf hg
  rw [cl_comp hL hM, Om_cl μ (hL.append hM), Om_cl μ hL, Om_cl μ hM,
    Linear.smul_comp, Linear.comp_smul, cl_comp (sChain_omegaL hM) (sChain_omegaL hL),
    omegaL_append, omegaC_append, hp, hq, smul_smul, smul_smul]
  congr 1
  ring

theorem Om_plcL (μ : X) (u v : List (Letter I)) {s t : List (Letter I)} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)}
    (hf : f ∈ homPar D Sc (wt D μ v) s t p) :
    Om D Sc μ (u ++ s ++ v) (u ++ t ++ v) (plcL D Sc μ u v s t f) =
      wordCast (-μ) (by simp only [flipW_append]) (by simp only [flipW_append])
        (plcL D Sc (-μ) (flipW u) (flipW v) (flipW t) (flipW s)
          (regionCast (wt_flipW D μ v).symm (Om D Sc (wt D μ v) s t f))) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, hp, rfl⟩ := hf
    rw [plcL_cl, Om_cl μ (hL.whisk u v), Om_cl _ hL, regionCast_smul, regionCast_cl,
      map_smul, map_smul, plcL_cl, wordCast_cl, omegaC_map_whL, omegaL_map_whL]
  | zero => simp only [map_zero, Om_zero, regionCast_zero]
  | add x y _ _ hx hy => simp only [map_add, Om_add, regionCast_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, Om_smul, regionCast_smul, hx]

variable (cs : CScalars Sc)

theorem Om_etaP (i : I) (μ : X) :
    Om D Sc μ [] [up i, dn i] (etaP cs i μ) =
      (zsign k (ipar D i μ) * (cs.c μ i : k) * (cs.c (-μ) i : k)) • epsP cs i (-μ) := by
  by_cases hh : 0 < D.h i μ
  · rw [etaP_of_pos cs hh, Om_smul, Om_cl μ (sChain_dcupL i _),
      omegaL_dcupL, omegaC_dcupL, epsP_of_neg cs (by rw [coroot_neg]; omega)]
    simp only [coroot_neg, neg_neg, smul_smul, mul_assoc, Units.mul_inv, mul_one]
    have hp : D.parity i * (((D.h i μ - 1).toNat : ℕ) : ZMod 2) = ipar D i μ := by
      rw [natCast_toNat_zmod2 (by omega), ipar]
      push_cast
      generalize D.parity i = p; generalize (D.h i μ : ZMod 2) = q
      revert p q; decide
    rw [hp, mul_comm (cs.c μ i : k)]
    rfl
  · have hn : D.h i μ ≤ 0 := by omega
    rw [etaP_eq_of_nonpos cs hn, Om_smul,
      Om_cl μ ((sChain_etaL i _).append (sChain_lcrossL i i)),
      omegaL_append, omegaL_lcrossL, omegaL_etaL]
    change _ • (_ • cl D Sc (-μ) [dn i, up i] []
      (lcrossL i i ++ ((ddotsL i (-D.h i μ).toNat).map (whL [up i] []) ++ [([], Shape.cap i, [])]))) = _
    rw [← cl_comp (sChain_lcrossL i i) (sChain_dotsCap i _), cl_dotsCap,
      Linear.comp_smul, cl_comp (sChain_lcrossL i i) (sChain_epsL i _),
      epsP_eq_of_nonneg cs (by rw [coroot_neg]; omega)]
    simp only [omegaC_append, omegaC_etaL, omegaC_lcrossL, parsum_etaL, parsum_lcrossL,
      coroot_neg, smul_smul, mul_assoc]
    congr 1
    have hn2 : (((-D.h i μ).toNat : ℕ) : ZMod 2) = -(D.h i μ : ZMod 2) := by
      rw [natCast_toNat_zmod2 (by omega), Int.cast_neg]
    rw [hn2]
    simp only [Int.cast_neg, ipar]
    generalize D.parity i = p; generalize (D.h i μ : ZMod 2) = q
    generalize (((-D.h i μ).toNat / 2 : ℕ) : ZMod 2) = r
    fin_cases p <;> fin_cases q <;> fin_cases r <;>
      simp [zsign, Units.mul_inv]

theorem Om_epsP (i : I) (μ : X) :
    Om D Sc μ [dn i, up i] [] (epsP cs i μ) =
      (zsign k (ipar D i μ) * (↑(cs.c μ i)⁻¹ : k) * (↑(cs.c (-μ) i)⁻¹ : k)) • etaP cs i (-μ) := by
  by_cases hh : D.h i μ < 0
  · rw [epsP_of_neg cs hh, Om_smul, Om_cl μ (sChain_dcapL i _),
      omegaL_dcapL, omegaC_dcapL, etaP_of_pos cs (by rw [coroot_neg]; omega)]
    simp only [coroot_neg, smul_smul, mul_assoc, Units.inv_mul, mul_one]
    have hp : D.parity i * (((-D.h i μ - 1).toNat : ℕ) : ZMod 2) = ipar D i μ := by
      rw [natCast_toNat_zmod2 (by omega), ipar]
      push_cast
      generalize D.parity i = p; generalize (D.h i μ : ZMod 2) = q
      revert p q; decide
    rw [hp, mul_comm (↑(cs.c μ i)⁻¹ : k)]
    rfl
  · have hn : 0 ≤ D.h i μ := by omega
    rw [epsP_eq_of_nonneg cs hn, Om_smul,
      Om_cl μ ((sChain_lcrossL i i).append (sChain_epsL i _)),
      omegaL_append, omegaL_lcrossL, omegaL_epsL]
    change _ • (_ • cl D Sc (-μ) [] [up i, dn i]
      ((([], Shape.cup i, []) :: (ddotsL i (D.h i μ).toNat).map (whL [] [up i])) ++ lcrossL i i)) = _
    rw [← cl_comp (sChain_cupDots i _) (sChain_lcrossL i i), cl_cupDots,
      Linear.smul_comp, cl_comp (sChain_etaL i _) (sChain_lcrossL i i),
      etaP_eq_of_nonpos cs (by rw [coroot_neg]; omega)]
    simp only [omegaC_append, omegaC_epsL, omegaC_lcrossL, parsum_epsL, parsum_lcrossL,
      coroot_neg, neg_neg, smul_smul, mul_assoc]
    congr 1
    have hn2 : (((D.h i μ).toNat : ℕ) : ZMod 2) = (D.h i μ : ZMod 2) :=
      natCast_toNat_zmod2 hn
    rw [hn2]
    simp only [ipar, coroot_neg, Int.cast_neg]
    generalize D.parity i = p; generalize (D.h i μ : ZMod 2) = q
    generalize (((D.h i μ).toNat / 2 : ℕ) : ZMod 2) = r
    fin_cases p <;> fin_cases q <;> fin_cases r <;>
      simp [zsign, Units.inv_mul]

end OddMath.SKM
