/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PitchforkCup
import OddMath.SKM.ChevalleyHom
/-!
# Downward pitchfork relations

Both equalities in Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 7.2, (7.6), for all weights and colours.
The Chevalley images of (7.5) have a common invertible coefficient; the
remaining crossing coefficient is the sign `(-1)^(|i||j|)`.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

def pdcupL (i j : I) (μ : X) :
    (pres D Sc).obj (ob D μ [dn j]) ⟶ (pres D Sc).obj (ob D μ [up i, dn j, dn i]) :=
  cupAt cs i μ [] [dn j] ≫
    cl D Sc μ [up i, dn i, dn j] [up i, dn j, dn i] ((dcrossL i j).map (whL [up i] []))

def pdcupR (i j : I) (μ : X) :
    (pres D Sc).obj (ob D μ [dn j]) ⟶ (pres D Sc).obj (ob D μ [up i, dn j, dn i]) :=
  cupAt cs i μ [dn j] [] ≫
    cl D Sc μ [dn j, up i, dn i] [up i, dn j, dn i] ((lcrossL j i).map (whL [] [dn i]))

def pdcapL (i j : I) (μ : X) :
    (pres D Sc).obj (ob D μ [dn i, dn j, up i]) ⟶ (pres D Sc).obj (ob D μ [dn j]) :=
  cl D Sc μ [dn i, dn j, up i] [dn j, dn i, up i] ((dcrossL i j).map (whL [] [up i])) ≫
    capAt cs i μ [dn j] []

def pdcapR (i j : I) (μ : X) :
    (pres D Sc).obj (ob D μ [dn i, dn j, up i]) ⟶ (pres D Sc).obj (ob D μ [dn j]) :=
  cl D Sc μ [dn i, dn j, up i] [dn i, up i, dn j] ((lcrossL j i).map (whL [dn i] [])) ≫
    capAt cs i μ [] [dn j]

theorem cprod_wt_upj (i j : I) (μ : X) :
    cs.c (wt D μ [up j]) i * cs.c (-(wt D μ [up j])) i = cs.c μ i * cs.c (-μ) i := by
  rw [c_wt_upj, mul_assoc, mul_left_comm (Sc.t i j)]
  have h : Sc.t i j * cs.c (-(wt D μ [up j])) i = cs.c (-μ) i := by
    rw [← cs.shift]
    congr 1
    simp [wt, sh]
  rw [h]

theorem cinvprod_wt_upj (i j : I) (μ : X) :
    (cs.c (wt D μ [up j]) i)⁻¹ * (cs.c (-(wt D μ [up j])) i)⁻¹ =
      (cs.c μ i)⁻¹ * (cs.c (-μ) i)⁻¹ := by
  simpa only [mul_inv] using congrArg Inv.inv (cprod_wt_upj cs i j μ)

theorem Om_pfL (i j : I) (μ : X) :
    Om D Sc μ [dn i, up j, up i] [up j] (pfL cs i j μ) =
      (-(zsign k ((D.parity i * D.parity j) * ipar D i μ) *
        zsign k (ipar D i μ) * zsign k (D.parity i * D.parity j)) *
        ((↑(cs.c μ i)⁻¹ : k) * (↑(cs.c (-μ) i)⁻¹ : k))) • pdcupL cs i j (-μ) := by
  have hf : SChain [dn i, up j, up i] (crossL [dn i] j i []) [dn i, up i, up j] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hg : capAt cs i μ [] [up j] ∈ homPar D Sc μ [dn i, up i, up j] [up j] _ :=
    plcL_mem _ [] [up j] (epsP_mem cs i _)
  rw [pfL, Om_comp_hom μ (cl_mem_homPar hf rfl) hg, Om_cl μ hf]
  erw [Om_plcL μ [] [up j] (epsP_mem cs i _), Om_epsP]
  simp only [regionCast_smul, regionCast_family, flipW_cons, flipW_nil, flipL_up, flipL_dn,
    wordCast, parsum, parity_crossL]
  simp only [crossL, omegaL_cons, omegaL_nil, omegaC_cons, omegaC_nil, parsum_nil, mul_zero,
    zsign_zero, one_mul, mul_one, List.nil_append, chevC, chevL]
  change zsign k (D.parity j * D.parity i * ipar D i (wt D μ [up j])) •
    (plcL D Sc (-μ) [] [dn j] [] [up i, dn i]
      ((zsign k (ipar D i (wt D μ [up j])) * (↑(cs.c (wt D μ [up j]) i)⁻¹ : k) *
        (↑(cs.c (-wt D μ [up j]) i)⁻¹ : k)) • etaP cs i (wt D (-μ) [dn j])) ≫
      (-zsign k (D.parity j * D.parity i) •
        cl D Sc (-μ) [up i, dn i, dn j] [up i, dn j, dn i]
          ((dcrossL i j).map (whL [up i] [])))) = _
  rw [map_smul, Linear.smul_comp, Linear.comp_smul, smul_smul, smul_smul, ipar_wt_upj]
  change _ • pdcupL cs i j (-μ) = _
  congr 1
  have hc := congrArg (fun x : kˣ => (x : k)) (cinvprod_wt_upj cs i j μ)
  simp only [Units.val_mul] at hc
  rw [mul_comm (D.parity j) (D.parity i)]
  linear_combination -(zsign k ((D.parity i * D.parity j) * ipar D i μ) *
    zsign k (ipar D i μ) * zsign k (D.parity i * D.parity j)) * hc

theorem Om_pfR (i j : I) (μ : X) :
    Om D Sc μ [dn i, up j, up i] [up j] (pfR cs i j μ) =
      (-(zsign k ((D.parity i * D.parity j) * ipar D i μ) * zsign k (ipar D i μ)) *
        ((↑(cs.c μ i)⁻¹ : k) * (↑(cs.c (-μ) i)⁻¹ : k))) • pdcupR cs i j (-μ) := by
  have hf : SChain [dn i, up j, up i] ((lcrossL i j).map (whL [] [up i])) [up j, dn i, up i] := by
    simpa using (sChain_lcrossL i j).whisk [] [up i]
  have hg : capAt cs i μ [up j] [] ∈ homPar D Sc μ [up j, dn i, up i] [up j] _ :=
    plcL_mem _ [up j] [] (epsP_mem cs i _)
  rw [pfR]
  erw [Om_comp_hom μ (cl_mem_homPar hf rfl) hg, Om_cl μ hf,
    Om_plcL μ [up j] [] (epsP_mem cs i _), Om_epsP]
  simp only [regionCast_smul, regionCast_family, flipW_cons, flipW_nil, flipL_up, flipL_dn,
    wordCast, parsum_map_whL, parsum_lcrossL, omegaL_map_whL, omegaC_map_whL,
    omegaL_lcrossL, omegaC_lcrossL]
  change zsign k ((D.parity i * D.parity j) * ipar D i μ) •
    (plcL D Sc (-μ) [dn j] [] [] [up i, dn i]
      ((zsign k (ipar D i μ) * (↑(cs.c μ i)⁻¹ : k) * (↑(cs.c (-μ) i)⁻¹ : k)) •
        etaP cs i (wt D (-μ) [])) ≫
      ((-1 : k) • cl D Sc (-μ) [dn j, up i, dn i] [up i, dn j, dn i]
        ((lcrossL j i).map (whL [] [dn i])))) = _
  rw [map_smul, Linear.smul_comp, Linear.comp_smul, smul_smul, smul_smul]
  change _ • pdcupR cs i j (-μ) = _
  congr 1
  ring

theorem Om_pcuL (i j : I) (μ : X) :
    Om D Sc μ [up j] [up i, up j, dn i] (pcuL cs i j μ) =
      (-(zsign k (ipar D i μ * (D.parity i * D.parity j)) *
        zsign k (ipar D i μ) * zsign k (D.parity i * D.parity j)) *
        ((cs.c μ i : k) * (cs.c (-μ) i : k))) • pdcapL cs i j (-μ) := by
  have hf : cupAt cs i μ [up j] [] ∈ homPar D Sc μ [up j] [up j, up i, dn i] _ :=
    plcL_mem _ [up j] [] (etaP_mem cs i _)
  have hg : SChain [up j, up i, dn i] (crossL [] j i [dn i]) [up i, up j, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  rw [pcuL, Om_comp_hom μ hf (cl_mem_homPar hg rfl), Om_cl μ hg]
  erw [Om_plcL μ [up j] [] (etaP_mem cs i _), Om_etaP]
  simp only [regionCast_smul, regionCast_family, flipW_cons, flipW_nil, flipL_up, flipL_dn,
    wordCast, parsum, parity_crossL]
  simp only [crossL, omegaL_cons, omegaL_nil, omegaC_cons, omegaC_nil, parsum_nil, mul_zero,
    zsign_zero, one_mul, mul_one, List.nil_append, chevC, chevL]
  change zsign k (ipar D i μ * (D.parity j * D.parity i)) •
    ((-zsign k (D.parity j * D.parity i) •
      cl D Sc (-μ) [dn i, dn j, up i] [dn j, dn i, up i]
        ((dcrossL i j).map (whL [] [up i]))) ≫
      plcL D Sc (-μ) [dn j] [] [dn i, up i] []
        ((zsign k (ipar D i μ) * (cs.c μ i : k) * (cs.c (-μ) i : k)) •
          epsP cs i (wt D (-μ) []))) = _
  rw [map_smul, Linear.smul_comp, Linear.comp_smul, smul_smul, smul_smul]
  change _ • pdcapL cs i j (-μ) = _
  congr 1
  rw [mul_comm (D.parity j) (D.parity i)]
  ring

theorem Om_pcuR (i j : I) (μ : X) :
    Om D Sc μ [up j] [up i, up j, dn i] (pcuR cs i j μ) =
      (-(zsign k (ipar D i μ * (D.parity i * D.parity j)) * zsign k (ipar D i μ)) *
        ((cs.c μ i : k) * (cs.c (-μ) i : k))) • pdcapR cs i j (-μ) := by
  have hf : cupAt cs i μ [] [up j] ∈ homPar D Sc μ [up j] [up i, dn i, up j] _ :=
    plcL_mem _ [] [up j] (etaP_mem cs i _)
  have hg : SChain [up i, dn i, up j] ((lcrossL i j).map (whL [up i] [])) [up i, up j, dn i] := by
    simpa using (sChain_lcrossL i j).whisk [up i] []
  rw [pcuR, Om_comp_hom μ hf (cl_mem_homPar hg rfl), Om_cl μ hg]
  erw [Om_plcL μ [] [up j] (etaP_mem cs i _), Om_etaP]
  simp only [regionCast_smul, regionCast_family, flipW_cons, flipW_nil, flipL_up, flipL_dn,
    wordCast, parsum_map_whL, parsum_lcrossL, omegaL_map_whL, omegaC_map_whL,
    omegaL_lcrossL, omegaC_lcrossL]
  change zsign k (ipar D i (wt D μ [up j]) * (D.parity i * D.parity j)) •
    (((-1 : k) • cl D Sc (-μ) [dn i, dn j, up i] [dn i, up i, dn j]
      ((lcrossL j i).map (whL [dn i] []))) ≫
      plcL D Sc (-μ) [] [dn j] [dn i, up i] []
        ((zsign k (ipar D i (wt D μ [up j])) * (cs.c (wt D μ [up j]) i : k) *
          (cs.c (-wt D μ [up j]) i : k)) • epsP cs i (wt D (-μ) [dn j]))) = _
  rw [map_smul, Linear.smul_comp, Linear.comp_smul, smul_smul, smul_smul, ipar_wt_upj]
  change _ • pdcapR cs i j (-μ) = _
  congr 1
  have hc := congrArg (fun x : kˣ => (x : k)) (cprod_wt_upj cs i j μ)
  simp only [Units.val_mul] at hc
  linear_combination -(zsign k (ipar D i μ * (D.parity i * D.parity j)) * zsign k (ipar D i μ)) * hc

theorem pitchfork_scalar_cancel {M : Type*} [AddCommGroup M] [Module k M]
    (u : kˣ) (p q r : ZMod 2) {f g : M}
    (h : (-(zsign k p * zsign k q * zsign k r) * (u : k)) • f =
      (-(zsign k p * zsign k q) * (u : k)) • g) : f = zsign k r • g := by
  have hu : IsUnit (-(zsign k p * zsign k q) * (u : k)) :=
    ((zsign_isUnit p).mul (zsign_isUnit q)).neg.mul u.isUnit
  have hs : -(zsign k p * zsign k q * zsign k r) * (u : k) =
      (-(zsign k p * zsign k q) * (u : k)) * zsign k r := by ring
  rw [hs, mul_smul] at h
  rcases hu with ⟨a, ha⟩
  rw [← ha] at h
  have E := congrArg ((↑a⁻¹ : k) • ·) h
  simp only [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, one_smul] at E
  rw [← E, smul_smul, zsign_mul_self', one_smul]

/-- The downward-strand cup equality of Proposition 7.2, (7.6). -/
theorem eq_7_6_a (i j : I) (μ : X) :
    pdcupL cs i j μ = zsign k (D.parity i * D.parity j) • pdcupR cs i j μ := by
  have E := congrArg (Om D Sc (-μ) [dn i, up j, up i] [up j]) (eq_7_5_a cs i j (-μ))
  rw [Om_pfL, Om_pfR] at E
  simp only [neg_neg] at E
  have E' := pitchfork_scalar_cancel ((cs.c (-μ) i)⁻¹ * (cs.c μ i)⁻¹) _ _ _ E
  have E'' := congrArg (regionCast (D := D) (Sc := Sc)
    (s := [dn j]) (t := [up i, dn j, dn i]) (neg_neg μ)) E'
  simpa only [regionCast_family, regionCast_smul] using E''

/-- The downward-strand cap equality of Proposition 7.2, (7.6). -/
theorem eq_7_6_b (i j : I) (μ : X) :
    pdcapL cs i j μ = zsign k (D.parity i * D.parity j) • pdcapR cs i j μ := by
  have E := congrArg (Om D Sc (-μ) [up j] [up i, up j, dn i]) (eq_7_5_b cs i j (-μ))
  rw [Om_pcuL, Om_pcuR] at E
  simp only [neg_neg] at E
  have E' := pitchfork_scalar_cancel (cs.c (-μ) i * cs.c μ i) _ _ _ E
  have E'' := congrArg (regionCast (D := D) (Sc := Sc)
    (s := [dn i, dn j, up i]) (t := [dn j]) (neg_neg μ)) E'
  simpa only [regionCast_family, regionCast_smul] using E''

end OddMath.SKM
