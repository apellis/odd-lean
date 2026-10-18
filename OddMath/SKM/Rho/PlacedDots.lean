import OddMath.SKM.Rho.ShiftedBraid
import OddMath.SKM.Rho.BaseWhisker

/-!
# Placed Dots for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.SKM.RhoCoefficients
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem dotFirst3_whisker (t : k) (μ : X) (i j a : I) :
    HEq (QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerRight (B := TwoSRev k (Uqπ D Sc sy hc))
        (rhoDot t (wt D μ (ups [j,a])) i)
        (rhoUpAt (wt D μ (ups [j,a])) μ [j,a] rfl))))
      (dotFirst3 (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ (ups [i,j,a])) μ i j a rfl) := by
  change HEq (QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerLeft (B := Uqπ D Sc sy hc)
      (rhoUpAt (wt D μ (ups [j,a])) μ [j,a] rfl) (rhoDot t (wt D μ (ups [j,a])) i)))) _
  rw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
  change HEq ((pres D Sc).wL (ob D (wt D μ (ups [j,a])) [dn a,dn j])
    (psiCoeff t (D.parity i) • cl D Sc (wt D (wt D μ (ups [j,a])) [up i]) [dn i] [dn i] (ddotL i)))
    (psiCoeff t (D.parity i) • cl D Sc (wt D μ (ups [i,j,a])) [dn a,dn j,dn i] [dn a,dn j,dn i]
      ((ddotL i).map (whL [dn a,dn j] [])))
  have hs : wt D (wt D (wt D μ (ups [j,a])) [up i]) [dn i] = wt D μ (ups [j,a]) := by
    simp [wt, sh]
  have hm := Submodule.smul_mem
    (homPar D Sc (wt D (wt D μ (ups [j,a])) [up i]) [dn i] [dn i]
      (parsum D (ddotL i))) (psiCoeff t (D.parity i)) (cl_mem_homPar (sChain_ddotL i) rfl)
  have H := upward_wL_plcL (Sc := Sc) (wt D μ (ups [j,a])) (wt D (wt D μ (ups [j,a])) [up i])
    [dn a,dn j] [dn i] [dn i] hs hs hm
  simp only [map_smul] at H
  erw [plcL_cl] at H
  exact H

theorem dotMiddle3_whisker (t : k) (μ : X) (i j a : I) :
    HEq (QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerLeft (B := TwoSRev k (Uqπ D Sc sy hc))
        (rhoE (wt D μ (ups [j,a])) i)
        (rhoDotLeft t (wt D μ (ups [j,a])) μ j a rfl))))
      (dotMiddle3 (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ (ups [i,j,a])) μ i j a rfl) := by
  change HEq (QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerRight (B := Uqπ D Sc sy hc)
      (rhoDotLeft t (wt D μ (ups [j,a])) μ j a rfl)
      (rhoE (wt D μ (ups [j,a])) i)))) _
  rw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
  have hwt : wt D (wt D μ (ups [i,j,a])) [dn i] = wt D μ (ups [j,a]) := by simp [ups, wt, sh]
  have hs : wt D (wt D (wt D μ (ups [i,j,a])) [dn i]) [dn a,dn j] = μ := by
    rw [hwt]; simp [ups, wt, sh]
  have hchain : SChain [dn a,dn j] ((ddotL j).map (whL [dn a] [])) [dn a,dn j] :=
    (sChain_ddotL j).wh [dn a] [] rfl rfl
  have hm := Submodule.smul_mem
    (homPar D Sc (wt D (wt D μ (ups [i,j,a])) [dn i]) [dn a,dn j] [dn a,dn j]
      (parsum D ((ddotL j).map (whL [dn a] [])))) (psiCoeff t (D.parity j))
      (cl_mem_homPar hchain rfl)
  have H := upward_wR_plcL (Sc := Sc) μ (wt D μ (ups [i,j,a])) [dn a,dn j] [dn a,dn j] [dn i] hs hs hm
  simp only [map_smul] at H
  rw [plcL_cl] at H
  generalize hleft : wt D (wt D μ (ups [i,j,a])) [dn i] = ξ at hs hm H
  have hξ : ξ = wt D μ (ups [j,a]) := hleft.symm.trans hwt
  clear hleft
  subst ξ
  change HEq ((pres D Sc).wRAt μ
    (psiCoeff t (D.parity j) • cl D Sc (wt D μ (ups [j,a])) [dn a,dn j] [dn a,dn j]
      ((ddotL j).map (whL [dn a] [])))
    (ob D (wt D μ (ups [i,j,a])) [dn i]) (by simp [ob, ups, wt, sh]) (by simp [ob, ups, wt, sh]))
    (psiCoeff t (D.parity j) • cl D Sc (wt D μ (ups [i,j,a])) [dn a,dn j,dn i] [dn a,dn j,dn i]
      ((ddotL j).map (whL [dn a] [dn i])))
  simpa [ups, wt, sh, neg_add_cancel_left, List.map_map, Function.comp_def, whL_whL] using H

theorem dotLast3_whisker (t : k) (μ : X) (i j a : I) :
    HEq (QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerLeft (B := TwoSRev k (Uqπ D Sc sy hc))
        (rhoE (wt D μ (ups [j,a])) i)
        (rhoDotRight t (wt D μ (ups [j,a])) μ j a rfl))))
      (dotLast3 (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ (ups [i,j,a])) μ i j a rfl) := by
  change HEq (QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerRight (B := Uqπ D Sc sy hc)
      (rhoDotRight t (wt D μ (ups [j,a])) μ j a rfl)
      (rhoE (wt D μ (ups [j,a])) i)))) _
  rw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
  have hwt : wt D (wt D μ (ups [i,j,a])) [dn i] = wt D μ (ups [j,a]) := by simp [ups, wt, sh]
  have hs : wt D (wt D (wt D μ (ups [i,j,a])) [dn i]) [dn a,dn j] = μ := by
    rw [hwt]; simp [ups, wt, sh]
  have hchain : SChain [dn a,dn j] ((ddotL a).map (whL [] [dn j])) [dn a,dn j] :=
    (sChain_ddotL a).wh [] [dn j] rfl rfl
  have hm := Submodule.smul_mem
    (homPar D Sc (wt D (wt D μ (ups [i,j,a])) [dn i]) [dn a,dn j] [dn a,dn j]
      (parsum D ((ddotL a).map (whL [] [dn j])))) (psiCoeff t (D.parity a))
      (cl_mem_homPar hchain rfl)
  have H := upward_wR_plcL (Sc := Sc) μ (wt D μ (ups [i,j,a])) [dn a,dn j] [dn a,dn j] [dn i] hs hs hm
  simp only [map_smul] at H
  rw [plcL_cl] at H
  generalize hleft : wt D (wt D μ (ups [i,j,a])) [dn i] = ξ at hs hm H
  have hξ : ξ = wt D μ (ups [j,a]) := hleft.symm.trans hwt
  clear hleft
  subst ξ
  change HEq ((pres D Sc).wRAt μ
    (psiCoeff t (D.parity a) • cl D Sc (wt D μ (ups [j,a])) [dn a,dn j] [dn a,dn j]
      ((ddotL a).map (whL [] [dn j])))
    (ob D (wt D μ (ups [i,j,a])) [dn i]) (by simp [ob, ups, wt, sh]) (by simp [ob, ups, wt, sh]))
    (psiCoeff t (D.parity a) • cl D Sc (wt D μ (ups [i,j,a])) [dn a,dn j,dn i] [dn a,dn j,dn i]
      ((ddotL a).map (whL [] [dn j,dn i])))
  simpa [ups, wt, sh, neg_add_cancel_left, List.map_map, Function.comp_def, whL_whL] using H

end OddMath.SKM.RhoCoefficients
