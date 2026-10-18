import OddMath.SKM.RhoGenerators

/-!
# Base Whisker for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.SKM.RhoCoefficients
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem left_whisker_no_sign (t : k) (μ : X) (i j : I) :
    QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerRight (B := TwoSRev k (Uqπ D Sc sy hc))
        (rhoDot t (wt D μ [up j]) i) (rhoE μ j))) =
    BicategoryStruct.whiskerLeft (B := UGr D Sc sy hc)
      (rhoE (Sc := Sc) (sy := sy) (hc := hc) μ j).obj.obj
      (QEnvelope.toHom (Envelope.toHom (rhoDot t (wt D μ [up j]) i))) := by
  change QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerLeft (B := Uqπ D Sc sy hc)
      (rhoE μ j) (rhoDot t (wt D μ [up j]) i))) = _
  rw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
  rfl

theorem right_whisker_no_sign (t : k) (μ : X) (i j : I) :
    QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerLeft (B := TwoSRev k (Uqπ D Sc sy hc))
        (rhoE (wt D μ [up j]) i) (rhoDot t μ j))) =
    BicategoryStruct.whiskerRight (B := UGr D Sc sy hc)
      (QEnvelope.toHom (Envelope.toHom (rhoDot t μ j)))
      (rhoE (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [up j]) i).obj.obj := by
  change QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerRight (B := Uqπ D Sc sy hc)
      (rhoDot t μ j) (rhoE (wt D μ [up j]) i))) = _
  rw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
  rfl

private theorem ob_tensor (ν μ : X) (u s : List (Letter I)) (h : wt D μ s = ν) :
    (ob D ν u).tensor (ob D μ s) = ob D μ (u ++ s ++ []) := by
  apply Obj.ext
  · change wt D ν u = wt D μ (u ++ s ++ [])
    simp only [List.append_nil, wt_append, h]
  · change wd D ν u ++ wd D μ s = wd D μ (u ++ s ++ [])
    simp only [List.append_nil, wd_append, h]

private theorem raw_heq {C : Type*} [Category C] {a b a' b' : C}
    (ha : a = a') (hb : b = b') {f : a ⟶ b} {g : a' ⟶ b'}
    (h : f = eqToHom ha ≫ g ≫ eqToHom hb.symm) : HEq f g := by
  subst ha; subst hb
  exact heq_of_eq (by simpa using h)

private theorem wL_plcL (ν μ : X) (u s t : List (Letter I))
    (hs : wt D μ s = ν) (ht : wt D μ t = ν) {p : ZMod 2}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ homPar D Sc μ s t p) :
    HEq ((pres D Sc).wL (ob D ν u) f) (plcL D Sc μ u [] s t f) := by
  apply raw_heq (congrArg (pres D Sc).obj (ob_tensor ν μ u s hs))
    (congrArg (pres D Sc).obj (ob_tensor ν μ u t ht))
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, _, rfl⟩ := hf
    erw [plcL_cl]
    rw [cl_of hL]
    have hcomp : (ob D ν u).Composable (ob D μ s) :=
      Presentation.Bicat.Hom.composable
        (psiWordAt (Sc := Sc) (wt D ν u) ν u rfl) (psiWordAt ν μ s hs)
    rw [Presentation.wL_diag_of_composable _ _ _ hcomp]
    rw [cl_of (hL.whisk u [])]
    refine Presentation.diag_eq_of_layers_eq' _ _ _ (ob_tensor ν μ u s hs)
      (ob_tensor ν μ u t ht) ?_
    simp only [Diagram.layers_lwhisker, layers_mkD]
    rw [← layList_whisker D μ u [] hL]
    simp only [wt_nil, hs, wd, Layer.wl, Layer.whisker, List.append_nil]
  | zero => simp only [Presentation.wL_zero, map_zero, Limits.comp_zero, Limits.zero_comp]
  | add f g _ _ ihf ihg =>
    simp only [Presentation.wL_add, map_add, Preadditive.comp_add, Preadditive.add_comp, ihf, ihg]
  | smul a f _ ih =>
    simp only [Presentation.wL_smul, map_smul, Linear.comp_smul, Linear.smul_comp, ih]
private theorem ob_tensor_right (μ : X) (s v : List (Letter I)) :
    (ob D (wt D μ v) s).tensor (ob D μ v) = ob D μ ([] ++ s ++ v) := by
  simpa only [List.append_nil, List.nil_append] using ob_tensor (wt D μ v) μ s v rfl

private theorem wR_plcL (ν μ : X) (s t v : List (Letter I))
    (hs : wt D (wt D μ v) s = ν) (ht : wt D (wt D μ v) t = ν) {p : ZMod 2}
    {f : (pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)}
    (hf : f ∈ homPar D Sc (wt D μ v) s t p) :
    HEq ((pres D Sc).wRAt ν f (ob D μ v) hs ht) (plcL D Sc μ [] v s t f) := by
  apply raw_heq (congrArg (pres D Sc).obj (ob_tensor_right μ s v))
    (congrArg (pres D Sc).obj (ob_tensor_right μ t v))
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, _, rfl⟩ := hf
    rw [plcL_cl, cl_of hL]
    have hcomp : (ob D (wt D μ v) s).Composable (ob D μ v) :=
      Presentation.Bicat.Hom.composable
        (psiWordAt (Sc := Sc) ν (wt D μ v) s hs) (psiWordAt (wt D μ v) μ v rfl)
    rw [Presentation.wRAt_diag _ _ _ hcomp]
    rw [cl_of (hL.whisk [] v)]
    refine Presentation.diag_eq_of_layers_eq' _ _ _ (ob_tensor_right μ s v)
      (ob_tensor_right μ t v) ?_
    simp only [Diagram.layers_rwhisker, layers_mkD]
    rw [← layList_whisker D μ [] v hL]
    simp only [ob, wd, Layer.wr, Layer.whisker, List.nil_append]
    apply List.map_congr_left
    intro l hl
    apply Layer.ext
    · exact (Diagram.chain (mkD D (wt D μ v) L hL)).start_of_mem (L := l) hl
    all_goals rfl
  | zero => simp only [Presentation.wRAt_zero, map_zero, Limits.comp_zero, Limits.zero_comp]
  | add f g _ _ ihf ihg =>
    simp only [Presentation.wRAt_add, map_add, Preadditive.comp_add, Preadditive.add_comp, ihf, ihg]
  | smul a f _ ih =>
    simp only [Presentation.wRAt_smul, map_smul, Linear.comp_smul, Linear.smul_comp, ih]

theorem left_whisker_layers (t : k) (μ : X) (i j : I) :
    HEq (QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerRight (B := TwoSRev k (Uqπ D Sc sy hc))
        (rhoDot t (wt D μ [up j]) i) (rhoE μ j))))
      (rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ (ups [i,j])) μ i j rfl) := by
  rw [left_whisker_no_sign]
  change HEq ((pres D Sc).wL (ob D (wt D μ [up j]) [dn j])
    (psiCoeff t (D.parity i) • cl D Sc (wt D (wt D μ [up j]) [up i]) [dn i] [dn i] (ddotL i)))
    (psiCoeff t (D.parity i) • cl D Sc (wt D μ (ups [i,j])) [dn j,dn i] [dn j,dn i]
      ((ddotL i).map (whL [dn j] [])))
  have hwt : wt D (wt D (wt D μ [up j]) [up i]) [dn i] = wt D μ [up j] := by simp [wt, sh]
  have hm := Submodule.smul_mem (homPar D Sc (wt D (wt D μ [up j]) [up i]) [dn i] [dn i]
    (parsum D (ddotL i))) (psiCoeff t (D.parity i)) (cl_mem_homPar (sChain_ddotL i) rfl)
  have H := wL_plcL (Sc := Sc) (wt D μ [up j]) (wt D (wt D μ [up j]) [up i])
    [dn j] [dn i] [dn i] hwt hwt hm
  simp only [map_smul] at H
  erw [plcL_cl] at H
  exact H

theorem right_whisker_layers (t : k) (μ : X) (i j : I) :
    HEq (QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerLeft (B := TwoSRev k (Uqπ D Sc sy hc))
        (rhoE (wt D μ [up j]) i) (rhoDot t μ j))))
      (rhoDotRight (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ (ups [i,j])) μ i j rfl) := by
  rw [right_whisker_no_sign]
  have hwt : wt D (wt D μ (ups [i,j])) [dn i] = wt D μ [up j] := by simp [ups, wt, sh]
  have hs : wt D (wt D (wt D μ (ups [i,j])) [dn i]) [dn j] = μ := by
    rw [hwt]; simp [wt, sh]
  have hm := Submodule.smul_mem (homPar D Sc (wt D (wt D μ (ups [i,j])) [dn i]) [dn j] [dn j]
    (parsum D (ddotL j))) (psiCoeff t (D.parity j)) (cl_mem_homPar (sChain_ddotL j) rfl)
  have H := wR_plcL (Sc := Sc) μ (wt D μ (ups [i,j])) [dn j] [dn j] [dn i] hs hs hm
  simp only [map_smul] at H
  rw [plcL_cl] at H
  generalize hleft : wt D (wt D μ (ups [i,j])) [dn i] = ξ at hs hm H
  have hξ : ξ = wt D μ [up j] := hleft.symm.trans hwt
  clear hleft
  subst ξ
  change HEq ((pres D Sc).wRAt μ
    (psiCoeff t (D.parity j) • cl D Sc (wt D μ [up j]) [dn j] [dn j] (ddotL j))
    (ob D (wt D μ (ups [i,j])) [dn i]) (by simp [ob, wt, sh]) (by simp [ob, wt, sh]))
    (psiCoeff t (D.parity j) • cl D Sc (wt D μ (ups [i,j])) [dn j,dn i] [dn j,dn i]
      ((ddotL j).map (whL [] [dn i])))
  simpa [ups, wt, sh, neg_add_cancel_left] using H

end OddMath.SKM.RhoCoefficients
