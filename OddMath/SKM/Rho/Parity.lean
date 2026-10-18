import OddMath.SKM.RhoGenerators

/-!
# Parity for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoParity
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

def F (p : ZMod 2) (μ : X) (i : I) :
    rhoObj (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [dn i]) ⟶ rhoObj μ :=
  Envelope.mk p (rhoF (Sc := Sc) (sy := sy) (hc := hc) μ i).obj

example (μ : X) (i : I) : F (Sc := Sc) (sy := sy) (hc := hc) 0 μ i = rhoF μ i := rfl

private theorem wt_du (μ : X) (i : I) : wt D μ [dn i, up i] = μ := by
  simp [wt_cons, sh, dn, up]
private theorem wt_ud (μ : X) (i : I) : wt D μ [up i, dn i] = μ := by
  simp [wt_cons, sh, dn, up]

def DU (p : ZMod 2) (μ : X) (i : I) :
    rhoObj (Sc := Sc) (sy := sy) (hc := hc) μ ⟶ rhoObj μ :=
  Envelope.mk p (QEnvelope.mk 0 (psiWordAt μ μ [dn i, up i] (wt_du μ i)))
def UD (p : ZMod 2) (μ : X) (i : I) :
    rhoObj (Sc := Sc) (sy := sy) (hc := hc) μ ⟶ rhoObj μ :=
  Envelope.mk p (QEnvelope.mk 0 (psiWordAt μ μ [up i, dn i] (wt_ud μ i)))

theorem FE_par (p : ZMod 2) (μ : X) (i : I) :
    (F (Sc := Sc) (sy := sy) (hc := hc) p (wt D μ [up i]) i ≫ rhoE μ i).par = p := by
  change 0 + p = p
  simp

theorem EF_par (p : ZMod 2) (μ : X) (i : I) :
    (rhoE (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [dn i]) i ≫ F p μ i).par = p := by
  change p + 0 = p
  simp

theorem FE_shift (p : ZMod 2) (μ : X) (i : I) :
    (F (Sc := Sc) (sy := sy) (hc := hc) p (wt D μ [up i]) i ≫ rhoE μ i).obj.shift = 0 := by
  change rhoUpShift sy μ [i] + sy.d i * (D.h i (wt D μ [up i]) - 1) = 0
  rw [rhoUpShift_single, h_wt_up]
  ring

theorem EF_shift (p : ZMod 2) (μ : X) (i : I) :
    (rhoE (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [dn i]) i ≫ F p μ i).obj.shift = 0 := by
  change sy.d i * (D.h i μ - 1) + rhoUpShift sy (wt D μ [dn i]) [i] = 0
  rw [rhoUpShift_single, h_wt_dn]
  ring

theorem FE_word (p : ZMod 2) (μ : X) (i : I) :
    (F (Sc := Sc) (sy := sy) (hc := hc) p (wt D μ [up i]) i ≫ rhoE μ i).obj.obj.obj =
      ob D μ [dn i, up i] := by
  change (ob D (wt D μ [up i]) [dn i]).tensor
    (ob D (wt D (wt D μ [up i]) [dn i]) [up i]) = _
  simp [ob, wd, wt, sh, StringDiagrams.Obj.tensor]

theorem EF_word (p : ZMod 2) (μ : X) (i : I) :
    (rhoE (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [dn i]) i ≫ F p μ i).obj.obj.obj =
      ob D μ [up i, dn i] := by
  change (ob D (wt D μ [dn i]) [up i]).tensor
    (ob D (wt D (wt D μ [dn i]) [up i]) [dn i]) = _
  simp [ob, wd, wt, sh, StringDiagrams.Obj.tensor]

def cup (p : ZMod 2) (μ : X) (i : I) :
    𝟙 (rhoObj (Sc := Sc) (sy := sy) (hc := hc) μ) ⟶ DU p μ i :=
  cl D Sc μ [] [dn i, up i] [([], Shape.cup i, [])]

def cap (p : ZMod 2) (μ : X) (i : I) :
    UD (Sc := Sc) (sy := sy) (hc := hc) p μ i ⟶ 𝟙 (rhoObj μ) :=
  cl D Sc μ [up i, dn i] [] [([], Shape.cap i, [])]

theorem cup_parity (p : ZMod 2) (μ : X) (i : I) :
    cup (Sc := Sc) (sy := sy) (hc := hc) p μ i ∈ parity (R := k) _ _ p := by
  change cl D Sc μ [] [dn i, up i] [([], Shape.cup i, [])] ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (p + (0 + p))
  rw [zero_add, zmod2_add_self]
  rw [cl_of (by simp [SChain, Shape.dom, Shape.cod])]
  apply Presentation.diag_mem_homDeg'
  rw [degree_parity_mkD]
  rfl

theorem cap_parity (p : ZMod 2) (μ : X) (i : I) :
    cap (Sc := Sc) (sy := sy) (hc := hc) p μ i ∈ parity (R := k) _ _ p := by
  change cl D Sc μ [up i, dn i] [] [([], Shape.cap i, [])] ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (p + (p + 0))
  rw [add_zero, zmod2_add_self]
  rw [cl_of (by simp [SChain, Shape.dom, Shape.cod])]
  apply Presentation.diag_mem_homDeg'
  rw [degree_parity_mkD]
  rfl

theorem cup_degree (p : ZMod 2) (μ : X) (i : I) :
    cup (Sc := Sc) (sy := sy) (hc := hc) p μ i ∈
      GradedSupercategory.degree (R := k) _ _ (sy.d i * (1 + D.h i μ)) := by
  change cl D Sc μ [] [dn i, up i] [([], Shape.cup i, [])] ∈
    (pres D Sc).homDeg (gdeg D sy) _ _ (_ + (0 - 0))
  simp only [sub_self, add_zero]
  simpa [gsum, gdeg] using
    cl_mem_gdeg (Sc := Sc) sy μ [] [dn i, up i] [([], Shape.cup i, [])]

theorem cap_degree (p : ZMod 2) (μ : X) (i : I) :
    cap (Sc := Sc) (sy := sy) (hc := hc) p μ i ∈
      GradedSupercategory.degree (R := k) _ _ (sy.d i * (1 - D.h i μ)) := by
  change cl D Sc μ [up i, dn i] [] [([], Shape.cap i, [])] ∈
    (pres D Sc).homDeg (gdeg D sy) _ _ (_ + (0 - 0))
  simp only [sub_self, add_zero]
  simpa [gsum, gdeg] using
    cl_mem_gdeg (Sc := Sc) sy μ [up i, dn i] [] [([], Shape.cap i, [])]

theorem E_cup_whisker (p : ZMod 2) (μ : X) (i : I) :
    QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerLeft (B := TwoSRev k (Uqπ D Sc sy hc))
        (rhoE μ i) (cup p μ i))) =
    BicategoryStruct.whiskerRight (B := UGr D Sc sy hc)
      (QEnvelope.toHom (Envelope.toHom (cup p μ i)))
      (rhoE (Sc := Sc) (sy := sy) (hc := hc) μ i).obj.obj := by
  change QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerRight (B := Uqπ D Sc sy hc) (cup p μ i) (rhoE μ i))) = _
  rw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
  rfl

theorem E_cap_whisker (p : ZMod 2) (μ : X) (i : I) :
    QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerRight (B := TwoSRev k (Uqπ D Sc sy hc))
        (cap p (wt D μ [up i]) i) (rhoE μ i))) =
    BicategoryStruct.whiskerLeft (B := UGr D Sc sy hc)
      (rhoE (Sc := Sc) (sy := sy) (hc := hc) μ i).obj.obj
      (QEnvelope.toHom (Envelope.toHom (cap p (wt D μ [up i]) i))) := by
  change QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerLeft (B := Uqπ D Sc sy hc)
      (rhoE μ i) (cap p (wt D μ [up i]) i))) = _
  rw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
  rfl

private theorem cup_underlying_even (p : ZMod 2) (μ : X) (i : I) :
    Envelope.toHom (cup (Sc := Sc) (sy := sy) (hc := hc) p μ i) ∈
      parity (R := k) _ _ 0 := by
  have h := cup_parity (Sc := Sc) (sy := sy) (hc := hc) p μ i
  change _ ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (p + (0 + p)) at h
  change cup (Sc := Sc) (sy := sy) (hc := hc) p μ i ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ 0
  simpa only [zero_add, zmod2_add_self] using h

private theorem cap_underlying_even (p : ZMod 2) (μ : X) (i : I) :
    Envelope.toHom (cap (Sc := Sc) (sy := sy) (hc := hc) p μ i) ∈
      parity (R := k) _ _ 0 := by
  have h := cap_parity (Sc := Sc) (sy := sy) (hc := hc) p μ i
  change _ ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (p + (p + 0)) at h
  change cap (Sc := Sc) (sy := sy) (hc := hc) p μ i ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ 0
  simpa only [add_zero, zmod2_add_self] using h

theorem F_cup_whisker (p : ZMod 2) (μ : X) (i : I) :
    QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerRight (B := TwoSRev k (Uqπ D Sc sy hc))
        (cup p (wt D μ [dn i]) i) (F p μ i))) =
    BicategoryStruct.whiskerLeft (B := UGr D Sc sy hc)
      (F (Sc := Sc) (sy := sy) (hc := hc) p μ i).obj.obj
      (QEnvelope.toHom (Envelope.toHom (cup p (wt D μ [dn i]) i))) := by
  change QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerLeft (B := Uqπ D Sc sy hc)
      (F p μ i) (cup p (wt D μ [dn i]) i))) = _
  rw [TwoEnvelope.toHom_whiskerLeft_of_even _ (cup_underlying_even p _ i)]
  rfl

theorem F_cap_whisker (p : ZMod 2) (μ : X) (i : I) :
    QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerLeft (B := TwoSRev k (Uqπ D Sc sy hc))
        (F p μ i) (cap p μ i))) =
    sign k (p * p) • BicategoryStruct.whiskerRight (B := UGr D Sc sy hc)
      (QEnvelope.toHom (Envelope.toHom (cap p μ i)))
      (F (Sc := Sc) (sy := sy) (hc := hc) p μ i).obj.obj := by
  change QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerRight (B := Uqπ D Sc sy hc) (cap p μ i) (F p μ i))) = _
  rw [TwoEnvelope.toHom_whiskerRight_of_mem (cap_underlying_even p μ i)]
  change (sign k (p * (0 + (p + 0))) • _) = _
  simp only [add_zero, zero_add]
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

theorem proof_FE_par (μ : X) (i : I) :
    (F (Sc := Sc) (sy := sy) (hc := hc) (ipar D i (wt D μ [up i]))
      (wt D μ [up i]) i ≫ rhoE μ i).par = ipar D i μ := by
  rw [FE_par, ipar_wt_up]

theorem proof_EF_par (μ : X) (i : I) :
    (rhoE (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [dn i]) i ≫ F (ipar D i μ) μ i).par =
      ipar D i μ := EF_par _ _ _

theorem odd_zero_boundary_mismatch (i : I) (hi : D.parity i = 1) :
    (rhoE (Sc := Sc) (sy := sy) (hc := hc) (wt D (0 : X) [dn i]) i ≫
      F (ipar D i 0) 0 i).par ≠ 0 := by
  rw [proof_EF_par]
  simp [ipar, hi, Datum.h]

private theorem rightCup_mem (μ : X) (i : I) :
    cl D Sc μ [] [dn i, up i] [([], Shape.cup i, [])] ∈ homPar D Sc μ [] [dn i, up i] 0 :=
  cl_mem_homPar (by simp [SChain, Shape.dom, Shape.cod]) rfl

private theorem rightCap_mem (μ : X) (i : I) :
    cl D Sc μ [up i, dn i] [] [([], Shape.cap i, [])] ∈ homPar D Sc μ [up i, dn i] [] 0 :=
  cl_mem_homPar (by simp [SChain, Shape.dom, Shape.cod]) rfl

theorem E_cap_layers (p : ZMod 2) (μ : X) (i : I) :
    HEq (QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerRight (B := TwoSRev k (Uqπ D Sc sy hc))
        (cap p (wt D μ [up i]) i) (rhoE μ i))))
      (cl D Sc (wt D μ [up i]) [dn i, up i, dn i] [dn i]
        [([dn i], Shape.cap i, [])]) := by
  rw [E_cap_whisker]
  change HEq ((pres D Sc).wL (ob D (wt D μ [up i]) [dn i])
    (cl D Sc (wt D μ [up i]) [up i, dn i] [] [([], Shape.cap i, [])])) _
  have H := wL_plcL (Sc := Sc) (wt D μ [up i]) (wt D μ [up i])
    [dn i] [up i, dn i] [] (wt_ud _ i) rfl (rightCap_mem _ i)
  erw [plcL_cl] at H
  exact H

theorem F_cup_layers (p : ZMod 2) (μ : X) (i : I) :
    HEq (QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerRight (B := TwoSRev k (Uqπ D Sc sy hc))
        (cup p (wt D μ [dn i]) i) (F p μ i))))
      (cl D Sc (wt D μ [dn i]) [up i] [up i, dn i, up i]
        [([up i], Shape.cup i, [])]) := by
  rw [F_cup_whisker]
  change HEq ((pres D Sc).wL (ob D (wt D μ [dn i]) [up i])
    (cl D Sc (wt D μ [dn i]) [] [dn i, up i] [([], Shape.cup i, [])])) _
  have H := wL_plcL (Sc := Sc) (wt D μ [dn i]) (wt D μ [dn i])
    [up i] [] [dn i, up i] rfl (wt_du _ i) (rightCup_mem _ i)
  erw [plcL_cl] at H
  exact H

private theorem wR_cl_at (ν μ ξ : X) (s t v : List (Letter I)) (A : List (LayerData I))
    (hs : wt D μ s = ν) (ht : wt D μ t = ν) (hμ : wt D ξ v = μ) (hA : SChain s A t) :
    HEq ((pres D Sc).wRAt ν (cl D Sc μ s t A) (ob D ξ v) hs ht)
      (cl D Sc ξ ([] ++ s ++ v) ([] ++ t ++ v) (A.map (whL [] v))) := by
  subst μ
  have H := wR_plcL (Sc := Sc) ν ξ s t v hs ht (cl_mem_homPar hA rfl)
  erw [plcL_cl] at H
  exact H

theorem E_cup_layers (p : ZMod 2) (μ : X) (i : I) :
    HEq (QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerLeft (B := TwoSRev k (Uqπ D Sc sy hc))
        (rhoE μ i) (cup p μ i))))
      (cl D Sc (wt D μ [up i]) [dn i] [dn i, up i, dn i]
        [([], Shape.cup i, [dn i])]) := by
  rw [E_cup_whisker]
  exact wR_cl_at (Sc := Sc) μ μ (wt D μ [up i]) [] [dn i, up i] [dn i]
    [([], Shape.cup i, [])] rfl (wt_du μ i)
    (by simp [wt, sh]) (by simp [SChain, Shape.dom, Shape.cod])

theorem F_cap_base_layers (p : ZMod 2) (μ : X) (i : I) :
    HEq (BicategoryStruct.whiskerRight (B := UGr D Sc sy hc)
      (QEnvelope.toHom (Envelope.toHom (cap p μ i)))
      (F (Sc := Sc) (sy := sy) (hc := hc) p μ i).obj.obj)
      (cl D Sc (wt D μ [dn i]) [up i, dn i, up i] [up i]
        [([], Shape.cap i, [up i])]) := by
  exact wR_cl_at (Sc := Sc) μ μ (wt D μ [dn i]) [up i, dn i] [] [up i]
    [([], Shape.cap i, [])] (wt_ud μ i) rfl
    (by simp [wt, sh]) (by simp [SChain, Shape.dom, Shape.cod])

theorem E_snake_normalized (μ : X) (i : I) :
    cl D Sc μ [dn i] [dn i, up i, dn i] [([], Shape.cup i, [dn i])] ≫
      cl D Sc μ [dn i, up i, dn i] [dn i] [([dn i], Shape.cap i, [])] =
      𝟙 ((pres D Sc).obj (ob D μ [dn i])) := by
  rw [cl_comp (by simp [SChain, Shape.dom, Shape.cod]) (by simp [SChain, Shape.dom, Shape.cod])]
  erw [cl_zigF]
  exact cl_nil (Sc := Sc) _ _

theorem F_snake_normalized (p : ZMod 2) (μ : X) (i : I) :
    cl D Sc μ [up i] [up i, dn i, up i] [([up i], Shape.cup i, [])] ≫
      (sign k (p * p) • cl D Sc μ [up i, dn i, up i] [up i] [([], Shape.cap i, [up i])]) =
      sign k (p * p) • 𝟙 ((pres D Sc).obj (ob D μ [up i])) := by
  rw [Linear.comp_smul, cl_comp (by simp [SChain, Shape.dom, Shape.cod])
    (by simp [SChain, Shape.dom, Shape.cod])]
  erw [cl_zigE, cl_nil]

end OddMath.SKM.RhoParity
