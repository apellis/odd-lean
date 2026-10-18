import OddMath.SKM.Rho.Matrix

/-!
# Whisker for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoMixed
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

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
private theorem wR_cl_at (ν μ ξ : X) (s t v : List (Letter I)) (A : List (LayerData I))
    (hs : wt D μ s = ν) (ht : wt D μ t = ν) (hμ : wt D ξ v = μ) (hA : SChain s A t) :
    HEq ((pres D Sc).wRAt ν (cl D Sc μ s t A) (ob D ξ v) hs ht)
      (cl D Sc ξ ([] ++ s ++ v) ([] ++ t ++ v) (A.map (whL [] v))) := by
  subst μ
  have H := wR_plcL (Sc := Sc) ν ξ s t v hs ht (cl_mem_homPar hA rfl)
  erw [plcL_cl] at H
  exact H

theorem cup_whisker_layers (μ : X) (i j : I) :
    HEq (QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerRight (B := TwoSRev k (Uqπ D Sc sy hc))
        (RhoParity.cup 0 (wt D μ [up j, dn i]) i) (EF μ i j))))
      (cl D Sc (wt D μ [up j, dn i]) [up i, dn j] [up i, dn j, dn i, up i]
        [([up i, dn j], Shape.cup i, [])]) := by
  change HEq (QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerLeft (B := Uqπ D Sc sy hc)
      (EF μ i j) (RhoParity.cup 0 (wt D μ [up j, dn i]) i)))) _
  rw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
  change HEq ((pres D Sc).wL (EF (Sc := Sc) (sy := sy) (hc := hc) μ i j).obj.obj.obj
    (cl D Sc (wt D μ [up j, dn i]) [] [dn i, up i] [([], Shape.cup i, [])])) _
  rw [EF_word]
  have H := wL_plcL (Sc := Sc) (wt D μ [up j, dn i]) (wt D μ [up j, dn i])
    [up i, dn j] [] [dn i, up i] rfl (by simp [wt, sh])
    (cl_mem_homPar (show SChain [] [([], Shape.cup i, [])] [dn i, up i] from ⟨rfl,rfl⟩) rfl)
  erw [plcL_cl] at H
  exact H

theorem cap_whisker_layers (μ : X) (i j : I) :
    HEq (QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerLeft (B := TwoSRev k (Uqπ D Sc sy hc))
        (FE μ i j) (RhoParity.cap 0 μ i))))
      (cl D Sc (wt D μ [up j, dn i]) [up i, dn i, dn j, up i] [dn j, up i]
        [([], Shape.cap i, [dn j, up i])]) := by
  change HEq (QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerRight (B := Uqπ D Sc sy hc)
      (RhoParity.cap 0 μ i) (FE μ i j)))) _
  rw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
  change HEq ((pres D Sc).wRAt μ (cl D Sc μ [up i, dn i] [] [([], Shape.cap i, [])])
    (FE (Sc := Sc) (sy := sy) (hc := hc) μ i j).obj.obj.obj (by simp [ob, wt, sh]) rfl) _
  rw [FE_word]
  exact wR_cl_at (Sc := Sc) μ μ (wt D μ [up j, dn i]) [up i, dn i] [] [dn j, up i]
    [([], Shape.cap i, [])] (by simp [wt, sh]) rfl
    (by simp [wt, sh, add_comm, add_left_comm, add_assoc]) ⟨rfl,rfl⟩

private theorem wLwR_cl_at (a : k) (ν μ ξ : X) (u s t v : List (Letter I)) (A : List (LayerData I))
    (hs : wt D μ s = ν) (ht : wt D μ t = ν) (hμ : wt D ξ v = μ) (hA : SChain s A t) :
    HEq (a • (pres D Sc).wL (ob D ν u)
      ((pres D Sc).wRAt ν (cl D Sc μ s t A) (ob D ξ v) hs ht))
      (a • cl D Sc ξ (u ++ s ++ v) (u ++ t ++ v) (A.map (whL u v))) := by
  subst μ
  have ho (r : List (Letter I)) (hr : wt D (wt D ξ v) r = ν) :
      (ob D ν u).tensor ((ob D (wt D ξ v) r).tensor (ob D ξ v)) = ob D ξ (u ++ r ++ v) := by
    rw [ob_tensor_right]
    simpa only [List.nil_append, List.append_nil, List.append_assoc] using
      ob_tensor ν ξ u (r ++ v) (by simpa only [wt_append] using hr)
  apply raw_heq (congrArg (pres D Sc).obj (ho s hs)) (congrArg (pres D Sc).obj (ho t ht))
  rw [Linear.smul_comp, Linear.comp_smul]
  congr 1
  rw [cl_of hA]
  have hcomp : (ob D (wt D ξ v) s).Composable (ob D ξ v) :=
    Presentation.Bicat.Hom.composable
      (psiWordAt (Sc := Sc) ν (wt D ξ v) s hs) (psiWordAt (wt D ξ v) ξ v rfl)
  rw [Presentation.wRAt_diag _ _ _ hcomp]
  have hcomp' : (ob D ν u).Composable ((ob D (wt D ξ v) s).tensor (ob D ξ v)) :=
    Presentation.Bicat.Hom.composable
      (psiWordAt (Sc := Sc) (wt D ν u) ν u rfl)
      ((psiWordAt ν (wt D ξ v) s hs) ≫ psiWordAt (wt D ξ v) ξ v rfl)
  rw [Presentation.wL_diag_of_composable _ _ _ hcomp']
  rw [cl_of (hA.whisk u v)]
  refine Presentation.diag_eq_of_layers_eq' _ _ _ (ho s hs) (ho t ht) ?_
  simp only [Diagram.layers_lwhisker, Diagram.layers_rwhisker, layers_mkD]
  rw [← layList_whisker D ξ u v hA]
  simp only [List.map_map, ob, Layer.wl, Layer.wr, Layer.whisker, hs]
  rfl

private theorem middle_weight (μ : X) (i j : I) :
    wt D (wt D μ [dn i]) (ups [i,j]) = wt D μ [up j] := by
  simp [ups, wt, sh, add_comm, add_left_comm, add_assoc]

def crossLeg (t : k) (μ : X) (i j : I) :=
  BicategoryStruct.whiskerRight (B := TwoSRev k (Uqπ D Sc sy hc))
    (BicategoryStruct.whiskerLeft (B := TwoSRev k (Uqπ D Sc sy hc))
      (rhoF (wt D μ [up j]) i)
      (RhoCoefficients.correctedCrossing t (wt D μ [up j]) (wt D μ [dn i]) i j (middle_weight μ i j)))
    (rhoF μ i)

theorem cross_whisker_layers (t : k) (μ : X) (i j : I) :
    HEq (QEnvelope.toHom (Envelope.toHom (crossLeg (Sc := Sc) (sy := sy) (hc := hc) t μ i j)))
      (psiCoeff t (D.parity i * D.parity j) •
        cl D Sc (wt D μ [up j, dn i]) [up i, dn j, dn i, up i] [up i, dn i, dn j, up i]
          ((dcrossL j i).map (whL [up i] [up i]))) := by
  unfold crossLeg
  change HEq (QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerLeft (B := Uqπ D Sc sy hc) (rhoF μ i)
      (BicategoryStruct.whiskerRight (B := Uqπ D Sc sy hc)
        (RhoCoefficients.correctedCrossing t (wt D μ [up j]) (wt D μ [dn i]) i j (middle_weight μ i j))
        (rhoF (wt D μ [up j]) i))))) _
  rw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl,
    TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
  change HEq ((pres D Sc).wL (ob D (wt D μ [dn i]) [up i])
    ((pres D Sc).wRAt (wt (X := X) D μ [dn i])
      (zsign k (D.parity i * D.parity j) • (psiCoeff (-t) (D.parity i * D.parity j) •
        cl D Sc (wt D μ [up j]) [dn j,dn i] [dn i,dn j] (dcrossL j i)))
      (ob D (wt D (wt D μ [up j]) [dn i]) [up i])
      (by simp [ob, wt, sh, add_comm, add_left_comm, add_assoc])
      (by simp [ob, wt, sh, add_comm, add_assoc]))) _
  rw [smul_smul, RhoCoefficients.crossing_coefficient,
    Presentation.wRAt_smul, Presentation.wL_smul]
  have H := wLwR_cl_at (Sc := Sc) (psiCoeff t (D.parity i * D.parity j)) (wt D μ [dn i]) (wt D μ [up j])
    (wt D (wt D μ [up j]) [dn i]) [up i] [dn j,dn i] [dn i,dn j] [up i] (dcrossL j i)
    (by simp [wt, sh, add_comm, add_left_comm, add_assoc])
    (by simp [wt, sh, add_comm, add_assoc])
    (by simp [wt, sh]) (sChain_dcrossL j i)
  apply H.trans
  have hreg : wt D (wt D μ [up j]) [dn i] = wt D μ [up j, dn i] := by
    simp [wt, sh, add_comm, add_left_comm, add_assoc]
  rw [hreg]
  rfl

universe z
private theorem cast_of_heq {α β : Sort z} {a : α} {b : β} (h : HEq a b) :
    cast (type_eq_of_heq h) a = b := by
  cases h
  rfl

def normalizedCupLeg (μ : X) (i j : I) :
    (pres D Sc).obj (ob D (wt D μ [up j,dn i]) [up i,dn j]) ⟶
      (pres D Sc).obj (ob D (wt D μ [up j,dn i]) [up i,dn j,dn i,up i]) :=
  cast (type_eq_of_heq (cup_whisker_layers (Sc := Sc) (sy := sy) (hc := hc) μ i j))
    (QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerRight (B := TwoSRev k (Uqπ D Sc sy hc))
        (RhoParity.cup 0 (wt D μ [up j,dn i]) i) (EF μ i j))))

def normalizedCrossLeg (t : k) (μ : X) (i j : I) :
    (pres D Sc).obj (ob D (wt D μ [up j,dn i]) [up i,dn j,dn i,up i]) ⟶
      (pres D Sc).obj (ob D (wt D μ [up j,dn i]) [up i,dn i,dn j,up i]) :=
  cast (type_eq_of_heq (cross_whisker_layers (Sc := Sc) (sy := sy) (hc := hc) t μ i j))
    (QEnvelope.toHom (Envelope.toHom (crossLeg t μ i j)))

def normalizedCapLeg (μ : X) (i j : I) :
    (pres D Sc).obj (ob D (wt D μ [up j,dn i]) [up i,dn i,dn j,up i]) ⟶
      (pres D Sc).obj (ob D (wt D μ [up j,dn i]) [dn j,up i]) :=
  cast (type_eq_of_heq (cap_whisker_layers (Sc := Sc) (sy := sy) (hc := hc) μ i j))
    (QEnvelope.toHom (Envelope.toHom
      (BicategoryStruct.whiskerLeft (B := TwoSRev k (Uqπ D Sc sy hc))
        (FE μ i j) (RhoParity.cap 0 μ i))))

def sigmaImage (t : k) (μ : X) (i j : I) :=
  normalizedCupLeg (Sc := Sc) (sy := sy) (hc := hc) μ i j ≫
    normalizedCrossLeg (sy := sy) (hc := hc) t μ i j ≫ normalizedCapLeg (sy := sy) (hc := hc) μ i j

theorem sigmaImage_eq_mixed (t : k) (μ : X) (i j : I) :
    sigmaImage (Sc := Sc) (sy := sy) (hc := hc) t μ i j =
      mixed t (wt D μ [up j,dn i]) i j := by
  unfold sigmaImage normalizedCupLeg normalizedCrossLeg normalizedCapLeg
  rw [cast_of_heq (cup_whisker_layers (Sc := Sc) (sy := sy) (hc := hc) μ i j),
    cast_of_heq (cross_whisker_layers (Sc := Sc) (sy := sy) (hc := hc) t μ i j),
    cast_of_heq (cap_whisker_layers (Sc := Sc) (sy := sy) (hc := hc) μ i j)]
  rw [Linear.smul_comp (R := k), Linear.comp_smul (R := k)]
  unfold mixed
  congr 1
  erw [cl_comp ((sChain_dcrossL j i).whisk [up i] [up i])
      (show SChain [up i,dn i,dn j,up i] [([], Shape.cap i, [dn j,up i])] [dn j,up i] from ⟨rfl,rfl⟩)]
  erw [cl_comp (show SChain [up i,dn j] [([up i,dn j], Shape.cup i, [])]
      [up i,dn j,dn i,up i] from ⟨rfl,rfl⟩)
    (((sChain_dcrossL j i).whisk [up i] [up i]).append
      (show SChain [up i,dn i,dn j,up i] [([], Shape.cap i, [dn j,up i])] [dn j,up i] from ⟨rfl,rfl⟩))]
  simp only [mixedLayers, List.append_assoc]

theorem sigmaImage_eq (t : k) (μ : X) (i j : I) :
    sigmaImage (Sc := Sc) (sy := sy) (hc := hc) t μ i j =
      psiCoeff t (D.parity i * D.parity j) •
        cl D Sc (wt D μ [up j,dn i]) [up i,dn j] [dn j,up i] (sigmaL j i) := by
  rw [sigmaImage_eq_mixed, mixed_eq]

theorem sigmaImage_invNe₁ (t : k) (ht : t ^ 2 = -1) (μ : X) (i j : I) (hij : i ≠ j) :
    sigmaImage (Sc := Sc) (sy := sy) (hc := hc) t μ i j ≫
      mixedInverse t (wt D μ [up j,dn i]) i j = 𝟙 _ := by
  rw [sigmaImage_eq_mixed, mixed_invNe₁ t ht _ i j hij]

theorem sigmaImage_invNe₂ (t : k) (ht : t ^ 2 = -1) (μ : X) (i j : I) (hij : i ≠ j) :
    mixedInverse (Sc := Sc) t (wt D μ [up j,dn i]) i j ≫
      sigmaImage (sy := sy) (hc := hc) t μ i j = 𝟙 _ := by
  rw [sigmaImage_eq_mixed, mixed_invNe₂ t ht _ i j hij]

end OddMath.SKM.RhoMixed
