import OddMath.SKM.Rho.Whisker
import OddMath.SKM.Rho.ShiftedWhisker
import OddMath.SKM.Rho.Powers

/-!
# Dotted for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoDotted
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoCoefficients RhoMixed
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

def capDot (t : k) (μ : X) (i : I) :=
  BicategoryStruct.whiskerRight (B := TwoSRev k (Uqπ D Sc sy hc))
    (rhoDot t (wt D μ [dn i]) i) (rhoF μ i)

def cupDot (t : k) (μ : X) (i : I) :=
  BicategoryStruct.whiskerLeft (B := TwoSRev k (Uqπ D Sc sy hc))
    (rhoF (wt D μ [up i]) i) (rhoDot t μ i)

theorem capDot_layers (t : k) (μ : X) (i : I) :
    HEq (QEnvelope.toHom (Envelope.toHom (capDot (Sc := Sc) (sy := sy) (hc := hc) t μ i)))
      (psiCoeff t (D.parity i) • cl D Sc μ [up i,dn i] [up i,dn i]
        ((ddotL i).map (whL [up i] []))) := by
  change HEq (QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerLeft (B := Uqπ D Sc sy hc)
      (rhoF μ i) (rhoDot t (wt D μ [dn i]) i)))) _
  rw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
  change HEq ((pres D Sc).wL (ob D (wt D μ [dn i]) [up i])
    (psiCoeff t (D.parity i) • cl D Sc (wt D (wt D μ [dn i]) [up i]) [dn i] [dn i] (ddotL i))) _
  have hw : wt D (wt D μ [dn i]) [up i] = μ := by simp [wt, sh]
  rw [hw]
  have H := upward_wL_plcL (Sc := Sc) (wt D μ [dn i]) μ [up i] [dn i] [dn i] rfl rfl
    (Submodule.smul_mem (homPar D Sc μ [dn i] [dn i] (parsum D (ddotL i)))
      (psiCoeff t (D.parity i)) (cl_mem_homPar (sChain_ddotL i) rfl))
  simp only [map_smul] at H
  erw [plcL_cl] at H
  exact H

private theorem wR_smul_cl_at (a : k) (ν μ ξ : X) (s t v : List (Letter I)) (A : List (LayerData I))
    (hs : wt D μ s = ν) (ht : wt D μ t = ν) (hμ : wt D ξ v = μ) (hA : SChain s A t) :
    HEq ((pres D Sc).wRAt ν (a • cl D Sc μ s t A) (ob D ξ v) hs ht)
      (a • cl D Sc ξ ([] ++ s ++ v) ([] ++ t ++ v) (A.map (whL [] v))) := by
  subst μ
  have H := upward_wR_plcL (Sc := Sc) ν ξ s t v hs ht
    (Submodule.smul_mem (homPar D Sc (wt D ξ v) s t (parsum D A)) a (cl_mem_homPar hA rfl))
  simp only [map_smul] at H
  erw [plcL_cl] at H
  exact H

theorem cupDot_layers (t : k) (μ : X) (i : I) :
    HEq (QEnvelope.toHom (Envelope.toHom (cupDot (Sc := Sc) (sy := sy) (hc := hc) t μ i)))
      (psiCoeff t (D.parity i) • cl D Sc μ [dn i,up i] [dn i,up i]
        ((ddotL i).map (whL [] [up i]))) := by
  change HEq (QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerRight (B := Uqπ D Sc sy hc)
      (rhoDot t μ i) (rhoF (wt D μ [up i]) i)))) _
  rw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
  have hw : wt D (wt D μ [up i]) [dn i] = μ := by simp [wt, sh]
  change HEq ((pres D Sc).wRAt μ
    (psiCoeff t (D.parity i) • cl D Sc (wt D μ [up i]) [dn i] [dn i] (ddotL i))
    (ob D (wt D (wt D μ [up i]) [dn i]) [up i]) (by simp [ob, wt, sh]) (by simp [ob, wt, sh])) _
  have H := wR_smul_cl_at (Sc := Sc) (psiCoeff t (D.parity i)) μ (wt D μ [up i])
    (wt D (wt D μ [up i]) [dn i]) [dn i] [dn i] [up i] (ddotL i)
    (by simp [wt, sh]) (by simp [wt, sh]) (by simp [wt, sh]) (sChain_ddotL i)
  apply H.trans
  rw [hw]
  rfl

private theorem cpow_heq {C : Type*} [Category C] {a b : C}
    (h : a = b) {f : a ⟶ a} {g : b ⟶ b} (hf : HEq f g) (n : ℕ) :
    HEq (cpow f n) (cpow g n) := by
  subst b
  cases hf
  rfl

theorem forget_cpow {a b : TwoSRev k (Uqπ D Sc sy hc)} {f : a ⟶ b} (x : f ⟶ f) (n : ℕ) :
    QEnvelope.toHom (Envelope.toHom (cpow x n)) =
      @cpow (pres D Sc).Presented _ ((pres D Sc).obj f.obj.obj.obj)
        (QEnvelope.toHom (Envelope.toHom x)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (QEnvelope.toHom (Envelope.toHom (cpow x n)) :
      (pres D Sc).obj f.obj.obj.obj ⟶ (pres D Sc).obj f.obj.obj.obj) ≫
        QEnvelope.toHom (Envelope.toHom x) =
      @cpow (pres D Sc).Presented _ ((pres D Sc).obj f.obj.obj.obj)
        (QEnvelope.toHom (Envelope.toHom x)) n ≫ QEnvelope.toHom (Envelope.toHom x)
    rw [ih]
    rfl

def capDots (t : k) (μ : X) (i : I) (n : ℕ) :=
  cpow (capDot (Sc := Sc) (sy := sy) (hc := hc) t μ i) n

def cupDots (t : k) (μ : X) (i : I) (n : ℕ) :=
  cpow (cupDot (Sc := Sc) (sy := sy) (hc := hc) t μ i) n

theorem capDots_layers (t : k) (μ : X) (i : I) (n : ℕ) :
    HEq (QEnvelope.toHom (Envelope.toHom (capDots (Sc := Sc) (sy := sy) (hc := hc) t μ i n)))
      (psiCoeff t (D.parity i) ^ n • cl D Sc μ [up i,dn i] [up i,dn i]
        ((ddotsL i n).map (whL [up i] []))) := by
  unfold capDots
  rw [forget_cpow]
  have ho : (pres D Sc).obj ((rhoE (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [dn i]) i ≫ rhoF μ i).obj.obj.obj) =
      (pres D Sc).obj (ob D μ [up i,dn i]) := by
    congr 1
    exact RhoParity.EF_word 0 μ i
  have H := cpow_heq ho (capDot_layers (Sc := Sc) (sy := sy) (hc := hc) t μ i) n
  exact H.trans (heq_of_eq (placed_dot_power (Sc := Sc) μ [up i] [] i (psiCoeff t (D.parity i)) n))

theorem cupDots_layers (t : k) (μ : X) (i : I) (n : ℕ) :
    HEq (QEnvelope.toHom (Envelope.toHom (cupDots (Sc := Sc) (sy := sy) (hc := hc) t μ i n)))
      (psiCoeff t (D.parity i) ^ n • cl D Sc μ [dn i,up i] [dn i,up i]
        ((ddotsL i n).map (whL [] [up i]))) := by
  unfold cupDots
  rw [forget_cpow]
  have ho : (pres D Sc).obj ((rhoF (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [up i]) i ≫ rhoE μ i).obj.obj.obj) =
      (pres D Sc).obj (ob D μ [dn i,up i]) := by
    congr 1
    exact RhoParity.FE_word 0 μ i
  have H := cpow_heq ho (cupDot_layers (Sc := Sc) (sy := sy) (hc := hc) t μ i) n
  exact H.trans (heq_of_eq (placed_dot_power (Sc := Sc) μ [] [up i] i (psiCoeff t (D.parity i)) n))

universe z
private theorem cast_of_heq {α β : Sort z} {a : α} {b : β} (h : HEq a b) :
    cast (type_eq_of_heq h) a = b := by cases h; rfl

def capDotsAt (t : k) (μ : X) (i : I) (n : ℕ) :
    RhoParity.UD (Sc := Sc) (sy := sy) (hc := hc) 0 μ i ⟶ RhoParity.UD 0 μ i :=
  cast (type_eq_of_heq (capDots_layers (Sc := Sc) (sy := sy) (hc := hc) t μ i n))
    (QEnvelope.toHom (Envelope.toHom (capDots t μ i n)))

def cupDotsAt (t : k) (μ : X) (i : I) (n : ℕ) :
    RhoParity.DU (Sc := Sc) (sy := sy) (hc := hc) 0 μ i ⟶ RhoParity.DU 0 μ i :=
  cast (type_eq_of_heq (cupDots_layers (Sc := Sc) (sy := sy) (hc := hc) t μ i n))
    (QEnvelope.toHom (Envelope.toHom (cupDots t μ i n)))

def dottedCap (t : k) (μ : X) (i : I) (n : ℕ) :=
  capDotsAt (Sc := Sc) (sy := sy) (hc := hc) t μ i n ≫ RhoParity.cap 0 μ i

def dottedCup (t : k) (μ : X) (i : I) (n : ℕ) :=
  RhoParity.cup (Sc := Sc) (sy := sy) (hc := hc) 0 μ i ≫ cupDotsAt t μ i n

theorem dottedCap_eq_raw (t : k) (μ : X) (i : I) (n : ℕ) :
    dottedCap (Sc := Sc) (sy := sy) (hc := hc) t μ i n = epsImage t μ i n := by
  unfold dottedCap capDotsAt RhoParity.cap
  rw [cast_of_heq (capDots_layers (Sc := Sc) (sy := sy) (hc := hc) t μ i n)]
  change (psiCoeff t (D.parity i) ^ n • cl D Sc μ [up i,dn i] [up i,dn i]
    ((ddotsL i n).map (whL [up i] []))) ≫ cl D Sc μ [up i,dn i] [] [([], Shape.cap i, [])] = _
  rw [Linear.smul_comp]
  erw [cl_comp (Sc := Sc) (μ := μ) ((sChain_ddotsL i n).wh [up i] [] rfl rfl)
      (show SChain [up i,dn i] [([], Shape.cap i, [])] [] from ⟨rfl,rfl⟩)]
  rfl

theorem dottedCup_eq_raw (t : k) (μ : X) (i : I) (n : ℕ) :
    dottedCup (Sc := Sc) (sy := sy) (hc := hc) t μ i n = etaImage t μ i n := by
  unfold dottedCup cupDotsAt RhoParity.cup
  rw [cast_of_heq (cupDots_layers (Sc := Sc) (sy := sy) (hc := hc) t μ i n)]
  change cl D Sc μ [] [dn i,up i] [([], Shape.cup i, [])] ≫
    (psiCoeff t (D.parity i) ^ n • cl D Sc μ [dn i,up i] [dn i,up i]
      ((ddotsL i n).map (whL [] [up i]))) = _
  rw [Linear.comp_smul]
  erw [cl_comp (Sc := Sc) (μ := μ) (show SChain [] [([], Shape.cup i, [])] [dn i,up i] from ⟨rfl,rfl⟩)
      ((sChain_ddotsL i n).wh [] [up i] rfl rfl)]
  rfl

theorem dottedCap_eq (t : k) (μ : X) (i : I) (n : ℕ) :
    dottedCap (Sc := Sc) (sy := sy) (hc := hc) t μ i n =
      entryCoeff t (D.parity i) n • cl D Sc μ [up i,dn i] [] (epsL i n) := by
  rw [dottedCap_eq_raw, epsImage_eq]

theorem dottedCup_eq (t : k) (μ : X) (i : I) (n : ℕ) :
    dottedCup (Sc := Sc) (sy := sy) (hc := hc) t μ i n =
      entryCoeff t (D.parity i) n • cl D Sc μ [] [dn i,up i] (etaL i n) := by
  rw [dottedCup_eq_raw, etaImage_eq]

end OddMath.SKM.RhoDotted
