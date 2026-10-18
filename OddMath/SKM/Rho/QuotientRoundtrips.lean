import OddMath.SKM.Rho.GeneratorRoundtrips
import OddMath.SKM.Rho.InverseComparisons

/-!
# Quotient Roundtrips for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoQuotientRoundtrips
open CategoryTheory StringDiagrams Supercategory BicategoryStruct QPiSupercategory
  RhoWords RhoTwo RhoExtension RhoInverse
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}
variable (t : k) (ht : t ^ 2 = -1)
section Whiskering
variable {B C : Type*} [BicategoryStruct B] [BicategoryStruct C]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
    [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear k (a ⟶ b)]
    [∀ a b : B, Supercategory k (a ⟶ b)] [∀ a b : C, Supercategory k (a ⟶ b)]

private theorem strict_left (F : TwoSuperfunctor k B C) (hF : F.IsStrict)
    {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (x : g ⟶ h) :
    HEq (F.map₂ (f ◁ x)) (F.map f ◁ F.map₂ x) := by
  apply (conj_eqToHom_iff_heq _ _ (hF.map_comp f g) (hF.map_comp f h)).1
  have H := congrArg (eqToHom (hF.map_comp f g) ≫ ·) (F.mapComp_naturality_right f x)
  rw [hF.mapComp_eq, hF.mapComp_eq] at H
  simpa only [eqToIso.hom, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Category.assoc] using H.symm

private theorem strict_right (F : TwoSuperfunctor k B C) (hF : F.IsStrict)
    {a b c : B} {f g : a ⟶ b} (x : f ⟶ g) (h : b ⟶ c) :
    HEq (F.map₂ (x ▷ h)) (F.map₂ x ▷ F.map h) := by
  apply (conj_eqToHom_iff_heq _ _ (hF.map_comp f h) (hF.map_comp g h)).1
  have H := congrArg (eqToHom (hF.map_comp f h) ≫ ·) (F.mapComp_naturality_left x h)
  rw [hF.mapComp_eq, hF.mapComp_eq] at H
  simpa only [eqToIso.hom, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Category.assoc] using H.symm
end Whiskering

theorem rhoForwardInverse_whiskerLeft {a b c : Uqπ D Sc sy hc}
    (f : a ⟶ b) {g h : b ⟶ c} (x : g ⟶ h) :
    HEq (((rhoEnvelope t ht).comp (rhoInverse t ht)).map₂ (f ◁ x))
      (((rhoEnvelope t ht).comp (rhoInverse t ht)).map f ◁
        ((rhoEnvelope t ht).comp (rhoInverse t ht)).map₂ x) :=
  strict_left _ (rhoForwardInverse_isStrict t ht) f x

theorem rhoForwardInverse_whiskerRight {a b c : Uqπ D Sc sy hc}
    {f g : a ⟶ b} (x : f ⟶ g) (h : b ⟶ c) :
    HEq (((rhoEnvelope t ht).comp (rhoInverse t ht)).map₂ (x ▷ h))
      (((rhoEnvelope t ht).comp (rhoInverse t ht)).map₂ x ▷
        ((rhoEnvelope t ht).comp (rhoInverse t ht)).map h) :=
  strict_right _ (rhoForwardInverse_isStrict t ht) x h

def rhoForwardInverseHom {a b : Uqπ D Sc sy hc} (f g : a ⟶ b) : (f ⟶ g) →ₗ[k] (f ⟶ g) where
  toFun x := eqToHom (rhoInverse_rho_map t ht f).symm ≫
    (rhoInverse t ht).map₂ ((rhoEnvelope t ht).map₂ x) ≫
    eqToHom (rhoInverse_rho_map t ht g)
  map_add' x y := by simp only [TwoSuperfunctor.map₂_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r x := by simp only [TwoSuperfunctor.map₂_smul, Linear.smul_comp, Linear.comp_smul]; rfl

private theorem normalized_heq {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (x : f ⟶ g) :
    HEq (rhoForwardInverseHom t ht f g x)
      ((rhoInverse t ht).map₂ ((rhoEnvelope t ht).map₂ x)) :=
  (conj_eqToHom_iff_heq _ _ (rhoInverse_rho_map t ht f).symm
    (rhoInverse_rho_map t ht g).symm).1 rfl

private theorem whisker_left_heq {a b c : Uqπ D Sc sy hc}
    {f f' : a ⟶ b} {g g' h h' : b ⟶ c} (hf : f = f') (hg : g = g') (hh : h = h')
    {x : g ⟶ h} {y : g' ⟶ h'} (hxy : HEq x y) : HEq (f ◁ x) (f' ◁ y) := by
  cases hf; cases hg; cases hh; cases hxy; rfl

private theorem whisker_right_heq {a b c : Uqπ D Sc sy hc}
    {f f' g g' : a ⟶ b} {h h' : b ⟶ c} (hf : f = f') (hg : g = g') (hh : h = h')
    {x : f ⟶ g} {y : f' ⟶ g'} (hxy : HEq x y) : HEq (x ▷ h) (y ▷ h') := by
  cases hf; cases hg; cases hh; cases hxy; rfl

theorem rhoForwardInverseHom_whiskerLeft {a b c : Uqπ D Sc sy hc}
    (f : a ⟶ b) {g h : b ⟶ c} (x : g ⟶ h) :
    rhoForwardInverseHom t ht (f ≫ g) (f ≫ h) (f ◁ x) =
      f ◁ rhoForwardInverseHom t ht g h x := by
  apply eq_of_heq
  exact (normalized_heq t ht (f ◁ x)).trans
    ((rhoForwardInverse_whiskerLeft t ht f x).trans
      (whisker_left_heq (rhoInverse_rho_map t ht f)
        (rhoInverse_rho_map t ht g) (rhoInverse_rho_map t ht h)
        (normalized_heq t ht x).symm))

theorem rhoForwardInverseHom_whiskerRight {a b c : Uqπ D Sc sy hc}
    {f g : a ⟶ b} (x : f ⟶ g) (h : b ⟶ c) :
    rhoForwardInverseHom t ht (f ≫ h) (g ≫ h) (x ▷ h) =
      rhoForwardInverseHom t ht f g x ▷ h := by
  apply eq_of_heq
  exact (normalized_heq t ht (x ▷ h)).trans
    ((rhoForwardInverse_whiskerRight t ht x h).trans
      (whisker_right_heq (rhoInverse_rho_map t ht f)
        (rhoInverse_rho_map t ht g) (rhoInverse_rho_map t ht h)
        (normalized_heq t ht x).symm))

theorem rhoForwardInverseHom_id {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    rhoForwardInverseHom t ht f f (𝟙 f) = 𝟙 f := by
  simp only [rhoForwardInverseHom, LinearMap.coe_mk, AddHom.coe_mk, TwoSuperfunctor.map₂_id,
    Category.id_comp, eqToHom_trans, eqToHom_refl]

theorem rhoForwardInverseHom_comp {a b : Uqπ D Sc sy hc} {f g h : a ⟶ b}
    (x : f ⟶ g) (y : g ⟶ h) :
    rhoForwardInverseHom t ht f h (x ≫ y) =
      rhoForwardInverseHom t ht f g x ≫ rhoForwardInverseHom t ht g h y := by
  simp only [rhoForwardInverseHom, LinearMap.coe_mk, AddHom.coe_mk, TwoSuperfunctor.map₂_comp,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

theorem rhoForwardInverseHom_eqToHom {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (e : f = g) :
    rhoForwardInverseHom t ht f g (eqToHom e) = eqToHom e := by
  cases e
  exact rhoForwardInverseHom_id t ht f

def rhoForwardInverseWordHom {a b : UGr D Sc sy hc} (f g : a ⟶ b) : (f ⟶ g) →ₗ[k] (f ⟶ g) :=
  rhoForwardInverseHom t ht (QPiTwoEnvelope.Jm (R := k) f) (QPiTwoEnvelope.Jm g)

private theorem j_left {a b c : UGr D Sc sy hc} (f : a ⟶ b) {g h : b ⟶ c} (x : g ⟶ h) :
    (QPiTwoEnvelope.Jm (R := k) f) ◁
      (show QPiTwoEnvelope.Jm (R := k) g ⟶ QPiTwoEnvelope.Jm h from x) =
    (show QPiTwoEnvelope.Jm (R := k) (f ≫ g) ⟶ QPiTwoEnvelope.Jm (f ≫ h) from f ◁ x) := by
  change f ◁ twist k (0 : ZMod 2) x = f ◁ x
  rw [twist_zero]

private theorem j_right {a b c : UGr D Sc sy hc} {f g : a ⟶ b} (x : f ⟶ g) (h : b ⟶ c) :
    (show QPiTwoEnvelope.Jm (R := k) f ⟶ QPiTwoEnvelope.Jm g from x) ▷
      QPiTwoEnvelope.Jm (R := k) h =
    (show QPiTwoEnvelope.Jm (R := k) (f ≫ h) ⟶ QPiTwoEnvelope.Jm (g ≫ h) from x ▷ h) := by
  change QEnvelope.toHom (Envelope.toHom (twist k (0 : ZMod 2)
    (show QPiTwoEnvelope.Jm (R := k) f ⟶ QPiTwoEnvelope.Jm g from x))) ▷ h = _
  rw [twist_zero]
  rfl

theorem rhoForwardInverseWordHom_whiskerLeft {a b c : UGr D Sc sy hc}
    (f : a ⟶ b) {g h : b ⟶ c} (x : g ⟶ h) :
    rhoForwardInverseWordHom t ht (f ≫ g) (f ≫ h) (f ◁ x) =
      f ◁ rhoForwardInverseWordHom t ht g h x := by
  have H := rhoForwardInverseHom_whiskerLeft t ht (QPiTwoEnvelope.Jm (R := k) f)
    (show QPiTwoEnvelope.Jm (R := k) g ⟶ QPiTwoEnvelope.Jm h from x)
  rw [j_left, j_left] at H
  exact H

theorem rhoForwardInverseWordHom_whiskerRight {a b c : UGr D Sc sy hc}
    {f g : a ⟶ b} (x : f ⟶ g) (h : b ⟶ c) :
    rhoForwardInverseWordHom t ht (f ≫ h) (g ≫ h) (x ▷ h) =
      rhoForwardInverseWordHom t ht f g x ▷ h := by
  have H := rhoForwardInverseHom_whiskerRight t ht
    (show QPiTwoEnvelope.Jm (R := k) f ⟶ QPiTwoEnvelope.Jm g from x) (QPiTwoEnvelope.Jm (R := k) h)
  rw [j_right, j_right] at H
  exact H

theorem rhoForwardInverseWordHom_id {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    rhoForwardInverseWordHom t ht f f (𝟙 f) = 𝟙 f :=
  rhoForwardInverseHom_id t ht _

theorem rhoForwardInverseWordHom_comp {a b : UGr D Sc sy hc} {f g h : a ⟶ b}
    (x : f ⟶ g) (y : g ⟶ h) :
    rhoForwardInverseWordHom t ht f h (x ≫ y) =
      rhoForwardInverseWordHom t ht f g x ≫ rhoForwardInverseWordHom t ht g h y :=
  rhoForwardInverseHom_comp t ht
    (f := QPiTwoEnvelope.Jm (R := k) f) (g := QPiTwoEnvelope.Jm (R := k) g)
    (h := QPiTwoEnvelope.Jm (R := k) h) x y

theorem rhoForwardInverseWordHom_eqToHom {a b : UGr D Sc sy hc} {f g : a ⟶ b} (e : f = g) :
    rhoForwardInverseWordHom t ht f g (eqToHom e) = eqToHom e := by
  cases e
  exact rhoForwardInverseWordHom_id t ht _

private theorem wordHom_heq {a b : UGr D Sc sy hc} {f g f' g' : a ⟶ b}
    (hf : f = f') (hg : g = g') {x : f ⟶ g} {y : f' ⟶ g'} (h : HEq x y) :
    HEq (rhoForwardInverseWordHom t ht f g x) (rhoForwardInverseWordHom t ht f' g' y) := by
  cases hf; cases hg; cases h; rfl

private theorem normalized_generator (ν μ : X) (g : Shape I) (hs : wt D μ g.dom = ν) :
    rhoForwardInverseWordHom (sy := sy) (hc := hc) t ht (psiWordAt ν μ g.dom hs)
      (psiWordAt ν μ g.cod ((g.wt_dom_eq_wt_cod D μ).symm.trans hs))
      (cl D Sc μ g.dom g.cod [([], g, [])]) = cl D Sc μ g.dom g.cod [([], g, [])] := by
  exact eq_of_heq ((normalized_heq t ht _).trans (RhoGeneratorRoundtrips.shape_roundtrip t ht ν μ g hs _ 0 0))

private theorem ob_tensor (ν μ : X) (u s : List (Letter I)) (h : wt D μ s = ν) :
    (ob D ν u).tensor (ob D μ s) = ob D μ (u ++ s ++ []) := by
  apply Obj.ext
  · change wt D ν u = wt D μ (u ++ s ++ [])
    simp only [List.append_nil, wt_append, h]
  · change wd D ν u ++ wd D μ s = wd D μ (u ++ s ++ [])
    simp only [List.append_nil, wd_append, h]

private theorem source_left_cl (ν μ : X) (u s r : List (Letter I))
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (L : List (LayerData I)) (hL : SChain s L r) :
    HEq (BicategoryStruct.whiskerLeft (B := UGr D Sc sy hc)
      (psiWordAt (Sc := Sc) (wt D ν u) ν u rfl)
      (show psiWordAt (Sc := Sc) ν μ s hs ⟶ psiWordAt ν μ r hr from cl D Sc μ s r L))
      (cl D Sc μ (u ++ s ++ []) (u ++ r ++ []) (L.map (whL u []))) := by
  have hs' : (ob D ν u).tensor (ob D μ s) = ob D μ (u ++ s ++ []) := by
    simpa only [List.append_nil] using ob_tensor ν μ u s hs
  have hr' : (ob D ν u).tensor (ob D μ r) = ob D μ (u ++ r ++ []) := by
    simpa only [List.append_nil] using ob_tensor ν μ u r hr
  apply (conj_eqToHom_iff_heq _ _ (congrArg (pres D Sc).obj hs')
    (congrArg (pres D Sc).obj hr')).1
  change (pres D Sc).wL (ob D ν u) (cl D Sc μ s r L) = _
  rw [cl_of hL]
  have hcomp : (ob D ν u).Composable (ob D μ s) :=
    Presentation.Bicat.Hom.composable
      (psiWordAt (Sc := Sc) (wt D ν u) ν u rfl) (psiWordAt ν μ s hs)
  rw [Presentation.wL_diag_of_composable _ _ _ hcomp, cl_of (hL.whisk u [])]
  refine Presentation.diag_eq_of_layers_eq' _ _ _ hs' hr' ?_
  simp only [Diagram.layers_lwhisker, layers_mkD]
  rw [← layList_whisker D μ u [] hL]
  simp only [wt_nil, hs, wd, Layer.wl, Layer.whisker, List.append_nil]

private theorem source_right_cl (ν μ : X) (s r v : List (Letter I))
    (hs : wt D (wt D μ v) s = ν) (hr : wt D (wt D μ v) r = ν)
    (L : List (LayerData I)) (hL : SChain s L r) :
    HEq (BicategoryStruct.whiskerRight (B := UGr D Sc sy hc)
      (show psiWordAt (Sc := Sc) ν (wt D μ v) s hs ⟶ psiWordAt ν (wt D μ v) r hr from
        cl D Sc (wt D μ v) s r L)
      (psiWordAt (Sc := Sc) (wt D μ v) μ v rfl))
      (cl D Sc μ ([] ++ s ++ v) ([] ++ r ++ v) (L.map (whL [] v))) := by
  have hs' : (ob D (wt D μ v) s).tensor (ob D μ v) = ob D μ ([] ++ s ++ v) := by
    simpa only [List.append_nil, List.nil_append] using ob_tensor (wt D μ v) μ s v rfl
  have hr' : (ob D (wt D μ v) r).tensor (ob D μ v) = ob D μ ([] ++ r ++ v) := by
    simpa only [List.append_nil, List.nil_append] using ob_tensor (wt D μ v) μ r v rfl
  apply (conj_eqToHom_iff_heq _ _ (congrArg (pres D Sc).obj hs')
    (congrArg (pres D Sc).obj hr')).1
  change (pres D Sc).wRAt ν (cl D Sc (wt D μ v) s r L) (ob D μ v) hs hr = _
  rw [cl_of hL]
  have hcomp : (ob D (wt D μ v) s).Composable (ob D μ v) :=
    Presentation.Bicat.Hom.composable
      (psiWordAt (Sc := Sc) ν (wt D μ v) s hs) (psiWordAt (wt D μ v) μ v rfl)
  rw [Presentation.wRAt_diag _ _ _ hcomp, cl_of (hL.whisk [] v)]
  refine Presentation.diag_eq_of_layers_eq' _ _ _ hs' hr' ?_
  simp only [Diagram.layers_rwhisker, layers_mkD]
  rw [← layList_whisker D μ [] v hL]
  simp only [ob, wd, Layer.wr, Layer.whisker, List.nil_append]
  apply List.map_congr_left
  intro l hl
  apply Layer.ext
  · exact (Diagram.chain (mkD D (wt D μ v) L hL)).start_of_mem (L := l) hl
  all_goals rfl

private theorem fixed_transport {a b : UGr D Sc sy hc} {f g f' g' : a ⟶ b}
    (hf : f = f') (hg : g = g') {x : f ⟶ g} {y : f' ⟶ g'} (h : HEq x y)
    (hx : rhoForwardInverseWordHom t ht f g x = x) :
    rhoForwardInverseWordHom t ht f' g' y = y := by
  exact eq_of_heq ((wordHom_heq t ht hf hg h).symm.trans ((heq_of_eq hx).trans h))

private theorem fixed_left_cl (ν μ : X) (u s r : List (Letter I))
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (L : List (LayerData I)) (hL : SChain s L r)
    (H : rhoForwardInverseWordHom (sy := sy) (hc := hc) t ht
      (psiWordAt ν μ s hs) (psiWordAt ν μ r hr) (cl D Sc μ s r L) = cl D Sc μ s r L) :
    rhoForwardInverseWordHom (sy := sy) (hc := hc) t ht
      (psiWordAt (wt D ν u) μ (u ++ s ++ []) (by simp only [List.append_nil, wt_append, hs]))
      (psiWordAt (wt D ν u) μ (u ++ r ++ []) (by simp only [List.append_nil, wt_append, hr]))
      (cl D Sc μ (u ++ s ++ []) (u ++ r ++ []) (L.map (whL u []))) =
      cl D Sc μ (u ++ s ++ []) (u ++ r ++ []) (L.map (whL u [])) := by
  apply fixed_transport t ht
    (Presentation.Bicat.Hom.ext (ob_tensor ν μ u s hs))
    (Presentation.Bicat.Hom.ext (ob_tensor ν μ u r hr))
    (source_left_cl (sy := sy) (hc := hc) ν μ u s r hs hr L hL)
  rw [rhoForwardInverseWordHom_whiskerLeft, H]

private theorem fixed_right_cl (ν μ : X) (s r v : List (Letter I))
    (hs : wt D (wt D μ v) s = ν) (hr : wt D (wt D μ v) r = ν)
    (L : List (LayerData I)) (hL : SChain s L r)
    (H : rhoForwardInverseWordHom (sy := sy) (hc := hc) t ht
      (psiWordAt ν (wt D μ v) s hs) (psiWordAt ν (wt D μ v) r hr)
      (cl D Sc (wt D μ v) s r L) = cl D Sc (wt D μ v) s r L) :
    rhoForwardInverseWordHom (sy := sy) (hc := hc) t ht
      (psiWordAt ν μ ([] ++ s ++ v) (by simpa only [List.nil_append, wt_append] using hs))
      (psiWordAt ν μ ([] ++ r ++ v) (by simpa only [List.nil_append, wt_append] using hr))
      (cl D Sc μ ([] ++ s ++ v) ([] ++ r ++ v) (L.map (whL [] v))) =
      cl D Sc μ ([] ++ s ++ v) ([] ++ r ++ v) (L.map (whL [] v)) := by
  apply fixed_transport t ht
    (by simpa only [List.nil_append] using (psiWordAt_comp_eq (Sc := Sc) ν (wt D μ v) μ s v hs rfl))
    (by simpa only [List.nil_append] using (psiWordAt_comp_eq (Sc := Sc) ν (wt D μ v) μ r v hr rfl))
    (source_right_cl (sy := sy) (hc := hc) ν μ s r v hs hr L hL)
  rw [rhoForwardInverseWordHom_whiskerRight, H]

private theorem fixed_reindex (ν μ : X) {s r s' r' : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (hs' : wt D μ s' = ν) (hr' : wt D μ r' = ν) (L : List (LayerData I))
    (es : s = s') (er : r = r')
    (H : rhoForwardInverseWordHom (sy := sy) (hc := hc) t ht
      (psiWordAt ν μ s hs) (psiWordAt ν μ r hr) (cl D Sc μ s r L) = cl D Sc μ s r L) :
    rhoForwardInverseWordHom (sy := sy) (hc := hc) t ht
      (psiWordAt ν μ s' hs') (psiWordAt ν μ r' hr') (cl D Sc μ s' r' L) = cl D Sc μ s' r' L := by
  cases es
  cases er
  exact H

private theorem normalized_layer (ν μ : X) (u : List (Letter I)) (g : Shape I)
    (v : List (Letter I)) (hs : wt D μ (u ++ g.dom ++ v) = ν) :
    rhoForwardInverseWordHom (sy := sy) (hc := hc) t ht
      (psiWordAt ν μ (u ++ g.dom ++ v) hs)
      (psiWordAt ν μ (u ++ g.cod ++ v)
        (by simpa only [wt_append, ← g.wt_dom_eq_wt_cod D] using hs))
      (cl D Sc μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u,g,v)]) =
      cl D Sc μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u,g,v)] := by
  have hgen : SChain g.dom [([],g,[])] g.cod := by simp [SChain]
  have Hr := fixed_right_cl (sy := sy) (hc := hc) t ht (wt D (wt D μ v) g.dom) μ g.dom g.cod v rfl
    (g.wt_dom_eq_wt_cod D (wt D μ v)).symm [([],g,[])] hgen
    (normalized_generator t ht _ _ g rfl)
  simp only [List.nil_append, List.map_cons, List.map_nil, whL, List.append_nil] at Hr
  have H := fixed_left_cl (sy := sy) (hc := hc) t ht (wt D (wt D μ v) g.dom) μ u (g.dom ++ v) (g.cod ++ v)
    (by rw [wt_append]) (by rw [wt_append, g.wt_dom_eq_wt_cod D])
    [([],g,v)] (by simp [SChain]) Hr
  have hν : wt D (wt D (wt D μ v) g.dom) u = ν := by
    simpa only [wt_append] using hs
  cases hν
  simp only [List.append_nil, List.map_cons, List.map_nil, whL] at H
  exact fixed_reindex t ht _ μ _ _ _ _ [(u,g,v)]
    (by simp only [List.append_nil, List.append_assoc])
    (by simp only [List.append_nil, List.append_assoc]) H

private theorem normalized_cl (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (L : List (LayerData I)) (hL : SChain s L r) :
    rhoForwardInverseWordHom (sy := sy) (hc := hc) t ht
      (psiWordAt ν μ s hs) (psiWordAt ν μ r hr) (cl D Sc μ s r L) = cl D Sc μ s r L := by
  induction L generalizing s with
  | nil =>
    cases hL
    rw [cl_nil]
    exact rhoForwardInverseWordHom_id t ht _
  | cons x L ih =>
    obtain ⟨rfl, hL⟩ := hL
    have hm : wt D μ (x.1 ++ x.2.1.cod ++ x.2.2) = ν := by
      simpa only [wt_append, ← x.2.1.wt_dom_eq_wt_cod D] using hs
    have hx : SChain (x.1 ++ x.2.1.dom ++ x.2.2) [x] (x.1 ++ x.2.1.cod ++ x.2.2) :=
      ⟨rfl,rfl⟩
    rw [show x :: L = [x] ++ L from rfl, ← cl_comp hx hL]
    erw [rhoForwardInverseWordHom_comp t ht
      (f := psiWordAt ν μ _ hs) (g := psiWordAt ν μ _ hm) (h := psiWordAt ν μ r hr)]
    rw [normalized_layer t ht ν μ x.1 x.2.1 x.2.2 hs, ih hm hL]
    rfl

theorem rhoForwardInverseWordHom_apply {a b : UGr D Sc sy hc}
    (f g : a ⟶ b) (x : f ⟶ g) : rhoForwardInverseWordHom t ht f g x = x := by
  obtain ⟨s, hs, rfl⟩ := exists_psiWordAt f
  obtain ⟨r, hr, rfl⟩ := exists_psiWordAt g
  induction x using (pres D Sc).hom_induction with
  | diag d =>
    obtain ⟨L, hL, rfl⟩ := diag_eq_mkD d
    rw [← cl_of hL]
    exact normalized_cl t ht _ _ hs hr L hL
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | smul r x hx => rw [map_smul, hx]

theorem rhoForwardInverse_word {a b : UGr D Sc sy hc}
    (f g : a ⟶ b) (x : f ⟶ g) :
    HEq ((rhoInverse t ht).map₂ ((rhoEnvelope t ht).map₂
      (show QPiTwoEnvelope.Jm (R := k) f ⟶ QPiTwoEnvelope.Jm g from x))) x :=
  (normalized_heq t ht (f := QPiTwoEnvelope.Jm f)
    (g := QPiTwoEnvelope.Jm g) x).symm.trans
    (heq_of_eq (rhoForwardInverseWordHom_apply t ht f g x))

private theorem base_map_heq {a b : UGr D Sc sy hc} {f g f' g' : a ⟶ b}
    (ef : f = f') (eg : g = g') {x : f ⟶ g} {y : f' ⟶ g'} (h : HEq x y) :
    HEq (rhoMap₂ t ht f g x) (rhoMap₂ t ht f' g' y) := by
  subst f' g'
  cases h
  rfl

private theorem zero_map_heq {a b : Uqπ D Sc sy hc} {f g f' g' : a ⟶ b}
    (hf : f.par = 0) (hg : g.par = 0) (hf' : f'.par = 0) (hg' : g'.par = 0)
    (ef : f.obj.obj = f'.obj.obj) (eg : g.obj.obj = g'.obj.obj)
    {x : f ⟶ g} {y : f' ⟶ g'} (h : HEq x y) :
    HEq ((rhoEnvelope t ht).map₂ x) ((rhoEnvelope t ht).map₂ y) := by
  have H : HEq (QPiTwoEnvelope.toHom x) (QPiTwoEnvelope.toHom y) := h
  exact (RhoGeneratorRoundtrips.envelope_zero_heq t ht hf hg x).trans
    ((base_map_heq t ht ef eg H).trans
      (RhoGeneratorRoundtrips.envelope_zero_heq t ht hf' hg' y).symm)

theorem rhoForwardInverse_zero {a b : Uqπ D Sc sy hc} (f g : a ⟶ b)
    (hf : f.par = 0) (hg : g.par = 0) (x : f ⟶ g) :
    HEq ((rhoInverse t ht).map₂ ((rhoEnvelope t ht).map₂ x)) x := by
  let f' := QPiTwoEnvelope.Jm (R := k) f.obj.obj
  let g' := QPiTwoEnvelope.Jm (R := k) g.obj.obj
  have H := zero_map_heq t ht hf hg (f' := f') (g' := g') rfl rfl rfl rfl
    (x := x) (y := show f' ⟶ g' from x) HEq.rfl
  have ef : ((rhoEnvelope t ht).map f).obj.obj = ((rhoEnvelope t ht).map f').obj.obj := by
    apply Presentation.Bicat.Hom.ext
    rw [rhoEnvelope_map_word, rhoEnvelope_map_word]
    rfl
  have eg : ((rhoEnvelope t ht).map g).obj.obj = ((rhoEnvelope t ht).map g').obj.obj := by
    apply Presentation.Bicat.Hom.ext
    rw [rhoEnvelope_map_word, rhoEnvelope_map_word]
    rfl
  have H' := zero_map_heq (-t) (by simpa only [neg_sq] using ht)
    ((rhoEnvelope_map_par t ht f).trans hf) ((rhoEnvelope_map_par t ht g).trans hg)
    (rhoEnvelope_map_par t ht f') (rhoEnvelope_map_par t ht g') ef eg H
  exact H'.trans (rhoForwardInverse_word t ht f.obj.obj g.obj.obj x)

theorem rhoInverseForward_zero {a b : TwoSRev k (Uqπ D Sc sy hc)} (f g : a ⟶ b)
    (hf : f.par = 0) (hg : g.par = 0) (x : f ⟶ g) :
    HEq ((rhoEnvelope t ht).map₂ ((rhoInverse t ht).map₂ x)) x := by
  have H := rhoForwardInverse_zero (-t) (by simpa only [neg_sq] using ht) f g hf hg x
  change HEq ((rhoEnvelope (-(-t)) _).map₂ ((rhoEnvelope (-t) _).map₂ x)) x at H
  have e : rhoEnvelope (sy := sy) (hc := hc) (-(-t))
      (by simpa only [neg_sq] using ht) = rhoEnvelope t ht := by
    congr 1
    exact neg_neg t
  rw [e] at H
  exact H

end OddMath.SKM.RhoQuotientRoundtrips
