import OddMath.SKM.PsiInverseLaws
import OddMath.SKM.PsiRoundtrips

/-!
# Inverse identities for ψ

Both composites in Brundan–Ellis, *Super Kac–Moody 2-categories*,
Proposition 9.4 are identities on arbitrary Q/Π-envelope 2-morphisms and on
all fields of the associated 2-superfunctors. The proof extends the generator
roundtrips through the presented quotient and parity decomposition; the reverse
identity follows by exchanging the involutive parameter sets.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct QPiSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}
variable (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)

local instance : ∀ a b : TwoSOp k (Uqπ D Sc sy hc), QPiSupercategory k (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b

private theorem forward_on_word {a b : UGr D Sc sy hc} {f g : a ⟶ b} (x : f ⟶ g) :
    (psiExtension t ht cs).map₂ (show QPiTwoEnvelope.Jm (R := k) f ⟶ QPiTwoEnvelope.Jm g from x) =
      psiMap₂ t ht cs f g x := by
  change 𝟙 _ ≫ (𝟙 _ ≫ psiMap₂ t ht cs f g x ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

private theorem sign_word_zero {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    psiInverseSign (sy := sy) (hc := hc) (SOp.unop (psiMap f)) = 0 := by
  change psiParity (sy := sy) (hc := hc) f * (1 + psiParity (sy := sy) (hc := hc) f) = 0
  have H (p : ZMod 2) : p * (1 + p) = 0 := by revert p; decide
  exact H _

private theorem qpi_zero {a b : UGr D Sc sy hc}
    {f g : psiObj a ⟶ psiObj b} (p q : ZMod 2) (x : f ⟶ g) :
    psiQPiConjugate (Sc := Sc) 0 0 p q x = psiPiConjugate p q x := by
  simp only [psiQPiConjugate, psiQConjugate, psiQIso,
    σPow_zero, Iso.refl_hom, Iso.refl_inv, Category.comp_id]
  congr 1
  exact Category.id_comp x

private theorem inverse_on_word {a b : UGr D Sc sy hc} {f g : a ⟶ b} (x : f ⟶ g) :
    QPiTwoEnvelope.toHom ((psiInverseFunctor t ht cs).map₂ (psiMap₂ t ht cs f g x)) =
      QPiTwoEnvelope.toHom (SOp.unsop
        (psiPiConjugate (psiParity g) (psiParity f)
          (psiMap₂ (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs) g f
            (QPiTwoEnvelope.toHom (SOp.unsop (psiMap₂ t ht cs f g x)))))) := by
  rw [psiInverseFunctor_map₂]
  change sign k (psiInverseSign (SOp.unop (psiMap f)) + psiInverseSign (SOp.unop (psiMap g))) •
    QPiTwoEnvelope.toHom (SOp.unsop
      ((psiExtension (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)).map₂
        (SOp.unsop (psiMap₂ t ht cs f g x)))) = _
  rw [sign_word_zero, sign_word_zero, zero_add, sign_zero, one_smul, psiExtension_map₂_eq]
  change QPiTwoEnvelope.toHom (SOp.unsop (psiQPiConjugate 0 0 (psiParity g) (psiParity f)
    (psiMap₂ (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs) g f
      (QPiTwoEnvelope.toHom (SOp.unsop (psiMap₂ t ht cs f g x)))))) = _
  rw [qpi_zero]

theorem psiForwardInverse_word (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)) :
    HEq (QPiTwoEnvelope.toHom
      ((psiInverseFunctor (sy := sy) (hc := hc) t ht cs).map₂
        ((psiExtension t ht cs).map₂
          (show QPiTwoEnvelope.Jm (R := k) (B := UGr D Sc sy hc) (psiWordAt ν μ s hs) ⟶
            QPiTwoEnvelope.Jm (R := k) (B := UGr D Sc sy hc) (psiWordAt ν μ r hr) from x))))
      (psiWordDouble (sy := sy) (hc := hc) t ht cs ν μ hs hr x) := by
  erw [forward_on_word t ht cs (f := psiWordAt ν μ s hs) (g := psiWordAt ν μ r hr)]
  exact heq_of_eq (inverse_on_word t ht cs (f := psiWordAt ν μ s hs)
    (g := psiWordAt ν μ r hr) x)

private theorem envelope_heq {a b : Uqπ D Sc sy hc} {f g f' g' : a ⟶ b}
    (hf : f = f') (hg : g = g') (x : f ⟶ g) (y : f' ⟶ g')
    (h : HEq (QPiTwoEnvelope.toHom x) (QPiTwoEnvelope.toHom y)) : HEq x y := by
  cases hf
  cases hg
  exact heq_of_eq (eq_of_heq h)

/-- The seven original generators return under the actual composite 2-map. -/
theorem psiForwardInverse_generator (ν μ : X) (g : Shape I) (hs : wt D μ g.dom = ν) :
    HEq ((psiInverseFunctor (sy := sy) (hc := hc) t ht cs).map₂
      ((psiExtension t ht cs).map₂
        (show QPiTwoEnvelope.Jm (R := k) (B := UGr D Sc sy hc) (psiWordAt ν μ g.dom hs) ⟶
          QPiTwoEnvelope.Jm (R := k) (B := UGr D Sc sy hc)
            (psiWordAt ν μ g.cod ((g.wt_dom_eq_wt_cod D μ).symm.trans hs)) from
          cl D Sc μ g.dom g.cod [([], g, [])])))
      (show QPiTwoEnvelope.Jm (R := k) (B := UGr D Sc sy hc) (psiWordAt ν μ g.dom hs) ⟶
          QPiTwoEnvelope.Jm (R := k) (B := UGr D Sc sy hc)
            (psiWordAt ν μ g.cod ((g.wt_dom_eq_wt_cod D μ).symm.trans hs)) from
          cl D Sc μ g.dom g.cod [([], g, [])]) := by
  apply envelope_heq (psiInverseFunctor_map_forward t ht cs _) (psiInverseFunctor_map_forward t ht cs _)
  exact (psiForwardInverse_word t ht cs ν μ hs _ _).trans
    (psiGenerator_parameter_roundtrip t ht cs ν μ g hs)

/-- The actual forward/inverse composite, transported back to its original Hom space. -/
def psiForwardInverseHom {a b : Uqπ D Sc sy hc} (f g : a ⟶ b) : (f ⟶ g) →ₗ[k] (f ⟶ g) where
  toFun x := eqToHom (psiInverseFunctor_map_forward t ht cs f).symm ≫
    (psiInverseFunctor t ht cs).map₂ ((psiExtension t ht cs).map₂ x) ≫
    eqToHom (psiInverseFunctor_map_forward t ht cs g)
  map_add' x y := by simp only [TwoSuperfunctor.map₂_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r x := by simp only [TwoSuperfunctor.map₂_smul, Linear.smul_comp, Linear.comp_smul]; rfl

private theorem normalized_heq {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (x : f ⟶ g) :
    HEq (psiForwardInverseHom t ht cs f g x)
      ((psiInverseFunctor t ht cs).map₂ ((psiExtension t ht cs).map₂ x)) :=
  (conj_eqToHom_iff_heq _ _ (psiInverseFunctor_map_forward t ht cs f).symm
    (psiInverseFunctor_map_forward t ht cs g).symm).1 rfl

private theorem whisker_left_heq {a b c : Uqπ D Sc sy hc}
    {f f' : a ⟶ b} {g g' h h' : b ⟶ c} (hf : f = f') (hg : g = g') (hh : h = h')
    {x : g ⟶ h} {y : g' ⟶ h'} (hxy : HEq x y) : HEq (f ◁ x) (f' ◁ y) := by
  cases hf; cases hg; cases hh; cases hxy; rfl

private theorem whisker_right_heq {a b c : Uqπ D Sc sy hc}
    {f f' g g' : a ⟶ b} {h h' : b ⟶ c} (hf : f = f') (hg : g = g') (hh : h = h')
    {x : f ⟶ g} {y : f' ⟶ g'} (hxy : HEq x y) : HEq (x ▷ h) (y ▷ h') := by
  cases hf; cases hg; cases hh; cases hxy; rfl

theorem psiForwardInverseHom_whiskerLeft {a b c : Uqπ D Sc sy hc}
    (f : a ⟶ b) {g h : b ⟶ c} (x : g ⟶ h) :
    psiForwardInverseHom t ht cs (f ≫ g) (f ≫ h) (f ◁ x) =
      f ◁ psiForwardInverseHom t ht cs g h x := by
  apply eq_of_heq
  exact (normalized_heq t ht cs (f ◁ x)).trans
    ((psiForwardInverse_whiskerLeft t ht cs f x).trans
      (whisker_left_heq (psiInverseFunctor_map_forward t ht cs f)
        (psiInverseFunctor_map_forward t ht cs g) (psiInverseFunctor_map_forward t ht cs h)
        (normalized_heq t ht cs x).symm))

theorem psiForwardInverseHom_whiskerRight {a b c : Uqπ D Sc sy hc}
    {f g : a ⟶ b} (x : f ⟶ g) (h : b ⟶ c) :
    psiForwardInverseHom t ht cs (f ≫ h) (g ≫ h) (x ▷ h) =
      psiForwardInverseHom t ht cs f g x ▷ h := by
  apply eq_of_heq
  exact (normalized_heq t ht cs (x ▷ h)).trans
    ((psiForwardInverse_whiskerRight t ht cs x h).trans
      (whisker_right_heq (psiInverseFunctor_map_forward t ht cs f)
        (psiInverseFunctor_map_forward t ht cs g) (psiInverseFunctor_map_forward t ht cs h)
        (normalized_heq t ht cs x).symm))

theorem psiForwardInverseHom_id {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    psiForwardInverseHom t ht cs f f (𝟙 f) = 𝟙 f := by
  simp only [psiForwardInverseHom, LinearMap.coe_mk, AddHom.coe_mk, TwoSuperfunctor.map₂_id,
    Category.id_comp, eqToHom_trans, eqToHom_refl]

theorem psiForwardInverseHom_comp {a b : Uqπ D Sc sy hc} {f g h : a ⟶ b}
    (x : f ⟶ g) (y : g ⟶ h) :
    psiForwardInverseHom t ht cs f h (x ≫ y) =
      psiForwardInverseHom t ht cs f g x ≫ psiForwardInverseHom t ht cs g h y := by
  simp only [psiForwardInverseHom, LinearMap.coe_mk, AddHom.coe_mk, TwoSuperfunctor.map₂_comp,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

theorem psiForwardInverseHom_eqToHom {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (e : f = g) :
    psiForwardInverseHom t ht cs f g (eqToHom e) = eqToHom e := by
  cases e
  exact psiForwardInverseHom_id t ht cs f

/-- The normalized composite restricted to the original quotient Hom spaces. -/
def psiForwardInverseWordHom {a b : UGr D Sc sy hc} (f g : a ⟶ b) : (f ⟶ g) →ₗ[k] (f ⟶ g) :=
  psiForwardInverseHom t ht cs (QPiTwoEnvelope.Jm (R := k) f) (QPiTwoEnvelope.Jm g)

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

theorem psiForwardInverseWordHom_whiskerLeft {a b c : UGr D Sc sy hc}
    (f : a ⟶ b) {g h : b ⟶ c} (x : g ⟶ h) :
    psiForwardInverseWordHom t ht cs (f ≫ g) (f ≫ h) (f ◁ x) =
      f ◁ psiForwardInverseWordHom t ht cs g h x := by
  have H := psiForwardInverseHom_whiskerLeft t ht cs (QPiTwoEnvelope.Jm (R := k) f)
    (show QPiTwoEnvelope.Jm (R := k) g ⟶ QPiTwoEnvelope.Jm h from x)
  rw [j_left, j_left] at H
  exact H

theorem psiForwardInverseWordHom_whiskerRight {a b c : UGr D Sc sy hc}
    {f g : a ⟶ b} (x : f ⟶ g) (h : b ⟶ c) :
    psiForwardInverseWordHom t ht cs (f ≫ h) (g ≫ h) (x ▷ h) =
      psiForwardInverseWordHom t ht cs f g x ▷ h := by
  have H := psiForwardInverseHom_whiskerRight t ht cs
    (show QPiTwoEnvelope.Jm (R := k) f ⟶ QPiTwoEnvelope.Jm g from x) (QPiTwoEnvelope.Jm (R := k) h)
  rw [j_right, j_right] at H
  exact H

theorem psiForwardInverseWordHom_id {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    psiForwardInverseWordHom t ht cs f f (𝟙 f) = 𝟙 f :=
  psiForwardInverseHom_id t ht cs _

theorem psiForwardInverseWordHom_comp {a b : UGr D Sc sy hc} {f g h : a ⟶ b}
    (x : f ⟶ g) (y : g ⟶ h) :
    psiForwardInverseWordHom t ht cs f h (x ≫ y) =
      psiForwardInverseWordHom t ht cs f g x ≫ psiForwardInverseWordHom t ht cs g h y :=
  psiForwardInverseHom_comp t ht cs
    (f := QPiTwoEnvelope.Jm (R := k) f) (g := QPiTwoEnvelope.Jm (R := k) g)
    (h := QPiTwoEnvelope.Jm (R := k) h) x y

theorem psiForwardInverseWordHom_eqToHom {a b : UGr D Sc sy hc} {f g : a ⟶ b} (e : f = g) :
    psiForwardInverseWordHom t ht cs f g (eqToHom e) = eqToHom e := by
  cases e
  exact psiForwardInverseWordHom_id t ht cs _

private theorem wordHom_heq {a b : UGr D Sc sy hc} {f g f' g' : a ⟶ b}
    (hf : f = f') (hg : g = g') {x : f ⟶ g} {y : f' ⟶ g'} (h : HEq x y) :
    HEq (psiForwardInverseWordHom t ht cs f g x) (psiForwardInverseWordHom t ht cs f' g' y) := by
  cases hf; cases hg; cases h; rfl

private theorem normalized_generator (ν μ : X) (g : Shape I) (hs : wt D μ g.dom = ν) :
    psiForwardInverseWordHom (sy := sy) (hc := hc) t ht cs (psiWordAt ν μ g.dom hs)
      (psiWordAt ν μ g.cod ((g.wt_dom_eq_wt_cod D μ).symm.trans hs))
      (cl D Sc μ g.dom g.cod [([], g, [])]) = cl D Sc μ g.dom g.cod [([], g, [])] := by
  exact eq_of_heq ((normalized_heq t ht cs _).trans (psiForwardInverse_generator t ht cs ν μ g hs))

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
    (hx : psiForwardInverseWordHom t ht cs f g x = x) :
    psiForwardInverseWordHom t ht cs f' g' y = y := by
  exact eq_of_heq ((wordHom_heq t ht cs hf hg h).symm.trans ((heq_of_eq hx).trans h))

private theorem fixed_left_cl (ν μ : X) (u s r : List (Letter I))
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (L : List (LayerData I)) (hL : SChain s L r)
    (H : psiForwardInverseWordHom (sy := sy) (hc := hc) t ht cs
      (psiWordAt ν μ s hs) (psiWordAt ν μ r hr) (cl D Sc μ s r L) = cl D Sc μ s r L) :
    psiForwardInverseWordHom (sy := sy) (hc := hc) t ht cs
      (psiWordAt (wt D ν u) μ (u ++ s ++ []) (by simp only [List.append_nil, wt_append, hs]))
      (psiWordAt (wt D ν u) μ (u ++ r ++ []) (by simp only [List.append_nil, wt_append, hr]))
      (cl D Sc μ (u ++ s ++ []) (u ++ r ++ []) (L.map (whL u []))) =
      cl D Sc μ (u ++ s ++ []) (u ++ r ++ []) (L.map (whL u [])) := by
  apply fixed_transport t ht cs
    (Presentation.Bicat.Hom.ext (ob_tensor ν μ u s hs))
    (Presentation.Bicat.Hom.ext (ob_tensor ν μ u r hr))
    (source_left_cl (sy := sy) (hc := hc) ν μ u s r hs hr L hL)
  rw [psiForwardInverseWordHom_whiskerLeft, H]

private theorem fixed_right_cl (ν μ : X) (s r v : List (Letter I))
    (hs : wt D (wt D μ v) s = ν) (hr : wt D (wt D μ v) r = ν)
    (L : List (LayerData I)) (hL : SChain s L r)
    (H : psiForwardInverseWordHom (sy := sy) (hc := hc) t ht cs
      (psiWordAt ν (wt D μ v) s hs) (psiWordAt ν (wt D μ v) r hr)
      (cl D Sc (wt D μ v) s r L) = cl D Sc (wt D μ v) s r L) :
    psiForwardInverseWordHom (sy := sy) (hc := hc) t ht cs
      (psiWordAt ν μ ([] ++ s ++ v) (by simpa only [List.nil_append, wt_append] using hs))
      (psiWordAt ν μ ([] ++ r ++ v) (by simpa only [List.nil_append, wt_append] using hr))
      (cl D Sc μ ([] ++ s ++ v) ([] ++ r ++ v) (L.map (whL [] v))) =
      cl D Sc μ ([] ++ s ++ v) ([] ++ r ++ v) (L.map (whL [] v)) := by
  apply fixed_transport t ht cs
    (by simpa only [List.nil_append] using (psiWordAt_comp_eq (Sc := Sc) ν (wt D μ v) μ s v hs rfl))
    (by simpa only [List.nil_append] using (psiWordAt_comp_eq (Sc := Sc) ν (wt D μ v) μ r v hr rfl))
    (source_right_cl (sy := sy) (hc := hc) ν μ s r v hs hr L hL)
  rw [psiForwardInverseWordHom_whiskerRight, H]

private theorem fixed_reindex (ν μ : X) {s r s' r' : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (hs' : wt D μ s' = ν) (hr' : wt D μ r' = ν) (L : List (LayerData I))
    (es : s = s') (er : r = r')
    (H : psiForwardInverseWordHom (sy := sy) (hc := hc) t ht cs
      (psiWordAt ν μ s hs) (psiWordAt ν μ r hr) (cl D Sc μ s r L) = cl D Sc μ s r L) :
    psiForwardInverseWordHom (sy := sy) (hc := hc) t ht cs
      (psiWordAt ν μ s' hs') (psiWordAt ν μ r' hr') (cl D Sc μ s' r' L) = cl D Sc μ s' r' L := by
  cases es
  cases er
  exact H

private theorem normalized_layer (ν μ : X) (u : List (Letter I)) (g : Shape I)
    (v : List (Letter I)) (hs : wt D μ (u ++ g.dom ++ v) = ν) :
    psiForwardInverseWordHom (sy := sy) (hc := hc) t ht cs
      (psiWordAt ν μ (u ++ g.dom ++ v) hs)
      (psiWordAt ν μ (u ++ g.cod ++ v)
        (by simpa only [wt_append, ← g.wt_dom_eq_wt_cod D] using hs))
      (cl D Sc μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u,g,v)]) =
      cl D Sc μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u,g,v)] := by
  have hgen : SChain g.dom [([],g,[])] g.cod := by simp [SChain]
  have Hr := fixed_right_cl (sy := sy) (hc := hc) t ht cs (wt D (wt D μ v) g.dom) μ g.dom g.cod v rfl
    (g.wt_dom_eq_wt_cod D (wt D μ v)).symm [([],g,[])] hgen
    (normalized_generator t ht cs _ _ g rfl)
  simp only [List.nil_append, List.map_cons, List.map_nil, whL, List.append_nil] at Hr
  have H := fixed_left_cl (sy := sy) (hc := hc) t ht cs (wt D (wt D μ v) g.dom) μ u (g.dom ++ v) (g.cod ++ v)
    (by rw [wt_append]) (by rw [wt_append, g.wt_dom_eq_wt_cod D])
    [([],g,v)] (by simp [SChain]) Hr
  have hν : wt D (wt D (wt D μ v) g.dom) u = ν := by
    simpa only [wt_append] using hs
  cases hν
  simp only [List.append_nil, List.map_cons, List.map_nil, whL] at H
  exact fixed_reindex t ht cs _ μ _ _ _ _ [(u,g,v)]
    (by simp only [List.append_nil, List.append_assoc])
    (by simp only [List.append_nil, List.append_assoc]) H

private theorem normalized_cl (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (L : List (LayerData I)) (hL : SChain s L r) :
    psiForwardInverseWordHom (sy := sy) (hc := hc) t ht cs
      (psiWordAt ν μ s hs) (psiWordAt ν μ r hr) (cl D Sc μ s r L) = cl D Sc μ s r L := by
  induction L generalizing s with
  | nil =>
    cases hL
    rw [cl_nil]
    exact psiForwardInverseWordHom_id t ht cs _
  | cons x L ih =>
    obtain ⟨rfl, hL⟩ := hL
    have hm : wt D μ (x.1 ++ x.2.1.cod ++ x.2.2) = ν := by
      simpa only [wt_append, ← x.2.1.wt_dom_eq_wt_cod D] using hs
    have hx : SChain (x.1 ++ x.2.1.dom ++ x.2.2) [x] (x.1 ++ x.2.1.cod ++ x.2.2) :=
      ⟨rfl,rfl⟩
    rw [show x :: L = [x] ++ L from rfl, ← cl_comp hx hL]
    erw [psiForwardInverseWordHom_comp t ht cs
      (f := psiWordAt ν μ _ hs) (g := psiWordAt ν μ _ hm) (h := psiWordAt ν μ r hr)]
    rw [normalized_layer t ht cs ν μ x.1 x.2.1 x.2.2 hs, ih hm hL]
    rfl

/-- The normalized composite is the identity on every morphism of the original quotient,
including arbitrary linear combinations of different parities and degrees. -/
theorem psiForwardInverseWordHom_apply {a b : UGr D Sc sy hc}
    (f g : a ⟶ b) (x : f ⟶ g) : psiForwardInverseWordHom t ht cs f g x = x := by
  obtain ⟨s, hs, rfl⟩ := exists_psiWordAt f
  obtain ⟨r, hr, rfl⟩ := exists_psiWordAt g
  induction x using (pres D Sc).hom_induction with
  | diag d =>
    obtain ⟨L, hL, rfl⟩ := diag_eq_mkD d
    rw [← cl_of hL]
    exact normalized_cl t ht cs _ _ hs hr L hL
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | smul r x hx => rw [map_smul, hx]

private def baseReverse {a b : UGr D Sc sy hc} (f g : a ⟶ b) : (f ⟶ g) →ₗ[k] (g ⟶ f) where
  toFun x := QPiTwoEnvelope.toHom (SOp.unsop (psiMap₂ t ht cs f g x))
  map_add' x y := by rw [map_add]; rfl
  map_smul' r x := by rw [map_smul]; rfl

private theorem underlying_heq {a b : Uqπ D Sc sy hc} {f g f' g' : a ⟶ b}
    (hf : f = f') (hg : g = g') {x : f ⟶ g} {y : f' ⟶ g'} (h : HEq x y) :
    HEq (QPiTwoEnvelope.toHom x) (QPiTwoEnvelope.toHom y) := by
  cases hf; cases hg; cases h; rfl

private theorem word_roundtrip_heq {a b : UGr D Sc sy hc} (f g : a ⟶ b) (x : f ⟶ g) :
    HEq (QPiTwoEnvelope.toHom ((psiInverseFunctor t ht cs).map₂ (psiMap₂ t ht cs f g x))) x := by
  have H := (normalized_heq t ht cs
    (f := QPiTwoEnvelope.Jm (R := k) f) (g := QPiTwoEnvelope.Jm (R := k) g) x).symm.trans
    (heq_of_eq (psiForwardInverseWordHom_apply t ht cs f g x))
  have H' := underlying_heq (psiInverseFunctor_map_forward t ht cs (QPiTwoEnvelope.Jm f))
    (psiInverseFunctor_map_forward t ht cs (QPiTwoEnvelope.Jm g)) H
  erw [forward_on_word t ht cs (f := f) (g := g)] at H'
  exact H'

private theorem base_double_signed {a b : UGr D Sc sy hc} (f g : a ⟶ b)
    {x : f ⟶ g} {r : ZMod 2} (hx : x ∈ parity (R := k) _ _ r) :
    sign k (psiParity g * (r + (psiParity g + psiParity f)) +
      (psiParity g + (r + (psiParity g + psiParity f))) * psiParity f + psiParity f) •
      baseReverse (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs) g f
        (baseReverse t ht cs f g x) = x := by
  have hx' : baseReverse t ht cs f g x ∈ parity (R := k) g f
      (r + (psiParity g + psiParity f)) := psiMap₂_mem_parity t ht cs hx
  have H := word_roundtrip_heq t ht cs f g x
  rw [inverse_on_word] at H
  have H' := psiPiConjugate_heq (psiParity g) (psiParity f) _
    (psiMap₂_mem_parity (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs) hx')
  exact eq_of_heq (H'.symm.trans H)

private theorem baseReverse_heq {a b : UGr D Sc sy hc} {f g f' g' : a ⟶ b}
    (hf : f = f') (hg : g = g') {x : f ⟶ g} {y : f' ⟶ g'} (h : HEq x y) :
    HEq (baseReverse t ht cs f g x) (baseReverse t ht cs f' g' y) := by
  cases hf; cases hg; cases h; rfl

private theorem scalar_heq {a b : UGr D Sc sy hc} {f g f' g' : a ⟶ b}
    (hf : f = f') (hg : g = g') {x : f ⟶ g} {y : f' ⟶ g'} (h : HEq x y) (c : k) :
    HEq (c • x) (c • y) := by
  cases hf; cases hg; cases h; rfl

private theorem extension_par {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    (SOp.unop ((psiExtension t ht cs).map f)).par = f.par + psiParity f.obj.obj :=
  congrArg (fun z => z.par) (psiExtension_map_eq_psiShift t ht cs f)

private theorem extension_inverseSign {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    psiInverseSign (SOp.unop ((psiExtension t ht cs).map f)) = psiInverseSign f := by
  rw [psiExtension_map_eq_psiShift, psiInverseSign_psiShift]

private theorem extension_raw_mem {a b : Uqπ D Sc sy hc} {f g : a ⟶ b}
    {x : f ⟶ g} {r : ZMod 2} (hx : QPiTwoEnvelope.toHom x ∈ parity (R := k) _ _ r) :
    QPiTwoEnvelope.toHom (SOp.unsop ((psiExtension t ht cs).map₂ x)) ∈ parity (R := k) _ _
      (r + (psiParity g.obj.obj + psiParity f.obj.obj)) := by
  have Hx : x ∈ parity (R := k) f g (r + (f.par + g.par)) := by
    change QPiTwoEnvelope.toHom x ∈ parity (R := k) _ _ (r + (f.par + g.par) + (f.par + g.par))
    rw [add_assoc, zmod2_add_self, add_zero]
    exact hx
  have H := (psiExtension t ht cs).map₂_mem Hx
  change QPiTwoEnvelope.toHom (SOp.unsop ((psiExtension t ht cs).map₂ x)) ∈ parity (R := k) _ _
    (r + (f.par + g.par) + ((SOp.unop ((psiExtension t ht cs).map g)).par +
      (SOp.unop ((psiExtension t ht cs).map f)).par)) at H
  rw [extension_par, extension_par] at H
  convert H using 1
  congr 1
  have e (r a b p q : ZMod 2) : r + (q+p) = r + (a+b) + ((b+q)+(a+p)) := by
    revert r a b p q; decide
  exact e _ _ _ _ _

private theorem forward_raw_double {a b : Uqπ D Sc sy hc} {f g : a ⟶ b}
    {x : f ⟶ g} {r : ZMod 2} (hx : QPiTwoEnvelope.toHom x ∈ parity (R := k) _ _ r) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop
      ((psiExtension (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)).map₂
        (SOp.unsop ((psiExtension t ht cs).map₂ x)))))
      (sign k ((g.par + psiParity g.obj.obj) * (r + (psiParity g.obj.obj + psiParity f.obj.obj)) +
       ((g.par + psiParity g.obj.obj) + (r + (psiParity g.obj.obj + psiParity f.obj.obj))) *
         (f.par + psiParity f.obj.obj) + (f.par + psiParity f.obj.obj)) •
       sign k (f.par * r + (f.par + r) * g.par + g.par) •
       baseReverse (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs) g.obj.obj f.obj.obj
         (baseReverse t ht cs f.obj.obj g.obj.obj (QPiTwoEnvelope.toHom x))) := by
  have ef : (SOp.unop ((psiExtension t ht cs).map f)).obj.obj = f.obj.obj :=
    congrArg (fun z => z.obj.obj) (psiExtension_map_eq_psiShift t ht cs f)
  have eg : (SOp.unop ((psiExtension t ht cs).map g)).obj.obj = g.obj.obj :=
    congrArg (fun z => z.obj.obj) (psiExtension_map_eq_psiShift t ht cs g)
  have H1 := psiExtension_map₂_toHom_heq t ht cs hx
  have H2 := psiExtension_map₂_toHom_heq (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
    (extension_raw_mem t ht cs hx)
  have HB := baseReverse_heq (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs) eg ef H1
  have HS := scalar_heq ef eg HB (sign k
    ((SOp.unop ((psiExtension t ht cs).map g)).par * (r + (psiParity g.obj.obj + psiParity f.obj.obj)) +
      ((SOp.unop ((psiExtension t ht cs).map g)).par + (r + (psiParity g.obj.obj + psiParity f.obj.obj))) *
        (SOp.unop ((psiExtension t ht cs).map f)).par + (SOp.unop ((psiExtension t ht cs).map f)).par))
  have HH := H2.trans HS
  simp only [map_smul] at HH
  rw [extension_par, extension_par] at HH
  exact HH

private theorem correction_cancel {a b : Uqπ D Sc sy hc} (f g : a ⟶ b) (r : ZMod 2) :
    psiInverseSign f + psiInverseSign g +
      ((g.par + psiParity g.obj.obj) * (r + (psiParity g.obj.obj + psiParity f.obj.obj)) +
       ((g.par + psiParity g.obj.obj) + (r + (psiParity g.obj.obj + psiParity f.obj.obj))) *
         (f.par + psiParity f.obj.obj) + (f.par + psiParity f.obj.obj) +
       (f.par * r + (f.par + r) * g.par + g.par)) =
      psiParity g.obj.obj * (r + (psiParity g.obj.obj + psiParity f.obj.obj)) +
      (psiParity g.obj.obj + (r + (psiParity g.obj.obj + psiParity f.obj.obj))) * psiParity f.obj.obj +
      psiParity f.obj.obj := by
  have residual := psiInverseSign_extension_residual f.par g.par
    (psiParity f.obj.obj) (psiParity g.obj.obj) r
  rw [show r + psiParity f.obj.obj + psiParity g.obj.obj =
    r + (psiParity g.obj.obj + psiParity f.obj.obj) by abel] at residual
  have cancel (u v w : ZMod 2) : (u + v + w) + (v + u) = w := by
    revert u v w; decide
  change f.par * (1 + psiParity f.obj.obj) + g.par * (1 + psiParity g.obj.obj) + _ = _
  rw [← residual]
  exact cancel _ _ _

private theorem inverse_raw_map {a b : TwoSOp k (Uqπ D Sc sy hc)} {f g : a ⟶ b}
    (y : f ⟶ g) : QPiTwoEnvelope.toHom ((psiInverseFunctor t ht cs).map₂ y) =
      sign k (psiInverseSign (SOp.unop f) + psiInverseSign (SOp.unop g)) •
        QPiTwoEnvelope.toHom (SOp.unsop
          ((psiExtension (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)).map₂ (SOp.unsop y))) := by
  rw [psiInverseFunctor_map₂]
  rfl

private theorem forward_raw_correction {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (x : f ⟶ g) :
    QPiTwoEnvelope.toHom ((psiInverseFunctor t ht cs).map₂ ((psiExtension t ht cs).map₂ x)) =
      sign k (psiInverseSign f + psiInverseSign g) •
        QPiTwoEnvelope.toHom (SOp.unsop
          ((psiExtension (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)).map₂
            (SOp.unsop ((psiExtension t ht cs).map₂ x)))) := by
  refine (inverse_raw_map t ht cs ((psiExtension t ht cs).map₂ x)).trans ?_
  exact congrArg (fun z : ZMod 2 => sign k z • _) (congrArg₂ (fun p q => p + q)
    (extension_inverseSign t ht cs f) (extension_inverseSign t ht cs g))

private theorem forward_raw_homogeneous {a b : Uqπ D Sc sy hc} {f g : a ⟶ b}
    {x : f ⟶ g} {r : ZMod 2} (hx : QPiTwoEnvelope.toHom x ∈ parity (R := k) _ _ r) :
    HEq (QPiTwoEnvelope.toHom ((psiInverseFunctor t ht cs).map₂
      ((psiExtension t ht cs).map₂ x))) (QPiTwoEnvelope.toHom x) := by
  have HH := forward_raw_double t ht cs hx
  -- The remaining correction is the established extension residual, not an assumed inverse.
  have eff := congrArg (fun z => z.obj.obj) (psiInverseFunctor_map_forward t ht cs f)
  have egg := congrArg (fun z => z.obj.obj) (psiInverseFunctor_map_forward t ht cs g)
  have HC := scalar_heq eff egg HH (sign k
    (psiInverseSign (SOp.unop ((psiExtension t ht cs).map f)) +
     psiInverseSign (SOp.unop ((psiExtension t ht cs).map g))))
  rw [extension_inverseSign, extension_inverseSign] at HC
  simp only [smul_smul, ← sign_add] at HC
  have E := correction_cancel f g r
  refine (heq_of_eq (forward_raw_correction t ht cs x)).trans (HC.trans (heq_of_eq ?_))
  rw [E]
  exact base_double_signed t ht cs _ _ hx

/-- Every shifted-envelope 2-morphism is fixed by the normalized actual composite.
The decomposition is the existing parity direct sum, not a homogeneity assumption. -/
theorem psiForwardInverseHom_apply {a b : Uqπ D Sc sy hc}
    (f g : a ⟶ b) (x : f ⟶ g) : psiForwardInverseHom t ht cs f g x = x := by
  induction x using Supercategory.induction_on (R := k) (C := a ⟶ b) with
  | zero => exact map_zero _
  | hom p x hx =>
    have H := forward_raw_homogeneous t ht cs
      (show QPiTwoEnvelope.toHom x ∈ parity (R := k) _ _ (p + (f.par + g.par)) from hx)
    exact eq_of_heq ((normalized_heq t ht cs x).trans
      (envelope_heq (psiInverseFunctor_map_forward t ht cs f)
        (psiInverseFunctor_map_forward t ht cs g) _ _ H))
  | add x y hx hy => rw [map_add, hx, hy]

/-- The actual forward-then-inverse map returns every envelope 2-morphism. -/
theorem psiForwardInverse_map₂ {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (x : f ⟶ g) :
    HEq ((psiInverseFunctor t ht cs).map₂ ((psiExtension t ht cs).map₂ x)) x :=
  (normalized_heq t ht cs x).symm.trans (heq_of_eq (psiForwardInverseHom_apply t ht cs f g x))

private theorem equalityIso_heq_refl {C : Type*} [Category C] {x y z : C}
    (h : x = y) (e : y = z) : HEq (eqToIso h) (Iso.refl z) := by
  cases e; cases h; rfl

/-- Proposition 9.4, forward-then-inverse: equality of all functor data,
including composition and identity comparisons. -/
theorem psiExtension_comp_inverse :
    (psiExtension (sy := sy) (hc := hc) t ht cs).comp (psiInverseFunctor t ht cs) =
      TwoSuperfunctor.id k (Uqπ D Sc sy hc) := by
  apply TwoEnvelope.twoSuperfunctor_ext
    (F := (psiExtension t ht cs).comp (psiInverseFunctor t ht cs))
    (G := TwoSuperfunctor.id k (Uqπ D Sc sy hc)) rfl
  · apply heq_of_eq
    funext a b f
    exact psiInverseFunctor_map_forward t ht cs f
  · apply Function.hfunext rfl; intro a a' ha; cases ha
    apply Function.hfunext rfl; intro b b' hb; cases hb
    apply Function.hfunext rfl; intro f f' hf; cases hf
    apply Function.hfunext rfl; intro g g' hg; cases hg
    apply Function.hfunext rfl; intro x x' hx; cases hx
    exact psiForwardInverse_map₂ t ht cs x
  · apply Function.hfunext rfl; intro a a' ha; cases ha
    apply Function.hfunext rfl; intro b b' hb; cases hb
    apply Function.hfunext rfl; intro c c' hc'; cases hc'
    apply Function.hfunext rfl; intro f f' hf; cases hf
    apply Function.hfunext rfl; intro g g' hg; cases hg
    rw [psiForwardInverse_mapComp]
    exact equalityIso_heq_refl _ (psiInverseFunctor_map_forward t ht cs (f ≫ g))
  · apply Function.hfunext rfl; intro a a' ha; cases ha
    rw [psiForwardInverse_mapId]
    exact equalityIso_heq_refl _ (psiInverseFunctor_map_forward t ht cs (𝟙 a))

/-- Reversing the composite exchanges the two involutive ψ parameter sets.
This is a linear-map calculation and does not assume either composite identity. -/
theorem psiReverseComposite_unsop_parameter
    {a b : TwoSOp k (Uqπ D Sc sy hc)} {f g : a ⟶ b} (y : f ⟶ g) :
    HEq
      (SOp.unsop ((psiExtension t ht cs).map₂
        ((psiInverseFunctor t ht cs).map₂ y)))
      ((psiInverseFunctor (-t) (psi_neg_sq ht)
          (psiInverseCScalars t ht cs)).map₂
        ((psiExtension (-t) (psi_neg_sq ht)
          (psiInverseCScalars t ht cs)).map₂ (SOp.unsop y))) := by
  have hF : psiExtension (sy := sy) (hc := hc) (- -t) (psi_neg_sq (psi_neg_sq ht))
      (psiInverseCScalars (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)) =
      psiExtension t ht cs := by
    simp only [neg_neg, psiInverseCScalars_involutive]
  have hmap (F G : TwoSuperfunctor k (Uqπ D Sc sy hc) (TwoSOp k (Uqπ D Sc sy hc)))
      (h : F = G) {a₀ b₀ : Uqπ D Sc sy hc} {f₀ g₀ : a₀ ⟶ b₀}
      (z : f₀ ⟶ g₀) (s : k) :
      HEq (s • SOp.unsop (F.map₂ z)) (s • SOp.unsop (G.map₂ z)) := by
    subst G
    rfl
  rw [psiInverseFunctor_map₂, psiInverseFunctor_map₂]
  rw [TwoSuperfunctor.map₂_smul, SOp.unsop_smul]
  simp only [psiExtension_map_eq_psiShift, psiInverseSign_psiShift]
  rw [add_comm (psiInverseSign (SOp.unop g))]
  exact (hmap _ _ hF _ _).symm

/-- Heterogeneous equality of opposite morphisms follows from equality after
`unsop`, with the endpoint equalities supplied explicitly. -/
theorem psiUnsop_heq_of_endpoints
    {a b : TwoSOp k (Uqπ D Sc sy hc)} {f' g' f g : a ⟶ b}
    (hf : f' = f) (hg : g' = g) (x : f' ⟶ g') (y : f ⟶ g)
    (h : HEq (SOp.unsop x) (SOp.unsop y)) : HEq x y := by
  subst f'
  subst g'
  exact heq_of_eq (SOp.hom_ext (eq_of_heq h))


/-- The inverse-then-forward map returns every opposite-envelope 2-morphism. -/
theorem psiInverseForward_map₂
    {a b : TwoSOp k (Uqπ D Sc sy hc)} {f g : a ⟶ b} (y : f ⟶ g) :
    HEq ((psiExtension t ht cs).map₂ ((psiInverseFunctor t ht cs).map₂ y)) y := by
  apply psiUnsop_heq_of_endpoints
    (psiInverseFunctor_map_reverse t ht cs f) (psiInverseFunctor_map_reverse t ht cs g)
  exact (psiReverseComposite_unsop_parameter t ht cs y).trans
    (psiForwardInverse_map₂ (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs) (SOp.unsop y))

/-- Proposition 9.4, inverse-then-forward: equality of all functor data,
including composition and identity comparisons. -/
theorem psiInverse_comp_extension :
    (psiInverseFunctor (sy := sy) (hc := hc) t ht cs).comp (psiExtension t ht cs) =
      TwoSuperfunctor.id k (TwoSOp k (Uqπ D Sc sy hc)) := by
  apply TwoEnvelope.twoSuperfunctor_ext
    (F := (psiInverseFunctor t ht cs).comp (psiExtension t ht cs))
    (G := TwoSuperfunctor.id k (TwoSOp k (Uqπ D Sc sy hc))) rfl
  · apply heq_of_eq
    funext a b f
    exact psiInverseFunctor_map_reverse t ht cs f
  · apply Function.hfunext rfl; intro a a' ha; cases ha
    apply Function.hfunext rfl; intro b b' hb; cases hb
    apply Function.hfunext rfl; intro f f' hf; cases hf
    apply Function.hfunext rfl; intro g g' hg; cases hg
    apply Function.hfunext rfl; intro x x' hx; cases hx
    exact psiInverseForward_map₂ t ht cs x
  · apply Function.hfunext rfl; intro a a' ha; cases ha
    apply Function.hfunext rfl; intro b b' hb; cases hb
    apply Function.hfunext rfl; intro c c' hc'; cases hc'
    apply Function.hfunext rfl; intro f f' hf; cases hf
    apply Function.hfunext rfl; intro g g' hg; cases hg
    rw [psiInverseForward_mapComp]
    exact equalityIso_heq_refl _ (psiInverseFunctor_map_reverse t ht cs (f ≫ g))
  · apply Function.hfunext rfl; intro a a' ha; cases ha
    rw [psiInverseForward_mapId]
    exact equalityIso_heq_refl _ (psiInverseFunctor_map_reverse t ht cs (𝟙 a))

end OddMath.SKM
