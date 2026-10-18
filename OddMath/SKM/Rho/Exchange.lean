import OddMath.SKM.Rho.Gradings
import StringDiagrams.InterchangeLayers

/-!
# Exchange for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoEvaluator
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

private theorem eq_underlying {ν μ : X}
    {a b : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ} (h : a = b) :
    eqToHom h = eqToHom (congrArg (fun x => (pres D Sc).obj x.obj.obj.obj) h) := by
  cases h
  rfl

private theorem rev_leftUnitor {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : 𝟙 _ ≫ a = a) : (leftUnitor a).hom = eqToHom h := by
  rw [eq_underlying]
  rfl

private theorem rev_leftUnitor_inv {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : 𝟙 _ ≫ a = a) : (leftUnitor a).inv = eqToHom h.symm := by
  rw [eq_underlying]
  rfl

private theorem rev_rightUnitor {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : a ≫ 𝟙 _ = a) : (rightUnitor a).hom = eqToHom h := by
  rw [eq_underlying]
  rfl

private theorem rev_rightUnitor_inv {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : a ≫ 𝟙 _ = a) : (rightUnitor a).inv = eqToHom h.symm := by
  rw [eq_underlying]
  rfl

private theorem at_id_comp (ν μ : X) (s : List (Letter I)) (hs : wt D μ s = ν) :
    𝟙 _ ≫ rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs = rhoAt ν μ s hs := by
  rw [← at_nil, at_comp]
  rfl

private theorem at_comp_id (ν μ : X) (s : List (Letter I)) (hs : wt D μ s = ν) :
    rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ≫ 𝟙 _ = rhoAt ν μ s hs := by
  rw [← at_nil, at_comp]
  exact at_congr ν μ _ _ (List.append_nil s)

private theorem rhoRaw_reindex (t : k) (ν μ : X)
    (L : List (LayerData I)) {s r s' r' : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hs' : wt D μ s' = ν) (hr' : wt D μ r' = ν)
    (h : SChain s L r) (h' : SChain s' L r')
    (e : s = s') (f : r = r') :
    rhoRaw (sy := sy) (hc := hc) t ν μ L hs hr h =
      eqToHom (at_congr ν μ hs hs' e) ≫ rhoRaw t ν μ L hs' hr' h' ≫
        eqToHom (at_congr ν μ hr' hr f.symm) := by
  cases e; cases f
  simp

private theorem rhoRaw_whisk_left (t : k) (ν ξ μ : X)
    (s : List (Letter I)) (L : List (LayerData I)) {a b : List (Letter I)}
    (hs : wt D ξ s = ν) (ha : wt D μ a = ξ) (hb : wt D μ b = ξ) (hL : SChain a L b) :
    rhoRaw (sy := sy) (hc := hc) t ν μ (L.map (whL s []))
      (by rw [wt_append, ha, hs]) (by rw [wt_append, hb, hs])
      (show SChain (s ++ a) (L.map (whL s [])) (s ++ b) by
        simpa only [List.append_nil] using hL.whisk s []) =
      eqToHom (at_comp ν ξ μ s a hs ha).symm ≫
        (rhoAt ν ξ s hs ◁ rhoRaw t ξ μ L ha hb hL) ≫
          eqToHom (at_comp ν ξ μ s b hs hb) := by
  rw [rhoRaw_reindex t ν μ _ _ _
    (by simp only [List.append_nil, wt_append, ha, hs])
    (by simp only [List.append_nil, wt_append, hb, hs]) _ (hL.whisk s [])
    (List.append_nil _).symm (List.append_nil _).symm]
  rw [rhoRaw_whisk t ν ξ μ μ s [] L hs rfl ha hb hL]
  unfold place
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  change eqToHom _ ≫ (rhoAt ν ξ s hs ◁ (rhoRaw t ξ μ L ha hb hL ▷ 𝟙 _)) ≫ eqToHom _ = _
  rw [TwoSupercategory.whiskerRight_id (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    rev_rightUnitor _ (at_comp_id ξ μ a ha), rev_rightUnitor_inv _ (at_comp_id ξ μ b hb)]
  simp only [TwoSupercategory.whiskerLeft_comp (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    TwoSupercategory.whiskerLeft_eqToHom k, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

private theorem rhoRaw_whisk_right (t : k) (ν ξ μ : X)
    (L : List (LayerData I)) (a : List (Letter I)) {s r : List (Letter I)}
    (hs : wt D ξ s = ν) (hr : wt D ξ r = ν) (ha : wt D μ a = ξ) (hL : SChain s L r) :
    rhoRaw (sy := sy) (hc := hc) t ν μ (L.map (whL [] a))
      (by rw [wt_append, ha, hs]) (by rw [wt_append, ha, hr])
      (show SChain (s ++ a) (L.map (whL [] a)) (r ++ a) by
        simpa only [List.nil_append] using hL.whisk [] a) =
      eqToHom (at_comp ν ξ μ s a hs ha).symm ≫
        (rhoRaw t ν ξ L hs hr hL ▷ rhoAt ξ μ a ha) ≫
          eqToHom (at_comp ν ξ μ r a hr ha) := by
  subst ξ
  have he := rhoRaw_whisk (sy := sy) (hc := hc) t ν ν (wt D μ a) μ [] a L rfl rfl hs hr hL
  unfold place at he
  change _ = eqToHom _ ≫ (𝟙 _ ◁ (rhoRaw t ν (wt D μ a) L hs hr hL ▷ rhoAt (wt D μ a) μ a rfl)) ≫ eqToHom _ at he
  rw [TwoSupercategory.id_whiskerLeft (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    rev_leftUnitor _ (by rw [at_comp]; exact at_id_comp ν μ (s ++ a) _),
    rev_leftUnitor_inv _ (by rw [at_comp]; exact at_id_comp ν μ (r ++ a) _)] at he
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, List.nil_append] using he

theorem rhoRaw_exchange (t : k) (ν ξ μ : X)
    (L M : List (LayerData I)) {s r a b : List (Letter I)}
    (hs : wt D ξ s = ν) (hr : wt D ξ r = ν) (ha : wt D μ a = ξ) (hb : wt D μ b = ξ)
    (hL : SChain s L r) (hM : SChain a M b) :
    rhoRaw (sy := sy) (hc := hc) t ν μ (L.map (whL [] a) ++ M.map (whL r []))
      (by rw [wt_append, ha, hs]) (by rw [wt_append, hb, hr])
      ((show SChain (s ++ a) (L.map (whL [] a)) (r ++ a) by
        simpa only [List.nil_append] using hL.whisk [] a).append
       (show SChain (r ++ a) (M.map (whL r [])) (r ++ b) by
        simpa only [List.append_nil] using hM.whisk r [])) =
    koszulSign (parsum D L) (parsum D M) •
      rhoRaw t ν μ (M.map (whL s []) ++ L.map (whL [] b))
        (by rw [wt_append, ha, hs]) (by rw [wt_append, hb, hr])
        ((show SChain (s ++ a) (M.map (whL s [])) (s ++ b) by
          simpa only [List.append_nil] using hM.whisk s []).append
         (show SChain (s ++ b) (L.map (whL [] b)) (r ++ b) by
          simpa only [List.nil_append] using hL.whisk [] b)) := by
  rw [rhoRaw_append t ν μ (L.map (whL [] a)) (M.map (whL r []))
    (r := r ++ a) _ (by rw [wt_append, ha, hr]) _
    (by simpa only [List.nil_append] using hL.whisk [] a)
    (by simpa only [List.append_nil] using hM.whisk r []),
    rhoRaw_append t ν μ (M.map (whL s [])) (L.map (whL [] b))
      (r := s ++ b) _ (by rw [wt_append, hb, hs]) _
      (by simpa only [List.append_nil] using hM.whisk s [])
      (by simpa only [List.nil_append] using hL.whisk [] b)]
  rw [rhoRaw_whisk_right t ν ξ μ L a hs hr ha hL,
    rhoRaw_whisk_left t ν ξ μ r M hr ha hb hM,
    rhoRaw_whisk_left t ν ξ μ s M hs ha hb hM,
    rhoRaw_whisk_right t ν ξ μ L b hs hr hb hL]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have he := TwoSupercategory.super_interchange (R := k) (B := TwoSRev k (Uqπ D Sc sy hc))
    (rhoRaw_mem_parity (sy := sy) (hc := hc) t ν ξ L hs hr hL)
    (rhoRaw_mem_parity (sy := sy) (hc := hc) t ξ μ M ha hb hM)
  have H := congrArg (fun f => eqToHom (at_comp ν ξ μ s a hs ha).symm ≫ f ≫
    eqToHom (at_comp ν ξ μ r b hr hb)) he
  simpa only [Category.assoc, Linear.smul_comp, Linear.comp_smul] using H

private theorem rho_koszul_cast (p q : ZMod 2) :
    (koszulSign p q : k) = zsign k (p * q) := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;> simp [koszulSign, zsign]

theorem rhoRaw_swap₀ (t : k) (ν μ : X) (m : List (Letter I))
    (g h : Shape I) (hs : wt D μ (g.dom ++ m ++ h.dom) = ν)
    (hr : wt D μ (g.cod ++ m ++ h.cod) = ν) :
    rhoRaw (sy := sy) (hc := hc) t ν μ
      [([], g, m ++ h.dom), (g.cod ++ m, h, [])] hs hr
      (by simp only [sChain_cons, sChain_nil, List.nil_append, List.append_nil, List.append_assoc,
        true_and]) =
    zsign k (g.parity D * h.parity D) • rhoRaw t ν μ
      [(g.dom ++ m, h, []), ([], g, m ++ h.cod)] hs hr
      (by simp only [sChain_cons, sChain_nil, List.nil_append, List.append_nil, List.append_assoc,
        true_and]) := by
  have hL : SChain (g.dom ++ m) [([], g, m)] (g.cod ++ m) := ⟨rfl, rfl⟩
  have hM : SChain h.dom [([], h, [])] h.cod := by simp
  have he := rhoRaw_exchange (sy := sy) (hc := hc) t ν (wt D μ h.dom) μ
    [([], g, m)] [([], h, [])]
    (by simpa only [wt_append] using hs)
    ((hL.wt_eq D (wt D μ h.dom)).trans (by simpa only [wt_append] using hs))
    rfl (h.wt_dom_eq_wt_cod D μ).symm hL hM
  rw [← Int.cast_smul_eq_zsmul k, rho_koszul_cast] at he
  simpa only [List.map_cons, List.map_nil, List.singleton_append, List.nil_append,
    List.append_nil, whL, parsum, List.map, List.sum_cons, List.sum_nil, add_zero] using he

end OddMath.SKM.RhoEvaluator
