import OddMath.SKM.Rho.WordComparison

/-!
# Upward Words for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoUpwardKernel
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords RhoEvaluator RhoCoefficients
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

def upEval (t : k) (ν μ : X) (L : List (LayerData I)) {s r : List I}
    (hs : wt D μ (ups s) = ν) (hr : wt D μ (ups r) = ν) (h : SChain (ups s) L (ups r)) :
    rhoUpAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ rhoUpAt ν μ r hr :=
  eqToHom (rhoMap_upAt ν μ s hs).symm ≫ rhoRaw t ν μ L hs hr h ≫ eqToHom (rhoMap_upAt ν μ r hr)

theorem upEval_heq_eval (t : k) (ν μ : X) (L : List (LayerData I)) {s r : List I}
    (hs : wt D μ (ups s) = ν) (hr : wt D μ (ups r) = ν) (h : SChain (ups s) L (ups r)) :
    HEq (upEval (Sc := Sc) (sy := sy) (hc := hc) t ν μ L hs hr h)
      (eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ L hs hr h) :=
  (transport_heq _ _ _).trans (forget_heq ν μ hs hr _).symm

theorem rhoRaw_upEval (t : k) (ν μ : X) (L : List (LayerData I)) {s r : List I}
    (hs : wt D μ (ups s) = ν) (hr : wt D μ (ups r) = ν) (h : SChain (ups s) L (ups r)) :
    rhoRaw (Sc := Sc) (sy := sy) (hc := hc) t ν μ L hs hr h =
      eqToHom (rhoMap_upAt ν μ s hs) ≫ upEval t ν μ L hs hr h ≫ eqToHom (rhoMap_upAt ν μ r hr).symm := by
  simp [upEval, Category.assoc]

theorem eval_whisk_left (t : k) (Ω ν μ : X) (u s r : List I) (L : List (LayerData I))
    (hu : wt D ν (ups u) = Ω) (hs : wt D μ (ups s) = ν) (hr : wt D μ (ups r) = ν)
    (h : SChain (ups s) L (ups r)) :
    HEq (eval (Sc := Sc) (sy := sy) (hc := hc) t Ω μ (L.map (whL (ups u) []))
      (s := ups u ++ ups s ++ []) (r := ups u ++ ups r ++ [])
      (by rw [List.append_nil, wt_append, hs]; exact hu)
      (by rw [List.append_nil, wt_append, hr]; exact hu) (h.wh _ _ rfl rfl))
      (rhoUpAt Ω ν u hu ◁ upEval (Sc := Sc) (sy := sy) (hc := hc) t ν μ L hs hr h) := by
  apply (forget_heq _ _ _ _ _).trans
  erw [rhoRaw_whisk t Ω ν μ μ (ups u) [] L hu rfl hs hr h]
  apply (place_left_heq _ _ _ _ hu hs hr _).trans
  rw [rhoRaw_upEval t ν μ L hs hr h]
  exact whiskerLeft_transport _ _ (rhoMap_upAt Ω ν u hu) _

theorem eval_whisk_right (t : k) (ν ξ μ : X) (s r v : List I) (L : List (LayerData I))
    (hv : wt D μ (ups v) = ξ) (hs : wt D ξ (ups s) = ν) (hr : wt D ξ (ups r) = ν)
    (h : SChain (ups s) L (ups r)) :
    HEq (eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (L.map (whL [] (ups v)))
      (s := [] ++ ups s ++ ups v) (r := [] ++ ups r ++ ups v)
      (by rw [List.nil_append, wt_append, hv]; exact hs)
      (by rw [List.nil_append, wt_append, hv]; exact hr) (h.wh _ _ rfl rfl))
      (upEval (Sc := Sc) (sy := sy) (hc := hc) t ν ξ L hs hr h ▷ rhoUpAt ξ μ v hv) := by
  apply (forget_heq _ _ _ _ _).trans
  erw [rhoRaw_whisk t ν ν ξ μ [] (ups v) L rfl hv hs hr h]
  apply (place_right_heq _ _ _ _ hv hs hr _).trans
  rw [rhoRaw_upEval t ν ξ L hs hr h]
  exact whiskerRight_transport _ _ (rhoMap_upAt ξ μ v hv) _

theorem dot_middle3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ [up i,up j,up a] = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ [([up i], .dot j, [up a])] h h ⟨rfl,rfl⟩ =
      psiCoeff t (D.parity j) • cl D Sc ν [dn a,dn j,dn i] [dn a,dn j,dn i]
        ((ddotL j).map (whL [dn a] [dn i])) := by
  subst ν
  have H := eval_whisk_left (Sc := Sc) (sy := sy) (hc := hc) t
    (wt D μ [up i,up j,up a]) (wt D μ [up j,up a]) μ [i] [j,a] [j,a]
    [([], .dot j, [up a])] rfl rfl rfl ⟨rfl,rfl⟩
  have E : upEval (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up j,up a]) μ
      [([], .dot j, [up a])] (s := [j,a]) (r := [j,a]) rfl rfl ⟨rfl,rfl⟩ =
      rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up j,up a]) μ j a rfl :=
    eq_of_heq ((upEval_heq_eval t _ μ _ rfl rfl _).trans (heq_of_eq (eval_dot_left t _ μ j a rfl)))
  rw [E] at H
  exact eq_of_heq (H.trans (dotMiddle3_whisker t μ i j a))

theorem upEval_comp (t : k) (ν μ : X) (L M : List (LayerData I)) {s r q : List I}
    (hs : wt D μ (ups s) = ν) (hr : wt D μ (ups r) = ν) (hq : wt D μ (ups q) = ν)
    (hL : SChain (ups s) L (ups r)) (hM : SChain (ups r) M (ups q)) :
    upEval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (L ++ M) hs hq (hL.append hM) =
      upEval t ν μ L hs hr hL ≫ upEval t ν μ M hr hq hM := by
  unfold upEval
  rw [rhoRaw_append t ν μ L M hs hr hq hL hM]
  simp [Category.assoc]

theorem upEval_id (t : k) (ν μ : X) (s : List I) (hs : wt D μ (ups s) = ν) :
    upEval (Sc := Sc) (sy := sy) (hc := hc) t ν μ [] hs hs rfl = 𝟙 _ := by
  simp [upEval, rhoRaw]

theorem upEval_cross (t : k) (ν μ : X) (i j : I) (h : wt D μ (ups [i,j]) = ν)
    (h' : wt D μ (ups [j,i]) = ν) :
    upEval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (crossL [] i j []) h h' ⟨rfl,rfl⟩ =
      correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h :=
  eq_of_heq ((upEval_heq_eval t ν μ _ h h' _).trans (heq_of_eq (eval_cross t ν μ i j h h')))

theorem upEval_dot (t : k) (ν μ : X) (i : I) (h : wt D μ (ups [i]) = ν) :
    upEval (Sc := Sc) (sy := sy) (hc := hc) t ν μ [([], .dot i, [])] h h ⟨rfl,rfl⟩ =
      RhoGenerators.normal (Sc := Sc) (sy := sy) (hc := hc) t ν μ (.dot i) h := by
  apply eq_of_heq
  apply (upEval_heq_eval t ν μ _ h h _).trans
  apply heq_of_eq
  unfold eval
  erw [rhoRaw_gen]
  exact forget_generator t ν μ (.dot i) h

end OddMath.SKM.RhoUpwardKernel
