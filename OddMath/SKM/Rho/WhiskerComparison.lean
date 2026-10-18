import OddMath.SKM.Rho.LayerComparison

/-!
# Whisker Comparison for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoUpwardKernel
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords RhoEvaluator
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

private theorem left_unit {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : 𝟙 _ ≫ a = a) : (leftUnitor a).hom = eqToHom h := by
  rw [eq_underlying]
  rfl
private theorem left_unit_inv {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : 𝟙 _ ≫ a = a) : (leftUnitor a).inv = eqToHom h.symm := by
  rw [eq_underlying]
  rfl
private theorem right_unit {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : a ≫ 𝟙 _ = a) : (rightUnitor a).hom = eqToHom h := by
  rw [eq_underlying]
  rfl
private theorem right_unit_inv {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : a ≫ 𝟙 _ = a) : (rightUnitor a).inv = eqToHom h.symm := by
  rw [eq_underlying]
  rfl

private theorem id_comp_eq {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ) : 𝟙 _ ≫ a = a := by
  apply Envelope.ext
  · exact add_zero _
  · apply QEnvelope.ext
    · exact add_zero _
    · apply Presentation.Bicat.Hom.ext
      apply Obj.ext
      · rfl
      · exact List.append_nil _
private theorem comp_id_eq {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ) : a ≫ 𝟙 _ = a := by
  apply Envelope.ext
  · exact zero_add _
  · apply QEnvelope.ext
    · exact zero_add _
    · apply Presentation.Bicat.Hom.ext
      apply Obj.ext
      · exact a.obj.obj.start_eq.symm
      · rfl

theorem place_right_heq (ν ξ μ : X) (v : List (Letter I)) {s r : List (Letter I)}
    (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν)
    (η : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ rhoAt ν ξ r hr) :
    HEq (place ν ν ξ μ [] v rfl hv hs hr η) (η ▷ rhoAt ξ μ v hv) := by
  apply (place_heq ν ν ξ μ [] v rfl hv hs hr η).trans
  change HEq (𝟙 _ ◁ (η ▷ rhoAt ξ μ v hv)) _
  rw [TwoSupercategory.id_whiskerLeft (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    left_unit _ (id_comp_eq _), left_unit_inv _ (id_comp_eq _)]
  exact transport_heq _ _ _

theorem place_left_heq (Ω ν μ : X) (u : List (Letter I)) {s r : List (Letter I)}
    (hu : wt D ν u = Ω) (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (η : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ rhoAt ν μ r hr) :
    HEq (place Ω ν μ μ u [] hu rfl hs hr η) (rhoAt Ω ν u hu ◁ η) := by
  unfold place
  change HEq (eqToHom _ ≫ (rhoAt Ω ν u hu ◁ (η ▷ 𝟙 _)) ≫ eqToHom _) _
  rw [TwoSupercategory.whiskerRight_id (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    right_unit _ (comp_id_eq _), right_unit_inv _ (comp_id_eq _)]
  simp only [TwoSupercategory.whiskerLeft_comp (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    TwoSupercategory.whiskerLeft_eqToHom k, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  exact transport_heq _ _ _

theorem whiskerRight_transport {ν ξ μ : X}
    {a b a' b' : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj ξ}
    {c c' : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ξ ⟶ rhoObj μ}
    (ha : a = a') (hb : b' = b) (hc' : c = c') (η : a' ⟶ b') :
    HEq ((eqToHom ha ≫ η ≫ eqToHom hb) ▷ c) (η ▷ c') := by
  subst a' b' c'
  simp

theorem whiskerLeft_transport {Ω ν μ : X}
    {a b a' b' : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ}
    {c c' : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) Ω ⟶ rhoObj ν}
    (ha : a = a') (hb : b' = b) (hc' : c = c') (η : a' ⟶ b') :
    HEq (c ◁ (eqToHom ha ≫ η ≫ eqToHom hb)) (c' ◁ η) := by
  subst a' b' c'
  simp

theorem right_layer (t : k) (μ : X) (g : Shape I) (v : List I) :
    HEq (forget (Sc := Sc) (sy := sy) (hc := hc) (wt D (wt D μ (ups v)) g.dom) μ
      (s := g.dom ++ ups v) (r := g.cod ++ ups v)
      (by rw [wt_append]) (by rw [wt_append, ← g.wt_dom_eq_wt_cod D])
      (rhoRaw t _ μ [([], g, ups v)] _ _ ⟨rfl, rfl⟩))
      (RhoGenerators.normal (Sc := Sc) (sy := sy) (hc := hc) t
        (wt D (wt D μ (ups v)) g.dom) (wt D μ (ups v)) g rfl ▷
          rhoUpAt (wt D μ (ups v)) μ v rfl) := by
  apply (forget_heq _ _ _ _ _).trans
  erw [rhoRaw_layer t _ _ _ μ [] g (ups v) rfl rfl rfl]
  apply (place_right_heq _ _ _ _ rfl rfl _ _).trans
  exact whiskerRight_transport _ _ (rhoMap_upAt _ _ v rfl) _

theorem left_layer (t : k) (μ : X) (u : List I) (g : Shape I) :
    HEq (forget (Sc := Sc) (sy := sy) (hc := hc) (wt D (wt D μ g.dom) (ups u)) μ
      (s := ups u ++ g.dom ++ []) (r := ups u ++ g.cod ++ [])
      (by rw [List.append_nil, wt_append])
      (by rw [List.append_nil, wt_append, ← g.wt_dom_eq_wt_cod D])
      (rhoRaw t _ μ [(ups u, g, [])] _ _ ⟨rfl, rfl⟩))
      (rhoUpAt (wt D (wt D μ g.dom) (ups u)) (wt D μ g.dom) u rfl ◁
        RhoGenerators.normal (Sc := Sc) (sy := sy) (hc := hc) t
          (wt D μ g.dom) μ g rfl) := by
  apply (forget_heq _ _ _ _ _).trans
  erw [rhoRaw_layer t _ _ _ μ (ups u) g [] rfl rfl rfl]
  apply (place_left_heq _ _ _ _ rfl rfl _ _).trans
  exact whiskerLeft_transport _ _ (rhoMap_upAt _ _ u rfl) _

end OddMath.SKM.RhoUpwardKernel
