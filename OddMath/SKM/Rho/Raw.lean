import OddMath.SKM.Rho.Coherence

/-!
# Raw for ρ

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

def rhoLayer (t : k) (ν μ : X)
    (u : List (Letter I)) (g : Shape I) (v : List (Letter I))
    (h : wt D μ (u ++ g.dom ++ v) = ν) :
    rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ (u ++ g.dom ++ v) h ⟶
      rhoAt ν μ (u ++ g.cod ++ v)
        (by simpa only [wt_append, ← g.wt_dom_eq_wt_cod D] using h) :=
  place ν (wt D (wt D μ v) g.dom) (wt D μ v) μ u v
    (by simpa only [wt_append] using h) rfl rfl (g.wt_dom_eq_wt_cod D _).symm
    (RhoGenerators.generator t _ _ g rfl)

def rhoRaw (t : k) (ν μ : X) :
    (L : List (LayerData I)) → {s r : List (Letter I)} →
    (hs : wt D μ s = ν) → (hr : wt D μ r = ν) → SChain s L r →
    (rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ rhoAt ν μ r hr)
  | [], _, _, hs, hr, h => eqToHom (at_congr ν μ hs hr h)
  | x :: L, _, _, hs, hr, h =>
      eqToHom (at_congr ν μ hs _ h.1) ≫
        rhoLayer t ν μ x.1 x.2.1 x.2.2 (h.1 ▸ hs) ≫
        rhoRaw t ν μ L _ hr h.2

theorem rhoRaw_append (t : k) (ν μ : X)
    (L M : List (LayerData I)) {s r q : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hq : wt D μ q = ν)
    (hL : SChain s L r) (hM : SChain r M q) :
    rhoRaw (sy := sy) (hc := hc) t ν μ (L ++ M) hs hq (hL.append hM) =
      rhoRaw t ν μ L hs hr hL ≫ rhoRaw t ν μ M hr hq hM := by
  induction L generalizing s with
  | nil => cases hL; simp [rhoRaw]
  | cons x L ih =>
    obtain ⟨rfl, hL⟩ := hL
    simp only [List.cons_append, rhoRaw, eqToHom_refl, Category.id_comp, Category.assoc]
    congr 1
    exact ih _ hL

theorem rhoRaw_mem_parity (t : k) (ν μ : X)
    (L : List (LayerData I)) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (h : SChain s L r) :
    rhoRaw (sy := sy) (hc := hc) t ν μ L hs hr h ∈ parity (R := k) _ _ (parsum D L) := by
  induction L generalizing s with
  | nil => cases h; exact id_mem _
  | cons x L ih =>
    obtain ⟨rfl, h⟩ := h
    simp only [rhoRaw, eqToHom_refl, Category.id_comp]
    exact comp_mem (place_parity _ _ _ _ _ _ _ _ _ _ (RhoGenerators.generator_parity t _ _ _ rfl))
      (ih _ h)

theorem rhoRaw_mem_degree (t : k) (ν μ : X)
    (L : List (LayerData I)) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (h : SChain s L r) :
    rhoRaw (sy := sy) (hc := hc) t ν μ L hs hr h ∈
      GradedSupercategory.degree (R := k) _ _ (gsum D sy μ L) := by
  induction L generalizing s with
  | nil => cases h; exact GradedSupercategory.id_mem_degree _
  | cons x L ih =>
    obtain ⟨rfl, h⟩ := h
    simp only [rhoRaw, eqToHom_refl, Category.id_comp]
    exact GradedSupercategory.comp_mem_degree
      (place_degree _ _ _ _ _ _ _ _ _ _ (RhoGenerators.generator_degree t _ _ _ rfl)) (ih _ h)

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

private theorem rhoLayer_eq (t : k) (ν ξ μ : X)
    (u : List (Letter I)) (g : Shape I) (v : List (Letter I))
    (h : wt D μ (u ++ g.dom ++ v) = ν) (hv : wt D μ v = ξ) :
    rhoLayer (sy := sy) (hc := hc) t ν μ u g v h =
      place ν (wt D ξ g.dom) ξ μ u v
        (by rw [← hv]; simpa only [wt_append] using h) hv rfl
        (g.wt_dom_eq_wt_cod D ξ).symm (RhoGenerators.generator t _ ξ g rfl) := by
  subst ξ
  rfl

theorem rhoRaw_whisk (t : k) (Ω ν ξ μ : X)
    (u v : List (Letter I)) (L : List (LayerData I)) {s r : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν)
    (hL : SChain s L r) :
    rhoRaw (sy := sy) (hc := hc) t Ω μ (L.map (whL u v))
        (by rw [wt_append, wt_append, hv, hs, hu])
        (by rw [wt_append, wt_append, hv, hr, hu]) (hL.whisk u v) =
      place Ω ν ξ μ u v hu hv hs hr (rhoRaw t ν ξ L hs hr hL) := by
  induction L generalizing s with
  | nil =>
    cases hL
    simp only [List.map_nil, rhoRaw, eqToHom_refl]
    exact (place_id Ω ν ξ μ u v r hu hv hs).symm
  | cons x L ih =>
    obtain ⟨rfl, hL⟩ := hL
    simp only [List.map_cons, rhoRaw, eqToHom_refl, Category.id_comp]
    rw [place_comp (sy := sy) (hc := hc) Ω ν ξ μ u v hu hv hs _ hr]
    rw [← ih]
    unfold rhoLayer
    rw [place_place]
    simp only [whL, Category.assoc]
    congr 1
    apply congrArg₂ (· ≫ ·)
    · exact rhoLayer_eq t Ω (wt D ξ x.2.2) μ (u ++ x.1) x.2.1 (x.2.2 ++ v)
        _ (by rw [wt_append, hv])
    · simpa only [eqToHom_refl, Category.comp_id] using
        rhoRaw_reindex t Ω μ (L.map (whL u v)) _ _ _ _ _ (hL.whisk u v)
          (show (u ++ x.1) ++ x.2.1.cod ++ (x.2.2 ++ v) =
            u ++ (x.1 ++ x.2.1.cod ++ x.2.2) ++ v by simp [List.append_assoc]) rfl

end OddMath.SKM.RhoEvaluator
