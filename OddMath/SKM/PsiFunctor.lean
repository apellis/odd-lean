/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PsiInversion

/-!
# Raw ψ diagrams and horizontal placement

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 9.4, the generator assignment in its proof. This module evaluates
primary-generator diagrams in the existing shifted super-opposite. The evaluation
uses its actual composition and whiskering, and preserves parity and degree.
`psiPrimaryRaw_append` proves vertical functoriality on the existing `SChain`
syntax; `psiPlace_comp` proves compatibility of horizontal placement with
vertical composition. The concrete consumer `psiPrimaryRaw_mixed_inversion`
identifies the raw mixed-crossing composite with the independently verified
image and applies both distinct-colour inverse equations.

`psiPlace_place` proves compatibility with nested signed contexts, and
`psiPrimaryRaw_whisk` identifies source-layer placement with actual target
whiskering. The contextual equal-colour quadratic relation is checked directly.
The seven-shape linear evaluation is developed in `PsiDescent`; full quotient
descent and the strict graded functor remain separate obligations. No relation-
preservation hypothesis is used to assert a functor here. This slice works over
a purely even commutative ring; the quadratic and mixed-inverse consumers require
`t² = -1`, without the field assumption of §9.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-- Concatenation in the normalized word coordinates used for ψ. -/
theorem psiWordAt_comp_eq (ν ξ μ : X) (s t : List (Letter I))
    (hs : wt D ξ s = ν) (ht : wt D μ t = ξ) :
    psiWordAt (Sc := Sc) ν ξ s hs ≫ psiWordAt ξ μ t ht =
      psiWordAt ν μ (s ++ t) (by rw [wt_append, ht, hs]) := by
  apply Presentation.Bicat.Hom.ext
  apply Obj.ext
  · change wt D ξ s = wt D μ (s ++ t)
    rw [wt_append, ht]
  · change wd D ξ s ++ wd D μ t = wd D μ (s ++ t)
    rw [wd_append, ht]

/-- The word comparisons are equalities, not additional coherence data. -/
theorem psiAt_comp_eq (ν ξ μ : X) (s t : List (Letter I))
    (hs : wt D ξ s = ν) (ht : wt D μ t = ξ) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ≫ psiAt ξ μ t ht =
      psiAt ν μ (s ++ t) (by rw [wt_append, ht, hs]) := by
  rw [← psiMap_comp, psiWordAt_comp_eq]

/-- Equal signed words determine equal ψ images at fixed weights. -/
theorem psiAt_congr (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (h : s = r) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs = psiAt ν μ r hr := by
  cases h
  rfl

private theorem transport_parity {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {a b a' b' : C} (ha : a = a') (hb : b' = b) {p : ZMod 2}
    {η : a' ⟶ b'} (hη : η ∈ parity (R := k) _ _ p) :
    eqToHom ha ≫ η ≫ eqToHom hb ∈ parity (R := k) _ _ p := by
  subst a' b'
  simpa using hη

private theorem transport_degree {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] [GradedSupercategory k C]
    {a b a' b' : C} (ha : a = a') (hb : b' = b) {n : ℤ}
    {η : a' ⟶ b'} (hη : η ∈ GradedSupercategory.degree (R := k) _ _ n) :
    eqToHom ha ≫ η ≫ eqToHom hb ∈ GradedSupercategory.degree (R := k) _ _ n := by
  subst a' b'
  simpa using hη

/-- The single-dot image preserves parity. -/
theorem psiDot_mem_parity (t : k) (μ : X) (i : I) :
    psiDot (Sc := Sc) (sy := sy) (hc := hc) t μ i ∈ parity (R := k) _ _ (D.parity i) := by
  change psiCoeff t (1 * D.parity i) • cl D Sc μ [up i] [up i] (dotsL [] i [] 1) ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (D.parity i + (0 + 0))
  apply Submodule.smul_mem
  unfold cl
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_parity_mkD]
    simp
  · exact Submodule.zero_mem _

/-- The single-dot image preserves integer degree. -/
theorem psiDot_mem_degree (t : k) (μ : X) (i : I) :
    psiDot (Sc := Sc) (sy := sy) (hc := hc) t μ i ∈
      GradedSupercategory.degree (R := k) _ _ (2 * sy.d i) := by
  change psiCoeff t (1 * D.parity i) • cl D Sc μ [up i] [up i] (dotsL [] i [] 1) ∈
    (pres D Sc).homDeg (gdeg D sy) _ _ (2 * sy.d i + (0 - 0))
  apply Submodule.smul_mem
  unfold cl
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_gdeg_mkD]
    simp
  · exact Submodule.zero_mem _

/-- The empty signed word maps to the identity 1-morphism. -/
theorem psiAt_nil_eq (μ : X) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) μ μ [] rfl = 𝟙 (psiObj ⟨μ⟩) := by
  exact psiMap_id ⟨μ⟩

private theorem psiEq_underlying {ν μ : X}
    {a b : psiObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ⟨ν⟩ ⟶ psiObj ⟨μ⟩} (h : a = b) :
    SOp.unsop (eqToHom h) = eqToHom
      (congrArg (fun x => (pres D Sc).obj (SOp.unop x).obj.obj.obj) h.symm) := by
  cases h
  rfl

private theorem psiAt_leftUnitor (ν μ : X) (s : List (Letter I)) (hs : wt D μ s = ν)
    (h : 𝟙 (psiObj ⟨ν⟩) ≫ psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs = psiAt ν μ s hs) :
    (leftUnitor (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs)).hom = eqToHom h := by
  apply SOp.hom_ext
  rw [psiEq_underlying]
  rfl

private theorem psiAt_leftUnitor_inv (ν μ : X) (s : List (Letter I)) (hs : wt D μ s = ν)
    (h : 𝟙 (psiObj ⟨ν⟩) ≫ psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs = psiAt ν μ s hs) :
    (leftUnitor (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs)).inv = eqToHom h.symm := by
  apply SOp.hom_ext
  rw [psiEq_underlying]
  rfl

private theorem psiAt_rightUnitor (ν μ : X) (s : List (Letter I)) (hs : wt D μ s = ν)
    (h : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ≫ 𝟙 (psiObj ⟨μ⟩) = psiAt ν μ s hs) :
    (rightUnitor (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs)).hom = eqToHom h := by
  apply SOp.hom_ext
  rw [psiEq_underlying]
  rfl

private theorem psiAt_rightUnitor_inv (ν μ : X) (s : List (Letter I)) (hs : wt D μ s = ν)
    (h : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ≫ 𝟙 (psiObj ⟨μ⟩) = psiAt ν μ s hs) :
    (rightUnitor (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs)).inv = eqToHom h.symm := by
  apply SOp.hom_ext
  rw [psiEq_underlying]
  rfl

private theorem psiAt_id_comp (ν μ : X) (s : List (Letter I)) (hs : wt D μ s = ν) :
    𝟙 (psiObj ⟨ν⟩) ≫ psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs = psiAt ν μ s hs := by
  rw [← psiAt_nil_eq, psiAt_comp_eq]
  rfl

private theorem psiAt_comp_id (ν μ : X) (s : List (Letter I)) (hs : wt D μ s = ν) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ≫ 𝟙 (psiObj ⟨μ⟩) = psiAt ν μ s hs := by
  rw [← psiAt_nil_eq, psiAt_comp_eq]
  exact psiAt_congr ν μ _ _ (List.append_nil s)

/-- An empty left context contributes only the explicit word comparison. -/
theorem psiWhiskerLeft_nil (ν μ : X) (s r : List (Letter I))
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (η : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ psiAt ν μ r hr) :
    psiWhiskerLeft ν ν μ [] s r rfl hs hr η =
      eqToHom (psiAt_congr ν μ _ hs (by simp)) ≫ η ≫
        eqToHom (psiAt_congr ν μ hr _ (by simp)) := by
  change eqToHom _ ≫ (𝟙 _ ◁ η) ≫ eqToHom _ = _
  rw [TwoSupercategory.id_whiskerLeft (R := k)]
  rw [psiAt_leftUnitor ν μ s hs (psiAt_id_comp ν μ s hs),
    psiAt_leftUnitor_inv ν μ r hr (psiAt_id_comp ν μ r hr)]
  simp [Category.assoc]

/-- An empty right context contributes only the explicit word comparison. -/
theorem psiWhiskerRight_nil (ν μ : X) (s r : List (Letter I))
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (η : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ psiAt ν μ r hr) :
    psiWhiskerRight ν μ s r [] hs hr η =
      eqToHom (psiAt_congr ν μ _ hs (by simp)) ≫ η ≫
        eqToHom (psiAt_congr ν μ hr _ (by simp)) := by
  change eqToHom _ ≫ (η ▷ 𝟙 _) ≫ eqToHom _ = _
  rw [TwoSupercategory.whiskerRight_id (R := k)]
  rw [psiAt_rightUnitor ν μ s hs (psiAt_comp_id ν μ s hs),
    psiAt_rightUnitor_inv ν μ r hr (psiAt_comp_id ν μ r hr)]
  simp [Category.assoc]

/-- The four generators appearing in the printed assignment, before adjoining
inverse-matrix entries to the presentation. -/
def Shape.IsPrimary : Shape I → Prop
  | .dot _ | .cross _ _ | .cup _ | .cap _ => True
  | .lcross _ _ | .dcup _ _ | .dcap _ _ => False

/-- The printed assignment on a primary generator, at arbitrary fixed boundaries. -/
def psiPrimaryGen (t : k) (cs : CScalars Sc) (ν μ : X) (g : Shape I)
    (hg : g.IsPrimary) (h : wt D μ g.dom = ν) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ g.dom h ⟶
      psiAt ν μ g.cod ((g.wt_dom_eq_wt_cod D μ).symm.trans h) := by
  cases g with
  | dot i => subst ν; exact psiDot t μ i
  | cross i j => exact psiCross t ν μ i j h
  | cup i => subst ν; exact psiCup cs μ i
  | cap i =>
    have hn : ν = μ := by simpa [Shape.dom, wt_cons, sh] using h.symm
    cases hn
    exact psiCap cs ν i
  | lcross i j => exact False.elim hg
  | dcup i n => exact False.elim hg
  | dcap i n => exact False.elim hg

/-- Parity preservation for every primary generator, with no relation assumption. -/
theorem psiPrimaryGen_mem_parity (t : k) (cs : CScalars Sc) (ν μ : X) (g : Shape I)
    (hg : g.IsPrimary) (h : wt D μ g.dom = ν) :
    psiPrimaryGen (sy := sy) (hc := hc) t cs ν μ g hg h ∈ parity (R := k) _ _ (g.parity D) := by
  cases g with
  | dot i => subst ν; exact psiDot_mem_parity t μ i
  | cross i j => exact psiCross_mem_parity t ν μ i j h
  | cup i => subst ν; exact psiCup_mem_parity cs μ i
  | cap i =>
    have hn : ν = μ := by simpa [Shape.dom, wt_cons, sh] using h.symm
    cases hn
    exact psiCap_mem_parity cs ν i
  | lcross i j => exact False.elim hg
  | dcup i n => exact False.elim hg
  | dcap i n => exact False.elim hg

/-- Integer degree preservation for every primary generator. -/
theorem psiPrimaryGen_mem_degree (t : k) (cs : CScalars Sc) (ν μ : X) (g : Shape I)
    (hg : g.IsPrimary) (h : wt D μ g.dom = ν) :
    psiPrimaryGen (sy := sy) (hc := hc) t cs ν μ g hg h ∈
      GradedSupercategory.degree (R := k) _ _ (gdeg D sy (g, μ)) := by
  cases g with
  | dot i => subst ν; exact psiDot_mem_degree t μ i
  | cross i j => exact psiCross_mem_degree t ν μ i j h
  | cup i => subst ν; exact psiCup_mem_degree cs μ i
  | cap i =>
    have hn : ν = μ := by simpa [Shape.dom, wt_cons, sh] using h.symm
    cases hn
    exact psiCap_mem_degree cs ν i
  | lcross i j => exact False.elim hg
  | dcup i n => exact False.elim hg
  | dcap i n => exact False.elim hg

/-- Place a ψ image between arbitrary signed words. All signs come from the
whiskerings of the existing envelope and super-opposite, not a scalar surrogate. -/
def psiPlace (Ω ν ξ μ : X) (u v : List (Letter I)) {s r : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν)
    (η : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ psiAt ν ξ r hr) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) Ω μ (u ++ s ++ v)
        (by rw [wt_append, wt_append, hv, hs, hu]) ⟶
      psiAt Ω μ (u ++ r ++ v) (by rw [wt_append, wt_append, hv, hr, hu]) :=
  by
  subst ξ
  exact eqToHom (psiAt_congr Ω μ _ _ (show u ++ s ++ v = u ++ (s ++ v) ++ [] by simp)) ≫
    psiWhiskerLeft Ω ν μ u (s ++ v) (r ++ v) hu
      (by rw [wt_append, hs]) (by rw [wt_append, hr])
      (psiWhiskerRight ν μ s r v hs hr η) ≫
    eqToHom (psiAt_congr Ω μ _ _ (show u ++ r ++ v = u ++ (r ++ v) ++ [] by simp)).symm

/-- Placement preserves parity. -/
theorem psiPlace_mem_parity (Ω ν ξ μ : X) (u v : List (Letter I)) {s r : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν)
    {p : ZMod 2} {η : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ psiAt ν ξ r hr}
    (hη : η ∈ parity (R := k) _ _ p) :
    psiPlace Ω ν ξ μ u v hu hv hs hr η ∈ parity (R := k) _ _ p :=
  by
  subst ξ
  unfold psiPlace
  apply transport_parity
  exact psiWhiskerLeft_mem Ω ν μ u (s ++ v) (r ++ v) hu
    (by rw [wt_append, hs]) (by rw [wt_append, hr])
    (psiWhiskerRight_mem ν μ s r v hs hr hη)

/-- Placement preserves integer degree. -/
theorem psiPlace_mem_degree (Ω ν ξ μ : X) (u v : List (Letter I)) {s r : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν)
    {n : ℤ} {η : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ psiAt ν ξ r hr}
    (hη : η ∈ GradedSupercategory.degree (R := k) _ _ n) :
    psiPlace Ω ν ξ μ u v hu hv hs hr η ∈ GradedSupercategory.degree (R := k) _ _ n :=
  by
  subst ξ
  unfold psiPlace psiWhiskerLeft psiWhiskerRight
  apply transport_degree
  apply transport_degree
  apply GradedTwoSupercategory.whiskerLeft_mem_degree
  apply transport_degree
  exact GradedTwoSupercategory.whiskerRight_mem_degree _ hη

/-- Placement respects vertical composition in the actual target. -/
theorem psiPlace_comp (Ω ν ξ μ : X) (u v : List (Letter I)) {s r q : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ)
    (hs : wt D ξ s = ν) (hr : wt D ξ r = ν) (hq : wt D ξ q = ν)
    (η : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ psiAt ν ξ r hr)
    (θ : psiAt ν ξ r hr ⟶ psiAt ν ξ q hq) :
    psiPlace Ω ν ξ μ u v hu hv hs hq (η ≫ θ) =
      psiPlace Ω ν ξ μ u v hu hv hs hr η ≫ psiPlace Ω ν ξ μ u v hu hv hr hq θ := by
  subst ξ
  simp [psiPlace, psiWhiskerLeft, psiWhiskerRight, TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.comp_whiskerRight (R := k), TwoSupercategory.whiskerLeft_eqToHom k, Category.assoc]

/-- The raw image of a primary layer, with its complete horizontal context. -/
def psiPrimaryLayer (t : k) (cs : CScalars Sc) (ν μ : X) (u : List (Letter I))
    (g : Shape I) (v : List (Letter I)) (hg : g.IsPrimary)
    (h : wt D μ (u ++ g.dom ++ v) = ν) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ (u ++ g.dom ++ v) h ⟶
      psiAt ν μ (u ++ g.cod ++ v) (by
        simpa only [wt_append, ← g.wt_dom_eq_wt_cod D] using h) :=
  psiPlace ν (wt D (wt D μ v) g.dom) (wt D μ v) μ u v
    (by simpa only [wt_append] using h) rfl rfl (g.wt_dom_eq_wt_cod D _).symm
    (psiPrimaryGen t cs _ _ g hg rfl)

/-- Every primary layer retains the parity of its generator. -/
theorem psiPrimaryLayer_mem_parity (t : k) (cs : CScalars Sc) (ν μ : X)
    (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) (hg : g.IsPrimary)
    (h : wt D μ (u ++ g.dom ++ v) = ν) :
    psiPrimaryLayer (sy := sy) (hc := hc) t cs ν μ u g v hg h ∈
      parity (R := k) _ _ (g.parity D) :=
  psiPlace_mem_parity _ _ _ _ _ _ _ _ _ _ (psiPrimaryGen_mem_parity t cs _ _ g hg rfl)

/-- Every primary layer retains the degree at the region immediately to its right. -/
theorem psiPrimaryLayer_mem_degree (t : k) (cs : CScalars Sc) (ν μ : X)
    (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) (hg : g.IsPrimary)
    (h : wt D μ (u ++ g.dom ++ v) = ν) :
    psiPrimaryLayer (sy := sy) (hc := hc) t cs ν μ u g v hg h ∈
      GradedSupercategory.degree (R := k) _ _ (gdeg D sy (g, wt D μ v)) :=
  psiPlace_mem_degree _ _ _ _ _ _ _ _ _ _ (psiPrimaryGen_mem_degree t cs _ _ g hg rfl)

/-- All layers use the four primary generators. This is a predicate on the
existing presentation syntax, not a replacement category. -/
def PrimaryLayers (L : List (LayerData I)) : Prop := ∀ x ∈ L, x.2.1.IsPrimary

/-- Evaluate a primary diagram by its assigned layers in the target. The explicit
boundary and chain proofs are those of the existing normal-form presentation. -/
def psiPrimaryRaw (t : k) (cs : CScalars Sc) (ν μ : X) (L : List (LayerData I))
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (h : SChain s L r) (hp : PrimaryLayers L) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ psiAt ν μ r hr := by
  match L with
  | [] => exact eqToHom (psiAt_congr ν μ hs hr h)
  | x :: L =>
    have hx : wt D μ (x.1 ++ x.2.1.dom ++ x.2.2) = ν := (congrArg (wt D μ) h.1).symm.trans hs
    exact eqToHom (psiAt_congr ν μ hs hx h.1) ≫
      psiPrimaryLayer t cs ν μ x.1 x.2.1 x.2.2 (hp x (by simp)) hx ≫
      psiPrimaryRaw t cs ν μ L (by
        simpa only [wt_append, ← x.2.1.wt_dom_eq_wt_cod D] using hx) hr h.2
        (fun y hy => hp y (List.mem_cons_of_mem _ hy))

/-- Vertical concatenation of raw diagrams is evaluated as composition in the
super-opposite, including its Koszul sign. -/
theorem psiPrimaryRaw_append (t : k) (cs : CScalars Sc) (ν μ : X)
    (L M : List (LayerData I)) {s r q : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hq : wt D μ q = ν)
    (hL : SChain s L r) (hM : SChain r M q) (hp : PrimaryLayers L) (hpm : PrimaryLayers M) :
    psiPrimaryRaw (sy := sy) (hc := hc) t cs ν μ (L ++ M) hs hq (hL.append hM)
      (fun x hx => (List.mem_append.mp hx).elim (hp x) (hpm x)) =
      psiPrimaryRaw t cs ν μ L hs hr hL hp ≫ psiPrimaryRaw t cs ν μ M hr hq hM hpm := by
  induction L generalizing s with
  | nil => cases hL; simp [psiPrimaryRaw]
  | cons x L ih =>
    obtain ⟨rfl, hL⟩ := hL
    simp only [List.cons_append, psiPrimaryRaw, eqToHom_refl, Category.id_comp, Category.assoc]
    congr 1
    exact ih _ hL _

/-- **Proposition 9.4, raw parity check:** every primary diagram has the parity
of its source diagram. No quotient relation is assumed. -/
theorem psiPrimaryRaw_mem_parity (t : k) (cs : CScalars Sc) (ν μ : X)
    (L : List (LayerData I)) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (h : SChain s L r) (hp : PrimaryLayers L) :
    psiPrimaryRaw (sy := sy) (hc := hc) t cs ν μ L hs hr h hp ∈
      parity (R := k) _ _ (parsum D L) := by
  induction L generalizing s with
  | nil => cases h; exact id_mem _
  | cons x L ih =>
    obtain ⟨rfl, h⟩ := h
    simp only [psiPrimaryRaw, eqToHom_refl, Category.id_comp]
    exact comp_mem (psiPrimaryLayer_mem_parity t cs ν μ x.1 x.2.1 x.2.2 _ hs)
      (ih _ h _)

/-- **Proposition 9.4, raw degree check:** every primary diagram retains its
integer degree from the table after (1.31). -/
theorem psiPrimaryRaw_mem_degree (t : k) (cs : CScalars Sc) (ν μ : X)
    (L : List (LayerData I)) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (h : SChain s L r) (hp : PrimaryLayers L) :
    psiPrimaryRaw (sy := sy) (hc := hc) t cs ν μ L hs hr h hp ∈
      GradedSupercategory.degree (R := k) _ _ (gsum D sy μ L) := by
  induction L generalizing s with
  | nil => cases h; exact GradedSupercategory.id_mem_degree _
  | cons x L ih =>
    obtain ⟨rfl, h⟩ := h
    simp only [psiPrimaryRaw, eqToHom_refl, Category.id_comp]
    exact GradedSupercategory.comp_mem_degree
      (psiPrimaryLayer_mem_degree t cs ν μ x.1 x.2.1 x.2.2 _ hs) (ih _ h _)

/-- The defining mixed-crossing word consists entirely of primary layers. -/
theorem primaryLayers_sigmaL (i j : I) : PrimaryLayers (sigmaL i j) := by
  intro x hx
  simp only [sigmaL, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> trivial

private theorem psiPrimaryCapPlace (t : k) (cs : CScalars Sc) (Ω ν μ : X)
    (u : List (Letter I)) (i : I) (h : wt D μ (Shape.cap i).dom = ν) (hu : wt D ν u = Ω) :
    psiPlace (sy := sy) (hc := hc) Ω ν μ μ u [] hu rfl h
      (((Shape.cap i).wt_dom_eq_wt_cod D μ).symm.trans h)
      (psiPrimaryGen t cs ν μ (.cap i) trivial h) =
    psiWhiskerLeft Ω μ μ u [up i, dn i] []
      (by have hn : ν = μ := by simpa [Shape.dom, wt, sh] using h.symm
          simpa only [hn] using hu)
      (by simp [wt, sh]) rfl (psiCap cs μ i) := by
  have hn : ν = μ := by simpa [Shape.dom, wt, sh] using h.symm
  cases hn
  simp [psiPlace, psiPrimaryGen, psiWhiskerRight_nil, Shape.dom, Shape.cod]

/-- The raw evaluation of the mixed-crossing word is the actual three-factor
composite already used by the inversion proof. -/
theorem psiPrimaryRaw_sigma_composite (t : k) (cs : CScalars Sc) (μ : X) (i j : I) :
    psiPrimaryRaw (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ (sigmaL i j)
      rfl ((sChain_sigmaL i j).wt_eq D μ) (sChain_sigmaL i j) (primaryLayers_sigmaL i j) =
      psiSigmaCup cs μ i j ≫ psiSigmaMiddle t μ i j ≫ psiSigmaCap cs μ i j := by
  have h₁ : psiPrimaryLayer (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ
      [] (.cup i) [up j, dn i] trivial rfl = psiSigmaCup cs μ i j := by
    simp [psiPrimaryLayer, psiPlace, psiPrimaryGen, psiSigmaCup,
      Shape.dom, Shape.cod, psiWhiskerLeft_nil]
  have h₂ : psiPrimaryLayer (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ
      [dn i] (.cross i j) [dn i] trivial (by simp [Shape.dom, wt, sh]) =
      psiSigmaMiddle t μ i j := by
    simp [psiPrimaryLayer, psiPlace, psiPrimaryGen, psiSigmaMiddle, Shape.dom, Shape.cod]
  have h₃ : psiPrimaryLayer (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ
      [dn i, up j] (.cap i) [] trivial (by simp [Shape.dom, wt, sh]; abel) =
      psiSigmaCap cs μ i j :=
    psiPrimaryCapPlace t cs _ _ μ [dn i, up j] i rfl _
  have h := congrArg₂ (fun f g => f ≫ g) h₁ (congrArg₂ (fun f g => f ≫ g) h₂ h₃)
  simpa only [psiPrimaryRaw, sigmaL, eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- The primary raw evaluator agrees with the verified mixed-crossing image. -/
theorem psiPrimaryRaw_sigma_eq (t : k) (cs : CScalars Sc) (μ : X) (i j : I) :
    psiPrimaryRaw (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ (sigmaL i j)
      rfl ((sChain_sigmaL i j).wt_eq D μ) (sChain_sigmaL i j) (primaryLayers_sigmaL i j) =
      psiSigma t μ i j := by
  exact (psiPrimaryRaw_sigma_composite t cs μ i j).trans (psiSigma_eq_composite cs t μ i j)

/-- **Proposition 9.4, mixed inversion:** the actual raw assignment to the
primary mixed-crossing composite has the proved inverse for distinct colours. -/
theorem psiPrimaryRaw_mixed_inversion (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i j : I) (hij : i ≠ j) :
    let f := psiPrimaryRaw (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ (sigmaL i j)
      rfl ((sChain_sigmaL i j).wt_eq D μ) (sChain_sigmaL i j) (primaryLayers_sigmaL i j)
    f ≫ psiLCross t μ i j = 𝟙 _ ∧ psiLCross t μ i j ≫ f = 𝟙 _ := by
  dsimp only
  rw [psiPrimaryRaw_sigma_eq]
  exact ⟨psi_invNe₁ t ht μ i j hij, psi_invNe₂ t ht μ i j hij⟩

/-- Concrete downstream use: the raw assignment to the defining mixed-crossing
composite is homogeneous in its required parity and degree zero. -/
theorem psiPrimaryRaw_sigma_homogeneous (t : k) (cs : CScalars Sc) (μ : X) (i j : I) :
    let f := psiPrimaryRaw (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ (sigmaL i j)
      rfl ((sChain_sigmaL i j).wt_eq D μ) (sChain_sigmaL i j) (primaryLayers_sigmaL i j)
    f ∈ parity (R := k) _ _ (D.parity i * D.parity j) ∧
      f ∈ GradedSupercategory.degree (R := k) _ _ 0 := by
  constructor
  · simpa [parsum, sigmaL, Shape.parity] using
      psiPrimaryRaw_mem_parity (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ (sigmaL i j)
        rfl ((sChain_sigmaL i j).wt_eq D μ) (sChain_sigmaL i j) (primaryLayers_sigmaL i j)
  · simpa only [gsum_sigmaL] using
      psiPrimaryRaw_mem_degree (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ (sigmaL i j)
        rfl ((sChain_sigmaL i j).wt_eq D μ) (sChain_sigmaL i j) (primaryLayers_sigmaL i j)


/-- Horizontal placement is linear on the actual target hom module. -/
def psiPlaceLinear (Ω ν ξ μ : X) (u v : List (Letter I)) {s r : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν) :
    (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ psiAt ν ξ r hr) →ₗ[k]
      (psiAt (Sc := Sc) (sy := sy) (hc := hc) Ω μ (u ++ s ++ v)
          (by rw [wt_append, wt_append, hv, hs, hu]) ⟶
        psiAt Ω μ (u ++ r ++ v) (by rw [wt_append, wt_append, hv, hr, hu])) where
  toFun := psiPlace Ω ν ξ μ u v hu hv hs hr
  map_add' η θ := by
    subst ξ
    simp [psiPlace, psiWhiskerLeft, psiWhiskerRight,
      TwoSupercategory.whiskerLeft_add (R := k), TwoSupercategory.add_whiskerRight (R := k),
      Preadditive.add_comp, Preadditive.comp_add]
  map_smul' a η := by
    subst ξ
    simp [psiPlace, psiWhiskerLeft, psiWhiskerRight,
      TwoSupercategory.whiskerLeft_smul (R := k), TwoSupercategory.smul_whiskerRight (R := k),
      Linear.smul_comp, Linear.comp_smul]

/-- Placing an identity gives the identity on the concatenated word. -/
theorem psiPlace_id (Ω ν ξ μ : X) (u v s : List (Letter I))
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) :
    psiPlace (Sc := Sc) (sy := sy) (hc := hc) Ω ν ξ μ u v hu hv hs hs (𝟙 _) = 𝟙 _ := by
  subst ξ
  simp [psiPlace, psiWhiskerLeft, psiWhiskerRight,
    TwoSupercategory.whiskerLeft_id (R := k), TwoSupercategory.id_whiskerRight (R := k)]

/-- The equal-colour quadratic relation holds for the raw evaluator in any signed
horizontal context. This evaluates the two source layers, not merely a target equation. -/
theorem psiPrimaryRaw_quadEq (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (ν μ : X) (u v : List (Letter I)) (i : I)
    (h : wt D μ (u ++ [up i, up i] ++ v) = ν) :
    psiPrimaryRaw (sy := sy) (hc := hc) t cs ν μ
      (crossL u i i v ++ crossL u i i v) h h
      (by simp [crossL, Shape.dom, Shape.cod])
      (by intro x hx; simp only [crossL, List.singleton_append, List.mem_cons,
            List.not_mem_nil, or_false, or_self] at hx; subst x; trivial) = 0 := by
  simp only [crossL, List.singleton_append, psiPrimaryRaw, eqToHom_refl, Category.id_comp,
    Category.comp_id]

  unfold psiPrimaryLayer
  rw [← psiPlace_comp]
  change psiPlaceLinear ν (wt D (wt D μ v) [up i, up i]) (wt D μ v) μ u v
    (by simpa only [wt_append] using h) rfl rfl rfl
    (psiCross t _ _ i i rfl ≫ psiCross t _ _ i i rfl) = 0
  rw [psiCross_sq t ht, map_zero]


private theorem psiAt_associator {Ω ν ξ μ : X}
    (a : psiObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ⟨Ω⟩ ⟶ psiObj ⟨ν⟩)
    (b : psiObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ⟨ν⟩ ⟶ psiObj ⟨ξ⟩)
    (c : psiObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ⟨ξ⟩ ⟶ psiObj ⟨μ⟩)
    (h : (a ≫ b) ≫ c = a ≫ b ≫ c) :
    (associator a b c).hom = eqToHom h := by
  apply SOp.hom_ext
  rw [psiEq_underlying]
  rfl



private theorem psiAt_assoc_eq (Ω ν ξ μ : X) (u v w : List (Letter I))
    (hu : wt D ν u = Ω) (hv : wt D ξ v = ν) (hw : wt D μ w = ξ) :
    (psiAt (Sc := Sc) (sy := sy) (hc := hc) Ω ν u hu ≫ psiAt ν ξ v hv) ≫ psiAt ξ μ w hw =
      psiAt Ω ν u hu ≫ psiAt ν ξ v hv ≫ psiAt ξ μ w hw := by
  rw [psiAt_comp_eq, psiAt_comp_eq, psiAt_comp_eq, psiAt_comp_eq]
  exact psiAt_congr Ω μ _ _ (List.append_assoc u v w)

private theorem psiAt_associator_inv {Ω ν ξ μ : X}
    (a : psiObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ⟨Ω⟩ ⟶ psiObj ⟨ν⟩)
    (b : psiObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ⟨ν⟩ ⟶ psiObj ⟨ξ⟩)
    (c : psiObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ⟨ξ⟩ ⟶ psiObj ⟨μ⟩)
    (h : (a ≫ b) ≫ c = a ≫ b ≫ c) :
    (associator a b c).inv = eqToHom h.symm := by
  apply SOp.hom_ext
  rw [psiEq_underlying]
  rfl

private theorem psiWhiskerLeft_congr {Ω ν μ : X}
    {a b : psiObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ⟨Ω⟩ ⟶ psiObj ⟨ν⟩}
    (h : a = b) {s r : psiObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ⟨ν⟩ ⟶ psiObj ⟨μ⟩}
    (η : s ⟶ r) :
    b ◁ η = eqToHom (congrArg (· ≫ s) h.symm) ≫ (a ◁ η) ≫
      eqToHom (congrArg (· ≫ r) h) := by
  cases h
  simp

/-- Normalized left whiskering respects concatenation of signed contexts. -/
theorem psiWhiskerLeft_append (Ω ν ξ μ : X) (u v s r : List (Letter I))
    (hu : wt D ν u = Ω) (hv : wt D ξ v = ν)
    (hs : wt D μ s = ξ) (hr : wt D μ r = ξ)
    (η : psiAt (Sc := Sc) (sy := sy) (hc := hc) ξ μ s hs ⟶ psiAt ξ μ r hr) :
    psiWhiskerLeft Ω ν μ u (v ++ s ++ []) (v ++ r ++ []) hu
        (by simp only [List.append_nil, wt_append, hs, hv])
        (by simp only [List.append_nil, wt_append, hr, hv])
        (psiWhiskerLeft ν ξ μ v s r hv hs hr η) =
      eqToHom (psiAt_congr Ω μ _ _ (by simp [List.append_assoc])) ≫
        psiWhiskerLeft Ω ξ μ (u ++ v) s r (by rw [wt_append, hv, hu]) hs hr η ≫
        eqToHom (psiAt_congr Ω μ _ _ (by simp [List.append_assoc])) := by
  unfold psiWhiskerLeft
  simp only [TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.whiskerLeft_eqToHom k, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]
  rw [psiWhiskerLeft_congr (psiAt_comp_eq Ω ν ξ u v hu hv) η]
  rw [TwoSupercategory.comp_whiskerLeft (R := k)]
  rw [psiAt_associator _ _ _ (psiAt_assoc_eq Ω ν ξ μ u v s hu hv hs),
    psiAt_associator_inv _ _ _ (psiAt_assoc_eq Ω ν ξ μ u v r hu hv hr)]
  simp [Category.assoc]


private theorem psiWhiskerRight_congr {Ω ν μ : X}
    {a b : psiObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ⟨ν⟩ ⟶ psiObj ⟨μ⟩}
    (h : a = b) {s r : psiObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ⟨Ω⟩ ⟶ psiObj ⟨ν⟩}
    (η : s ⟶ r) :
    η ▷ b = eqToHom (congrArg (s ≫ ·) h.symm) ≫ (η ▷ a) ≫
      eqToHom (congrArg (r ≫ ·) h) := by
  cases h
  simp

/-- Placement in explicit weight coordinates, without eliminating a region equality. -/
theorem psiPlace_eq (Ω ν ξ μ : X) (u v : List (Letter I)) {s r : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν)
    (η : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ psiAt ν ξ r hr) :
    psiPlace Ω ν ξ μ u v hu hv hs hr η =
      eqToHom (by
        rw [psiAt_comp_eq, psiAt_comp_eq]
        exact psiAt_congr Ω μ _ _ (List.append_assoc u s v)) ≫
      (psiAt Ω ν u hu ◁ (η ▷ psiAt ξ μ v hv)) ≫
      eqToHom (by
        rw [psiAt_comp_eq, psiAt_comp_eq]
        exact psiAt_congr Ω μ _ _ (List.append_assoc u r v).symm) := by
  subst ξ
  simp [psiPlace, psiWhiskerLeft, psiWhiskerRight,
    TwoSupercategory.whiskerLeft_comp (R := k), TwoSupercategory.whiskerLeft_eqToHom k,
    Category.assoc]

private theorem psiAssoc {Ω ν ξ μ : X}
    (a : psiObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ⟨Ω⟩ ⟶ psiObj ⟨ν⟩)
    (b : psiObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ⟨ν⟩ ⟶ psiObj ⟨ξ⟩)
    (c : psiObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ⟨ξ⟩ ⟶ psiObj ⟨μ⟩) :
    (a ≫ b) ≫ c = a ≫ b ≫ c := by
  apply congrArg SOp.mk
  apply congrArg₂ Envelope.mk
  · exact add_assoc _ _ _
  · apply congrArg₂ QEnvelope.mk
    · exact add_assoc _ _ _
    · apply Presentation.Bicat.Hom.ext
      apply Obj.ext
      · rfl
      · exact List.append_assoc _ _ _

/-- Iterated placement agrees with concatenating both signed contexts. -/
theorem psiPlace_place (Δ Ω ν ξ ζ μ : X) (a b u v : List (Letter I))
    {s r : List (Letter I)} (ha : wt D Ω a = Δ) (hb : wt D μ b = ζ)
    (hu : wt D ν u = Ω) (hv : wt D ζ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν)
    (η : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ psiAt ν ξ r hr) :
    psiPlace Δ Ω ζ μ a b ha hb
        (by rw [wt_append, wt_append, hv, hs, hu])
        (by rw [wt_append, wt_append, hv, hr, hu])
        (psiPlace Ω ν ξ ζ u v hu hv hs hr η) =
      eqToHom (psiAt_congr Δ μ _ _ (by simp [List.append_assoc])) ≫
        psiPlace Δ ν ξ μ (a ++ u) (v ++ b)
          (by rw [wt_append, hu, ha]) (by rw [wt_append, hb, hv]) hs hr η ≫
        eqToHom (psiAt_congr Δ μ _ _ (by simp [List.append_assoc])) := by
  subst ζ ξ
  simp only [psiPlace_eq,
    TwoSupercategory.whiskerLeft_comp (R := k), TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.whiskerLeft_eqToHom k, TwoSupercategory.eqToHom_whiskerRight k,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  rw [psiWhiskerLeft_congr (psiAt_comp_eq Δ Ω ν a u ha hu)]
  rw [psiWhiskerRight_congr (psiAt_comp_eq (wt D (wt D μ b) v) (wt D μ b) μ v b rfl rfl)]
  rw [TwoSupercategory.comp_whiskerLeft (R := k),
    TwoSupercategory.whiskerRight_comp (R := k), TwoSupercategory.whisker_assoc (R := k)]
  simp only [psiAt_associator _ _ _ (psiAssoc _ _ _),
    psiAt_associator_inv _ _ _ (psiAssoc _ _ _),
    TwoSupercategory.whiskerLeft_comp (R := k), TwoSupercategory.whiskerLeft_eqToHom k,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans]


/-- Primary layers stay primary after horizontal placement. -/
theorem PrimaryLayers.whisk {L : List (LayerData I)} (hp : PrimaryLayers L)
    (u v : List (Letter I)) : PrimaryLayers (L.map (whL u v)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact hp y hy

private theorem psiPrimaryRaw_reindex (t : k) (cs : CScalars Sc) (ν μ : X)
    (L : List (LayerData I)) {s r s' r' : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hs' : wt D μ s' = ν) (hr' : wt D μ r' = ν)
    (h : SChain s L r) (h' : SChain s' L r') (hp : PrimaryLayers L)
    (e : s = s') (f : r = r') :
    psiPrimaryRaw (sy := sy) (hc := hc) t cs ν μ L hs hr h hp =
      eqToHom (psiAt_congr ν μ hs hs' e) ≫ psiPrimaryRaw t cs ν μ L hs' hr' h' hp ≫
        eqToHom (psiAt_congr ν μ hr' hr f.symm) := by
  cases e; cases f
  simp

private theorem psiPrimaryLayer_eq (t : k) (cs : CScalars Sc) (ν ξ μ : X)
    (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) (hg : g.IsPrimary)
    (h : wt D μ (u ++ g.dom ++ v) = ν) (hv : wt D μ v = ξ) :
    psiPrimaryLayer (sy := sy) (hc := hc) t cs ν μ u g v hg h =
      psiPlace ν (wt D ξ g.dom) ξ μ u v
        (by rw [← hv]; simpa only [wt_append] using h) hv rfl
        (g.wt_dom_eq_wt_cod D ξ).symm (psiPrimaryGen t cs _ ξ g hg rfl) := by
  subst ξ
  rfl

/-- The raw primary evaluator commutes with placement of every source layer. -/
theorem psiPrimaryRaw_whisk (t : k) (cs : CScalars Sc) (Ω ν ξ μ : X)
    (u v : List (Letter I)) (L : List (LayerData I)) {s r : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν)
    (hL : SChain s L r) (hp : PrimaryLayers L) :
    psiPrimaryRaw (sy := sy) (hc := hc) t cs Ω μ (L.map (whL u v))
        (by rw [wt_append, wt_append, hv, hs, hu])
        (by rw [wt_append, wt_append, hv, hr, hu]) (hL.whisk u v) (hp.whisk u v) =
      psiPlace Ω ν ξ μ u v hu hv hs hr (psiPrimaryRaw t cs ν ξ L hs hr hL hp) := by
  induction L generalizing s with
  | nil =>
    cases hL
    simp only [List.map_nil, psiPrimaryRaw, psiPlace_id, eqToHom_refl]
  | cons x L ih =>
    obtain ⟨rfl, hL⟩ := hL
    simp only [List.map_cons, psiPrimaryRaw, eqToHom_refl, Category.id_comp,
      psiPlace_comp]
    rw [← ih]
    unfold psiPrimaryLayer
    rw [psiPlace_place]
    simp only [whL, Category.assoc]
    congr 1
    apply congrArg₂ (· ≫ ·)
    · exact psiPrimaryLayer_eq t cs Ω (wt D ξ x.2.2) μ (u ++ x.1) x.2.1 (x.2.2 ++ v)
        _ _ (by rw [wt_append, hv])
    · simpa only [eqToHom_refl, Category.comp_id] using
        psiPrimaryRaw_reindex t cs Ω μ (L.map (whL u v)) _ _ _ _ _ (hL.whisk u v) _
          (show (u ++ x.1) ++ x.2.1.cod ++ (x.2.2 ++ v) =
            u ++ (x.1 ++ x.2.1.cod ++ x.2.2) ++ v by simp [List.append_assoc]) rfl

end OddMath.SKM
