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

The auxiliary inversion generators, linearization, full contextual relation
descent and the strict graded functor remain separate obligations; no
relation-preservation hypothesis is used to assert a functor here. The raw
slice works over a purely even commutative ring; only the mixed inverse consumer
requires `t² = -1`, and it does not need the field assumption of §9.
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

private theorem psiAt_congr (ν μ : X) {s r : List (Letter I)}
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

end OddMath.SKM
