/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PsiFunctor
import OddMath.SKM.PsiInversionSame

/-!
# Evaluation of the seven ψ generators on the linear presentation

Brundan–Ellis, *Super Kac–Moody 2-categories*, Proposition 9.4. The primary
assignments and the independently verified inverse entries are evaluated on the
existing diagram syntax. `psiRaw_whisk` proves horizontal compatibility for all
seven shapes, and `psiLin_comp` proves vertical composition on the original free
linear diagram module. `psiLin_quadEq` checks an actual defining relation. Full
quotient-kernel inclusion and the strict graded functor are not asserted here;
no relation-preservation hypothesis is part of the evaluator.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-- The actual seven generator images, including the adjoined inverse entries. -/
def psiGen (t : k) (cs : CScalars Sc) (ν μ : X) (g : Shape I)
    (h : wt D μ g.dom = ν) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ g.dom h ⟶
      psiAt ν μ g.cod ((g.wt_dom_eq_wt_cod D μ).symm.trans h) :=
  match g with
  | .dot i => psiPrimaryGen t cs ν μ (.dot i) trivial h
  | .cross i j => psiPrimaryGen t cs ν μ (.cross i j) trivial h
  | .cup i => psiPrimaryGen t cs ν μ (.cup i) trivial h
  | .cap i => psiPrimaryGen t cs ν μ (.cap i) trivial h
  | .lcross i j => psiRebase (((Shape.lcross i j).wt_dom_eq_wt_cod D μ).symm.trans h)
      (psiLCross t μ i j)
  | .dcup i r => psiRebase h (psiDiamondCup cs t μ i r)
  | .dcap i r => psiRebase (((Shape.dcap i r).wt_dom_eq_wt_cod D μ).symm.trans h)
      (psiDiamondCap cs t μ i r)

/-- The seven-shape assignment extends the printed four primary assignments literally. -/
theorem psiGen_eq_primary (t : k) (cs : CScalars Sc) (ν μ : X) (g : Shape I)
    (hg : g.IsPrimary) (h : wt D μ g.dom = ν) :
    psiGen (sy := sy) (hc := hc) t cs ν μ g h = psiPrimaryGen t cs ν μ g hg h := by
  cases g with
  | dot i | cross i j | cup i | cap i => rfl
  | lcross i j | dcup i r | dcap i r => exact False.elim hg

/-- All seven generator images have the prescribed source parity. -/
theorem psiGen_mem_parity (t : k) (cs : CScalars Sc) (ν μ : X) (g : Shape I)
    (h : wt D μ g.dom = ν) :
    psiGen (sy := sy) (hc := hc) t cs ν μ g h ∈ parity (R := k) _ _ (g.parity D) := by
  cases g with
  | dot i => exact psiPrimaryGen_mem_parity t cs ν μ (.dot i) trivial h
  | cross i j => exact psiPrimaryGen_mem_parity t cs ν μ (.cross i j) trivial h
  | cup i => exact psiPrimaryGen_mem_parity t cs ν μ (.cup i) trivial h
  | cap i => exact psiPrimaryGen_mem_parity t cs ν μ (.cap i) trivial h
  | lcross i j => exact psiRebase_mem _ (psiLCross_mem_parity t μ i j)
  | dcup i r =>
    apply psiRebase_mem
    change psiDiamondCup (sy := sy) (hc := hc) cs t μ i r ∈ parity (R := k) _ _ (D.parity i * r)
    simpa only [mul_comm] using psiDiamondCup_mem (sy := sy) (hc := hc) cs t μ i r
  | dcap i r =>
    apply psiRebase_mem
    change psiDiamondCap (sy := sy) (hc := hc) cs t μ i r ∈ parity (R := k) _ _ (D.parity i * r)
    simpa only [mul_comm] using psiDiamondCap_mem (sy := sy) (hc := hc) cs t μ i r

/-- All seven generator images have the prescribed integer degree. -/
theorem psiGen_mem_degree (t : k) (cs : CScalars Sc) (ν μ : X) (g : Shape I)
    (h : wt D μ g.dom = ν) :
    psiGen (sy := sy) (hc := hc) t cs ν μ g h ∈
      GradedSupercategory.degree (R := k) _ _ (gdeg D sy (g, μ)) := by
  cases g with
  | dot i => exact psiPrimaryGen_mem_degree t cs ν μ (.dot i) trivial h
  | cross i j => exact psiPrimaryGen_mem_degree t cs ν μ (.cross i j) trivial h
  | cup i => exact psiPrimaryGen_mem_degree t cs ν μ (.cup i) trivial h
  | cap i => exact psiPrimaryGen_mem_degree t cs ν μ (.cap i) trivial h
  | lcross i j => exact psiRebase_mem_degree _ (psiLCross_mem_degree t μ i j)
  | dcup i r => exact psiRebase_mem_degree _ (psiDiamondCup_mem_degree cs t μ i r)
  | dcap i r => exact psiRebase_mem_degree _ (psiDiamondCap_mem_degree cs t μ i r)

/-- Evaluate a layer with arbitrary signed left and right contexts. -/
def psiLayer (t : k) (cs : CScalars Sc) (ν μ : X)
    (u : List (Letter I)) (g : Shape I) (v : List (Letter I))
    (h : wt D μ (u ++ g.dom ++ v) = ν) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ (u ++ g.dom ++ v) h ⟶
      psiAt ν μ (u ++ g.cod ++ v)
        (by simpa only [wt_append, ← g.wt_dom_eq_wt_cod D] using h) :=
  psiPlace ν (wt D (wt D μ v) g.dom) (wt D μ v) μ u v
    (by simpa only [wt_append] using h) rfl rfl (g.wt_dom_eq_wt_cod D _).symm
    (psiGen t cs _ _ g rfl)

/-- Evaluate every well-typed raw diagram using the actual seven-shape assignment. -/
def psiRaw (t : k) (cs : CScalars Sc) (ν μ : X) :
    (L : List (LayerData I)) → {s r : List (Letter I)} →
    (hs : wt D μ s = ν) → (hr : wt D μ r = ν) → SChain s L r →
    (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ psiAt ν μ r hr)
  | [], _, _, hs, hr, h => eqToHom (psiAt_congr ν μ hs hr h)
  | x :: L, _, _, hs, hr, h =>
      eqToHom (psiAt_congr ν μ hs _ h.1) ≫
        psiLayer t cs ν μ x.1 x.2.1 x.2.2 (h.1 ▸ hs) ≫
        psiRaw t cs ν μ L _ hr h.2

private theorem psiLayer_eq_primary (t : k) (cs : CScalars Sc) (ν μ : X)
    (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) (hg : g.IsPrimary)
    (h : wt D μ (u ++ g.dom ++ v) = ν) :
    psiLayer (sy := sy) (hc := hc) t cs ν μ u g v h = psiPrimaryLayer t cs ν μ u g v hg h := by
  unfold psiLayer psiPrimaryLayer
  rw [psiGen_eq_primary t cs _ _ g hg]

/-- The complete raw evaluator restricts to the previously verified primary evaluator. -/
theorem psiRaw_eq_primary (t : k) (cs : CScalars Sc) (ν μ : X)
    (L : List (LayerData I)) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (h : SChain s L r) (hp : PrimaryLayers L) :
    psiRaw (sy := sy) (hc := hc) t cs ν μ L hs hr h =
      psiPrimaryRaw t cs ν μ L hs hr h hp := by
  induction L generalizing s with
  | nil => rfl
  | cons x L ih =>
    simp only [psiRaw, psiPrimaryRaw]
    rw [ih _ h.2 (fun y hy => hp y (List.mem_cons_of_mem x hy))]
    rw [psiLayer_eq_primary t cs ν μ x.1 x.2.1 x.2.2 (hp x List.mem_cons_self)]

/-- Evaluation respects vertical concatenation before taking the presentation quotient. -/
theorem psiRaw_append (t : k) (cs : CScalars Sc) (ν μ : X)
    (L M : List (LayerData I)) {s r q : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hq : wt D μ q = ν)
    (hL : SChain s L r) (hM : SChain r M q) :
    psiRaw (sy := sy) (hc := hc) t cs ν μ (L ++ M) hs hq (hL.append hM) =
      psiRaw t cs ν μ L hs hr hL ≫ psiRaw t cs ν μ M hr hq hM := by
  induction L generalizing s with
  | nil => cases hL; simp [psiRaw]
  | cons x L ih =>
    obtain ⟨rfl, hL⟩ := hL
    simp only [List.cons_append, psiRaw, eqToHom_refl, Category.id_comp, Category.assoc]
    congr 1
    exact ih _ hL

/-- Every raw evaluation has the parity of its source layers. -/
theorem psiRaw_mem_parity (t : k) (cs : CScalars Sc) (ν μ : X)
    (L : List (LayerData I)) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (h : SChain s L r) :
    psiRaw (sy := sy) (hc := hc) t cs ν μ L hs hr h ∈ parity (R := k) _ _ (parsum D L) := by
  induction L generalizing s with
  | nil => cases h; exact id_mem _
  | cons x L ih =>
    obtain ⟨rfl, h⟩ := h
    simp only [psiRaw, eqToHom_refl, Category.id_comp]
    exact comp_mem (psiPlace_mem_parity _ _ _ _ _ _ _ _ _ _ (psiGen_mem_parity t cs _ _ _ rfl))
      (ih _ h)

/-- Every raw evaluation retains the integer degree of its source layers. -/
theorem psiRaw_mem_degree (t : k) (cs : CScalars Sc) (ν μ : X)
    (L : List (LayerData I)) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (h : SChain s L r) :
    psiRaw (sy := sy) (hc := hc) t cs ν μ L hs hr h ∈
      GradedSupercategory.degree (R := k) _ _ (gsum D sy μ L) := by
  induction L generalizing s with
  | nil => cases h; exact GradedSupercategory.id_mem_degree _
  | cons x L ih =>
    obtain ⟨rfl, h⟩ := h
    simp only [psiRaw, eqToHom_refl, Category.id_comp]
    exact GradedSupercategory.comp_mem_degree
      (psiPlace_mem_degree _ _ _ _ _ _ _ _ _ _ (psiGen_mem_degree t cs _ _ _ rfl)) (ih _ h)

private theorem psiRaw_reindex (t : k) (cs : CScalars Sc) (ν μ : X)
    (L : List (LayerData I)) {s r s' r' : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hs' : wt D μ s' = ν) (hr' : wt D μ r' = ν)
    (h : SChain s L r) (h' : SChain s' L r')
    (e : s = s') (f : r = r') :
    psiRaw (sy := sy) (hc := hc) t cs ν μ L hs hr h =
      eqToHom (psiAt_congr ν μ hs hs' e) ≫ psiRaw t cs ν μ L hs' hr' h' ≫
        eqToHom (psiAt_congr ν μ hr' hr f.symm) := by
  cases e; cases f
  simp

private theorem psiLayer_eq (t : k) (cs : CScalars Sc) (ν ξ μ : X)
    (u : List (Letter I)) (g : Shape I) (v : List (Letter I))
    (h : wt D μ (u ++ g.dom ++ v) = ν) (hv : wt D μ v = ξ) :
    psiLayer (sy := sy) (hc := hc) t cs ν μ u g v h =
      psiPlace ν (wt D ξ g.dom) ξ μ u v
        (by rw [← hv]; simpa only [wt_append] using h) hv rfl
        (g.wt_dom_eq_wt_cod D ξ).symm (psiGen t cs _ ξ g rfl) := by
  subst ξ
  rfl

/-- The seven-shape raw evaluator commutes with placement of every source layer. -/
theorem psiRaw_whisk (t : k) (cs : CScalars Sc) (Ω ν ξ μ : X)
    (u v : List (Letter I)) (L : List (LayerData I)) {s r : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν)
    (hL : SChain s L r) :
    psiRaw (sy := sy) (hc := hc) t cs Ω μ (L.map (whL u v))
        (by rw [wt_append, wt_append, hv, hs, hu])
        (by rw [wt_append, wt_append, hv, hr, hu]) (hL.whisk u v) =
      psiPlace Ω ν ξ μ u v hu hv hs hr (psiRaw t cs ν ξ L hs hr hL) := by
  induction L generalizing s with
  | nil =>
    cases hL
    simp only [List.map_nil, psiRaw, psiPlace_id, eqToHom_refl]
  | cons x L ih =>
    obtain ⟨rfl, hL⟩ := hL
    simp only [List.map_cons, psiRaw, eqToHom_refl, Category.id_comp,
      psiPlace_comp]
    rw [← ih]
    unfold psiLayer
    rw [psiPlace_place]
    simp only [whL, Category.assoc]
    congr 1
    apply congrArg₂ (· ≫ ·)
    · exact psiLayer_eq t cs Ω (wt D ξ x.2.2) μ (u ++ x.1) x.2.1 (x.2.2 ++ v)
        _ (by rw [wt_append, hv])
    · simpa only [eqToHom_refl, Category.comp_id] using
        psiRaw_reindex t cs Ω μ (L.map (whL u v)) _ _ _ _ _ (hL.whisk u v)
          (show (u ++ x.1) ++ x.2.1.cod ++ (x.2.2 ++ v) =
            u ++ (x.1 ++ x.2.1.cod ++ x.2.2) ++ v by simp [List.append_assoc]) rfl


/-- Read the signed normal-form data of the existing diagram, forgetting redundant regions. -/
def psiLayers {μ : X} {s r : List (Letter I)} (d : ob D μ s ⟶ ob D μ r) :
    List (LayerData I) :=
  d.layers.map fun L => (L.left.map Col.l, L.gen.1, L.right.map Col.l)

@[simp] theorem psiLayers_mkD (μ : X) {s r : List (Letter I)} (L : List (LayerData I))
    (h : SChain s L r) : psiLayers (mkD D μ L h) = L := by
  simp only [psiLayers, layers_mkD, layList, List.map_map]
  simp only [Function.comp_def, lay, wd_map_l, Prod.mk.eta]
  exact List.map_id L

/-- The recovered layers have the original source and target. -/
theorem psiLayers_chain {μ : X} {s r : List (Letter I)} (d : ob D μ s ⟶ ob D μ r) :
    SChain s (psiLayers d) r := by
  obtain ⟨L, h, rfl⟩ := diag_eq_mkD d
  simpa only [psiLayers_mkD] using h

/-- Evaluate an actual diagram of the existing presentation, with all seven shapes. -/
def psiDiagram (t : k) (cs : CScalars Sc) (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (d : ob D μ s ⟶ ob D μ r) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ psiAt ν μ r hr :=
  psiRaw t cs ν μ (psiLayers d) hs hr (psiLayers_chain d)

@[simp] theorem psiDiagram_mkD (t : k) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (L : List (LayerData I)) (h : SChain s L r) :
    psiDiagram (sy := sy) (hc := hc) t cs ν μ hs hr (mkD D μ L h) =
      psiRaw t cs ν μ L hs hr h := by
  simp only [psiDiagram, psiLayers_mkD]

/-- Linear evaluation of the original free diagram module, not a replacement presentation. -/
def psiLin (t : k) (cs : CScalars Sc) (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) :
    LinDiagram k (ob D μ s) (ob D μ r) →ₗ[k]
      (psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ psiAt ν μ r hr) :=
  Finsupp.linearCombination k (psiDiagram t cs ν μ hs hr)

/-- The linear evaluation on every source normal-form diagram. -/
@[simp] theorem psiLin_mkD (t : k) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (L : List (LayerData I)) (h : SChain s L r) (a : k) :
    psiLin (sy := sy) (hc := hc) t cs ν μ hs hr (Finsupp.single (mkD D μ L h) a) =
      a • psiRaw t cs ν μ L hs hr h := by
  exact (Finsupp.linearCombination_single k (v := psiDiagram t cs ν μ hs hr) a
    (mkD D μ L h)).trans (congrArg (a • ·) (psiDiagram_mkD t cs ν μ hs hr L h))


/-- On a single bare layer, the raw evaluation is exactly its seven-shape assignment. -/
theorem psiRaw_gen (t : k) (cs : CScalars Sc) (ν μ : X) (g : Shape I)
    (h : wt D μ g.dom = ν) :
    psiRaw (sy := sy) (hc := hc) t cs ν μ [([], g, [])] h
        ((g.wt_dom_eq_wt_cod D μ).symm.trans h) (by simp [SChain]) =
      psiGen t cs ν μ g h := by
  subst ν
  simp [psiRaw, psiLayer, psiPlace, psiWhiskerLeft_nil, psiWhiskerRight_nil, Category.assoc]

@[simp] theorem psiLin_single (t : k) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (d : ob D μ s ⟶ ob D μ r) (a : k) :
    psiLin (sy := sy) (hc := hc) t cs ν μ hs hr (Finsupp.single d a) =
      a • psiDiagram t cs ν μ hs hr d :=
  Finsupp.linearCombination_single k a d

/-- The original diagram identity evaluates to the target identity. -/
@[simp] theorem psiDiagram_id (t : k) (cs : CScalars Sc) (ν μ : X)
    (s : List (Letter I)) (hs : wt D μ s = ν) :
    psiDiagram (sy := sy) (hc := hc) t cs ν μ hs hs (𝟙 (ob D μ s)) = 𝟙 _ := rfl

/-- Vertical functoriality on the actual source diagrams. -/
theorem psiDiagram_comp (t : k) (cs : CScalars Sc) (ν μ : X)
    {s r q : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hq : wt D μ q = ν)
    (d : ob D μ s ⟶ ob D μ r) (e : ob D μ r ⟶ ob D μ q) :
    psiDiagram (sy := sy) (hc := hc) t cs ν μ hs hq (d ≫ e) =
      psiDiagram t cs ν μ hs hr d ≫ psiDiagram t cs ν μ hr hq e := by
  obtain ⟨L, hL, rfl⟩ := diag_eq_mkD d
  obtain ⟨M, hM, rfl⟩ := diag_eq_mkD e
  rw [mkD_comp, psiDiagram_mkD, psiDiagram_mkD, psiDiagram_mkD]
  exact psiRaw_append t cs ν μ L M hs hr hq hL hM

/-- The linearized seven-shape evaluation respects vertical composition. -/
theorem psiLin_comp (t : k) (cs : CScalars Sc) (ν μ : X)
    {s r q : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hq : wt D μ q = ν)
    (f : LinDiagram k (ob D μ s) (ob D μ r)) (g : LinDiagram k (ob D μ r) (ob D μ q)) :
    psiLin (sy := sy) (hc := hc) t cs ν μ hs hq (f ≫ g) =
      psiLin t cs ν μ hs hr f ≫ psiLin t cs ν μ hr hq g := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' ih ih' =>
    erw [Preadditive.add_comp]
    simp only [map_add, ih, ih', Preadditive.add_comp]
  | single d a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' ih ih' =>
      erw [Preadditive.comp_add]
      simp only [map_add, ih, ih', Preadditive.comp_add]
    | single e b =>
      erw [Free.single_comp_single k (Obj (sig D))]
      rw [psiLin_single, psiLin_single, psiLin_single,
        psiDiagram_comp t cs ν μ hs hr hq]
      simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]

/-- Evaluation of the presentation's normal-form singleton notation. -/
@[simp] theorem psiLin_dg (t : k) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (L : List (LayerData I)) (h : SChain s L r) :
    psiLin (sy := sy) (hc := hc) t cs ν μ hs hr (dg D μ L h) =
      psiRaw t cs ν μ L hs hr h := by
  exact (psiLin_mkD t cs ν μ hs hr L h 1).trans (one_smul k _)

@[simp] theorem psiLin_idg (t : k) (cs : CScalars Sc) (ν μ : X)
    (s : List (Letter I)) (hs : wt D μ s = ν) :
    psiLin (sy := sy) (hc := hc) t cs ν μ hs hs (idg D μ s) = 𝟙 _ := by
  exact (psiLin_single t cs ν μ hs hs (𝟙 _) 1).trans
    ((congrArg (1 • ·) (psiDiagram_id t cs ν μ s hs)).trans (one_smul k _))

/-- The actual equal-colour defining relation belongs to the kernel of the linear evaluation. -/
theorem psiLin_quadEq (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (μ : X) (i : I) :
    psiLin (sy := sy) (hc := hc) t cs (wt D μ [up i, up i]) μ rfl rfl
      (relation D Sc (.quadEq i μ)) = 0 := by
  change psiLin t cs _ μ rfl rfl (dg D μ _ _) = 0
  rw [psiLin_dg, psiRaw_eq_primary t cs _ μ _ _ _ _
    (by intro x hx; simp only [crossL, List.singleton_append, List.mem_cons,
        List.not_mem_nil, or_false, or_self] at hx; subst x; trivial)]
  exact psiPrimaryRaw_quadEq t ht cs _ μ [] [] i rfl


/-- Actual source whiskering and boundary retyping evaluate to target placement. -/
theorem psiDiagram_place (t : k) (cs : CScalars Sc) (μ : X) (u v s r : List (Letter I))
    (hst : wt D (wt D μ v) r = wt D (wt D μ v) s)
    (d : ob D (wt D μ v) s ⟶ ob D (wt D μ v) r) :
    psiDiagram (sy := sy) (hc := hc) t cs (wt D (wt D (wt D μ v) s) u) μ
        (by rw [wt_append, wt_append]) (by rw [wt_append, wt_append, hst])
        (Diagram.cast (Diagram.whisker d (ob D (wt D (wt D μ v) s) u) (wd D μ v)
          (whiskerOK_ob D μ u v s))
          (ob_whisker D μ u v s s rfl) (ob_whisker D μ u v s r hst)) =
      psiPlace _ _ _ μ u v rfl rfl rfl hst (psiDiagram t cs _ _ rfl hst d) := by
  obtain ⟨L, hL, rfl⟩ := diag_eq_mkD d
  have e : Diagram.cast
      (Diagram.whisker (mkD D (wt D μ v) L hL) (ob D (wt D (wt D μ v) s) u)
        (wd D μ v) (whiskerOK_ob D μ u v s))
      (ob_whisker D μ u v s s rfl) (ob_whisker D μ u v s r hst) =
        mkD D μ (L.map (whL u v)) (hL.whisk u v) := by
    apply Diagram.ext
    simp only [Diagram.layers_cast, Diagram.layers_whisker, layers_mkD]
    exact layList_whisker D μ u v hL
  rw [e, psiDiagram_mkD, psiDiagram_mkD]
  exact psiRaw_whisk t cs _ _ _ μ u v L rfl rfl rfl hst hL

/-- Horizontal compatibility on the original free linear diagram module. -/
theorem psiLin_place (t : k) (cs : CScalars Sc) (μ : X) (u v s r : List (Letter I))
    (hst : wt D (wt D μ v) r = wt D (wt D μ v) s)
    (f : LinDiagram k (ob D (wt D μ v) s) (ob D (wt D μ v) r)) :
    psiLin (sy := sy) (hc := hc) t cs (wt D (wt D (wt D μ v) s) u) μ
        (by rw [wt_append, wt_append]) (by rw [wt_append, wt_append, hst])
        (LinDiagram.cast (LinDiagram.whisker f (ob D (wt D (wt D μ v) s) u) (wd D μ v)
          (whiskerOK_ob D μ u v s))
          (ob_whisker D μ u v s s rfl) (ob_whisker D μ u v s r hst)) =
      psiPlaceLinear _ _ _ μ u v rfl rfl rfl hst (psiLin t cs _ _ rfl hst f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [LinDiagram.cast]
  | add f g hf hg =>
    erw [LinDiagram.whisker_add, LinDiagram.cast_add]
    simp only [map_add, hf, hg]
  | single d a =>
    rw [LinDiagram.whisker_single, LinDiagram.cast_single, psiLin_single, psiLin_single,
      map_smul, psiDiagram_place]
    rfl


/-- The disconnected-colour quadratic defining relation is killed. -/
theorem psiLin_quadZero (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (μ : X) (i j : I)
    (hij : i ≠ j) (hd : D.d i j = 0) :
    psiLin (sy := sy) (hc := hc) t cs (wt D μ [up i, up j]) μ rfl rfl
      (relation D Sc (.quadZero i j μ hij hd)) = 0 := by
  change psiLin t cs _ μ rfl rfl (dg D μ _ _ - (Sc.t i j : k) • idg D μ [up i, up j]) = 0
  rw [map_sub, map_smul, psiLin_dg, psiLin_idg,
    psiRaw_append t cs _ μ (crossL [] i j []) (crossL [] j i []) (r := [up j, up i]) rfl
      (by simp only [wt_cons, wt_nil]; abel) rfl
      (by simp [crossL, Shape.dom, Shape.cod]) (by simp [crossL, Shape.dom, Shape.cod])]
  change psiRaw t cs _ μ [([], Shape.cross i j, [])] _ _ _ ≫
    psiRaw t cs _ μ [([], Shape.cross j i, [])] _ _ _ - _ = 0
  rw [psiRaw_gen, psiRaw_gen]
  exact sub_eq_zero.mpr (psiCross_quadZero t ht _ μ i j rfl hij hd)

/-- The complete evaluator sends the primary mixed-crossing word to the verified image. -/
theorem psiRaw_sigma (t : k) (cs : CScalars Sc) (μ : X) (i j : I) :
    psiRaw (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ (sigmaL i j)
      rfl ((sChain_sigmaL i j).wt_eq D μ) (sChain_sigmaL i j) = psiSigma t μ i j := by
  rw [psiRaw_eq_primary t cs _ μ _ _ _ _ (primaryLayers_sigmaL i j)]
  exact psiPrimaryRaw_sigma_eq t cs μ i j

/-- The adjoined mixed crossing evaluates to its independently verified target image. -/
theorem psiRaw_lcross (t : k) (cs : CScalars Sc) (μ : X) (i j : I) :
    psiRaw (sy := sy) (hc := hc) t cs (wt D μ [up j, dn i]) μ (lcrossL i j)
      ((sChain_sigmaL i j).wt_eq D μ) rfl (sChain_lcrossL i j) = psiLCross t μ i j := by
  change psiRaw t cs _ μ [([], Shape.lcross i j, [])] _ _ _ = _
  rw [psiRaw_gen]
  rfl

private theorem psiLayer_at (t : k) (cs : CScalars Sc) (Ω ν ξ μ : X)
    (u : List (Letter I)) (g : Shape I) (v : List (Letter I))
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hg : wt D ξ g.dom = ν) :
    psiLayer (sy := sy) (hc := hc) t cs Ω μ u g v
        (by rw [wt_append, wt_append, hv, hg, hu]) =
      psiPlace Ω ν ξ μ u v hu hv hg ((g.wt_dom_eq_wt_cod D ξ).symm.trans hg)
        (psiGen t cs ν ξ g hg) := by
  subst ξ ν
  rfl

/-- A contextual singleton computes by the actual target placement of its generator. -/
theorem psiRaw_layer (t : k) (cs : CScalars Sc) (Ω ν ξ μ : X)
    (u : List (Letter I)) (g : Shape I) (v : List (Letter I))
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hg : wt D ξ g.dom = ν) :
    psiRaw (sy := sy) (hc := hc) t cs Ω μ [(u, g, v)]
        (by rw [wt_append, wt_append, hv, hg, hu])
        (by rw [wt_append, wt_append, hv, ← g.wt_dom_eq_wt_cod D, hg, hu]) ⟨rfl, rfl⟩ =
      psiPlace Ω ν ξ μ u v hu hv hg ((g.wt_dom_eq_wt_cod D ξ).symm.trans hg)
        (psiGen t cs ν ξ g hg) := by
  simp only [psiRaw, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact psiLayer_at t cs Ω ν ξ μ u g v hu hv hg

/-- Source left dots evaluate to the actual two-strand left dot used in the target relations. -/
theorem psiRaw_dotLeft (t : k) (cs : CScalars Sc) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j] = ν) :
    psiRaw (sy := sy) (hc := hc) t cs ν μ (dotsL [] i [up j] 1) h h
      (sChain_dotsL [] i [up j] 1) = psiDotLeft t ν μ i j h := by
  subst ν
  change psiRaw t cs _ μ [([], Shape.dot i, [up j])] _ _ _ = _
  erw [psiRaw_layer t cs _ _ _ μ [] (.dot i) [up j] rfl rfl rfl]
  change psiPlace _ _ _ μ [] [up j] rfl rfl rfl rfl (psiDot t (wt D μ [up j]) i) = _
  simp only [psiPlace, wt_nil]
  erw [psiWhiskerLeft_nil]
  simp only [psiWhiskerRight, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact psiDot_whiskerRight t μ i j

/-- Source right dots evaluate to the actual two-strand right dot. -/
theorem psiRaw_dotRight (t : k) (cs : CScalars Sc) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j] = ν) :
    psiRaw (sy := sy) (hc := hc) t cs ν μ (dotsL [up i] j [] 1) h h
      (sChain_dotsL [up i] j [] 1) = psiDotRight t ν μ i j h := by
  subst ν
  change psiRaw t cs _ μ [([up i], Shape.dot j, [])] _ _ _ = _
  erw [psiRaw_layer t cs _ _ μ μ [up i] (.dot j) [] rfl rfl rfl]
  change psiPlace _ _ μ μ [up i] [] rfl rfl rfl rfl (psiDot t μ j) = _
  simp only [psiPlace, psiWhiskerRight_nil]
  simp only [psiWhiskerLeft, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact psiDot_whiskerLeft t μ i j


/-- The raw upward crossing has its printed target image. -/
theorem psiRaw_cross (t : k) (cs : CScalars Sc) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j] = ν) :
    psiRaw (sy := sy) (hc := hc) t cs ν μ (crossL [] i j []) h
      ((Shape.cross i j).wt_dom_eq_wt_cod D μ |>.symm.trans h)
      (by simp [crossL, Shape.dom, Shape.cod]) = psiCross t ν μ i j h := by
  change psiRaw t cs ν μ [([], Shape.cross i j, [])] _ _ _ = _
  rw [psiRaw_gen]
  rfl

end OddMath.SKM
