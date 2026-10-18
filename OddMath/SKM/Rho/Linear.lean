import OddMath.SKM.Rho.Raw

/-!
# Linear for ρ

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

def rhoDiagram (t : k) (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (d : ob D μ s ⟶ ob D μ r) :
    rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ rhoAt ν μ r hr :=
  rhoRaw t ν μ (psiLayers d) hs hr (psiLayers_chain d)

@[simp] theorem rhoDiagram_mkD (t : k) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (L : List (LayerData I)) (h : SChain s L r) :
    rhoDiagram (sy := sy) (hc := hc) t ν μ hs hr (mkD D μ L h) =
      rhoRaw t ν μ L hs hr h := by
  simp only [rhoDiagram, psiLayers_mkD]

def rhoLin (t : k) (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) :
    LinDiagram k (ob D μ s) (ob D μ r) →ₗ[k]
      (rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ rhoAt ν μ r hr) :=
  Finsupp.linearCombination k (rhoDiagram t ν μ hs hr)

@[simp] theorem rhoLin_mkD (t : k) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (L : List (LayerData I)) (h : SChain s L r) (a : k) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hr (Finsupp.single (mkD D μ L h) a) =
      a • rhoRaw t ν μ L hs hr h := by
  exact (Finsupp.linearCombination_single k (v := rhoDiagram t ν μ hs hr) a
    (mkD D μ L h)).trans (congrArg (a • ·) (rhoDiagram_mkD t ν μ hs hr L h))

theorem rhoRaw_gen (t : k) (ν μ : X) (g : Shape I)
    (h : wt D μ g.dom = ν) :
    rhoRaw (sy := sy) (hc := hc) t ν μ [([], g, [])] h
        ((g.wt_dom_eq_wt_cod D μ).symm.trans h) (by simp [SChain]) =
      RhoGenerators.generator t ν μ g h := by
  subst ν
  simp [rhoRaw, rhoLayer, place_nil, Category.assoc]

@[simp] theorem rhoLin_single (t : k) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (d : ob D μ s ⟶ ob D μ r) (a : k) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hr (Finsupp.single d a) =
      a • rhoDiagram t ν μ hs hr d :=
  Finsupp.linearCombination_single k a d

@[simp] theorem rhoDiagram_id (t : k) (ν μ : X)
    (s : List (Letter I)) (hs : wt D μ s = ν) :
    rhoDiagram (sy := sy) (hc := hc) t ν μ hs hs (𝟙 (ob D μ s)) = 𝟙 _ := rfl

theorem rhoDiagram_comp (t : k) (ν μ : X)
    {s r q : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hq : wt D μ q = ν)
    (d : ob D μ s ⟶ ob D μ r) (e : ob D μ r ⟶ ob D μ q) :
    rhoDiagram (sy := sy) (hc := hc) t ν μ hs hq (d ≫ e) =
      rhoDiagram t ν μ hs hr d ≫ rhoDiagram t ν μ hr hq e := by
  obtain ⟨L, hL, rfl⟩ := diag_eq_mkD d
  obtain ⟨M, hM, rfl⟩ := diag_eq_mkD e
  rw [mkD_comp, rhoDiagram_mkD, rhoDiagram_mkD, rhoDiagram_mkD]
  exact rhoRaw_append t ν μ L M hs hr hq hL hM

theorem rhoLin_comp (t : k) (ν μ : X)
    {s r q : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hq : wt D μ q = ν)
    (f : LinDiagram k (ob D μ s) (ob D μ r)) (g : LinDiagram k (ob D μ r) (ob D μ q)) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hq (f ≫ g) =
      rhoLin t ν μ hs hr f ≫ rhoLin t ν μ hr hq g := by
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
      rw [rhoLin_single, rhoLin_single, rhoLin_single,
        rhoDiagram_comp t ν μ hs hr hq]
      simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]

@[simp] theorem rhoLin_dg (t : k) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (L : List (LayerData I)) (h : SChain s L r) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hr (dg D μ L h) =
      rhoRaw t ν μ L hs hr h := by
  exact (rhoLin_mkD t ν μ hs hr L h 1).trans (one_smul k _)

@[simp] theorem rhoLin_idg (t : k) (ν μ : X)
    (s : List (Letter I)) (hs : wt D μ s = ν) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hs (idg D μ s) = 𝟙 _ := by
  exact (rhoLin_single t ν μ hs hs (𝟙 _) 1).trans
    ((congrArg (1 • ·) (rhoDiagram_id t ν μ s hs)).trans (one_smul k _))

theorem rhoDiagram_place (t : k) (μ : X) (u v s r : List (Letter I))
    (hst : wt D (wt D μ v) r = wt D (wt D μ v) s)
    (d : ob D (wt D μ v) s ⟶ ob D (wt D μ v) r) :
    rhoDiagram (sy := sy) (hc := hc) t (wt D (wt D (wt D μ v) s) u) μ
        (by rw [wt_append, wt_append]) (by rw [wt_append, wt_append, hst])
        (Diagram.cast (Diagram.whisker d (ob D (wt D (wt D μ v) s) u) (wd D μ v)
          (whiskerOK_ob D μ u v s))
          (ob_whisker D μ u v s s rfl) (ob_whisker D μ u v s r hst)) =
      place _ _ _ μ u v rfl rfl rfl hst (rhoDiagram t _ _ rfl hst d) := by
  obtain ⟨L, hL, rfl⟩ := diag_eq_mkD d
  have e : Diagram.cast
      (Diagram.whisker (mkD D (wt D μ v) L hL) (ob D (wt D (wt D μ v) s) u)
        (wd D μ v) (whiskerOK_ob D μ u v s))
      (ob_whisker D μ u v s s rfl) (ob_whisker D μ u v s r hst) =
        mkD D μ (L.map (whL u v)) (hL.whisk u v) := by
    apply Diagram.ext
    simp only [Diagram.layers_cast, Diagram.layers_whisker, layers_mkD]
    exact layList_whisker D μ u v hL
  rw [e, rhoDiagram_mkD, rhoDiagram_mkD]
  exact rhoRaw_whisk t _ _ _ μ u v L rfl rfl rfl hst hL

theorem rhoLin_place (t : k) (μ : X) (u v s r : List (Letter I))
    (hst : wt D (wt D μ v) r = wt D (wt D μ v) s)
    (f : LinDiagram k (ob D (wt D μ v) s) (ob D (wt D μ v) r)) :
    rhoLin (sy := sy) (hc := hc) t (wt D (wt D (wt D μ v) s) u) μ
        (by rw [wt_append, wt_append]) (by rw [wt_append, wt_append, hst])
        (LinDiagram.cast (LinDiagram.whisker f (ob D (wt D (wt D μ v) s) u) (wd D μ v)
          (whiskerOK_ob D μ u v s))
          (ob_whisker D μ u v s s rfl) (ob_whisker D μ u v s r hst)) =
      placeLinear _ _ _ μ u v rfl rfl rfl hst (rhoLin t _ _ rfl hst f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [LinDiagram.cast]
  | add f g hf hg =>
    erw [LinDiagram.whisker_add, LinDiagram.cast_add]
    simp only [map_add, hf, hg]
  | single d a =>
    rw [LinDiagram.whisker_single, LinDiagram.cast_single, rhoLin_single, rhoLin_single,
      map_smul, rhoDiagram_place]
    rfl

end OddMath.SKM.RhoEvaluator
