/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.EvenBridge.Datum
import OddMath.SKM.Presentation
import Categorification.Diagrams.KL3.Decompositions
import Categorification.Diagrams.KL3.BubbleSlidesGen
import Categorification.Diagrams.KL3.EndOne

/-!
# The generators of `𝔘(𝔤)` in the Khovanov–Lauda 2-category, for even data

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5,
for a datum all of whose colours are even (`IsEven D`), compared with A. D. Lauda,
M. Khovanov, *A categorification of quantum sl(n)* III (KL III, arXiv:0807.3250),
Definition 3.1, for a compatible symmetric datum `C` (`Compatible D C`).

This file sends the generators of Definition 1.5 to 2-morphisms of KL III's `U` (in the weight
datum `weightDatum D C hc`):

* the dot, the upward crossing, the rightward cup `η` and cap `ε` go to the dot, the crossing,
  and the cup and cap of the downward strand;
* the leftward crossing (2.6) goes to KL III's sideways crossing `crossrL`;
* the `♦`-cups and `♦`-caps (2.6) go to the components of the inverse of KL III's
  decomposition (Proposition 3.25) dual to the components `ε ∘ (xⁿ ⊗ 1)` and
  `(1 ⊗ xⁿ) ∘ η` of (1.13), (1.14).

The images are described on layers in normal form (`map_mkD_single`): the layer `u ⊗ g ⊗ v`
goes to the placement of the image of `g` between the strands `u` and `v`.
-/

noncomputable section

namespace OddMath.SKM.EvenBridge

open CategoryTheory Categorification.KL3

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
  (C : Categorification.QuantumGroup.CartanDatum I) (hc : Compatible D C)
  (k : Type w) [CommRing k]

/-- Shorthand for the KL III weight datum of `D`. -/
local notation "RD" => weightDatum D C hc

/-! ## Weights and words -/

theorem sh_eq (l : Letter I) : Diagram.sh RD l = sh D l := by
  obtain ⟨b, i⟩ := l
  cases b <;> simp [Diagram.sh, sh, Categorification.QuantumGroup.UDot.sgn]

theorem wt_eq (μ : X) (t : List (Letter I)) : Diagram.wt RD μ t = wt D μ t := by
  induction t with
  | nil => rfl
  | cons l t ih => rw [Diagram.wt_cons, wt_cons, ih, sh_eq]

theorem wt_fun : Diagram.wt RD = wt D := funext fun μ => funext fun t => wt_eq D C hc μ t

/-- Relabelling of regions and strands: the identity on weights and on signed letters. -/
def κ : StringDiagrams.ColourMap (sig D) (Diagram.psig RD) where
  region := id
  colour c := ⟨c.l, c.r⟩
  colourSrc c := by
    show Diagram.sh RD c.l + c.r = sh D c.l + c.r
    rw [sh_eq]
  colourTgt _ := rfl

theorem κ_word_wd (μ : X) (t : List (Letter I)) :
    (κ D C hc).word (wd D μ t) = Diagram.wd RD μ t := by
  rw [(κ D C hc).word_eq]
  induction t with
  | nil => rfl
  | cons l t ih =>
    rw [wd_cons, List.map_cons, ih, Diagram.wd_cons, wt_eq]
    rfl

theorem κ_obj_ob (μ : X) (t : List (Letter I)) :
    (κ D C hc).obj (ob D μ t) = Diagram.ob RD μ t := by
  refine StringDiagrams.Obj.ext ?_ ?_
  · exact (wt_eq D C hc μ t).symm
  · exact κ_word_wd D C hc μ t


/-! ## Placement between empty contexts -/

/-- Placement between empty strand sequences is the identity, up to retyping. -/
theorem plcL_nil_nil (μ : X) (s t : List (Letter I))
    (hst : Diagram.wt RD μ t = Diagram.wt RD μ s)
    (f : (Diagram.pres RD k).obj (Diagram.ob RD μ s) ⟶ (Diagram.pres RD k).obj (Diagram.ob RD μ t)) :
    Diagram.plcL RD k μ [] [] s t f =
      eqToHom (by simp) ≫ f ≫ eqToHom (by simp) := by
  let ψ : ((Diagram.pres RD k).obj (Diagram.ob RD μ s) ⟶
      (Diagram.pres RD k).obj (Diagram.ob RD μ t)) →ₗ[k]
      ((Diagram.pres RD k).obj (Diagram.ob RD μ ([] ++ s ++ [])) ⟶
        (Diagram.pres RD k).obj (Diagram.ob RD μ ([] ++ t ++ []))) :=
    { toFun := fun f => eqToHom (by simp) ≫ f ≫ eqToHom (by simp)
      map_add' := fun f g => by simp
      map_smul' := fun r f => by simp }
  show _ = ψ f
  refine LinearMap.congr_fun (Diagram.hom_ext_diag RD k (Diagram.plcL RD k μ [] [] s t) ψ
    fun d => ?_) f
  rw [Diagram.plcL_diag, StringDiagrams.Presentation.diag_cast]
  have hl : StringDiagrams.Diagram.layers (StringDiagrams.Diagram.whisker d
      (Diagram.ob RD (Diagram.wt RD (Diagram.wt RD μ []) s) []) (Diagram.wd RD μ [])
      (Diagram.whiskerOK_ob RD μ [] [] s)) = StringDiagrams.Diagram.layers d := by
    rw [StringDiagrams.Diagram.layers_whisker]
    conv_rhs => rw [← List.map_id (StringDiagrams.Diagram.layers d)]
    exact List.map_congr_left fun L hL =>
      StringDiagrams.Layer.ext ((StringDiagrams.Diagram.chain d).start_of_mem hL).symm
        (List.nil_append _) rfl (List.append_nil _)
  rw [(Diagram.pres RD k).diag_eq_of_layers_eq'
    (StringDiagrams.Diagram.whisker d _ _ (Diagram.whiskerOK_ob RD μ [] [] s)) d
    (StringDiagrams.Obj.ext rfl (by simp)) (StringDiagrams.Obj.ext (by simp [hst]) (by simp)) hl]
  simp [ψ]

/-! ## Images of the generators -/

/-- The image of the generator of shape `g` with rightmost region `ν`, as a 2-morphism of KL III's
`U` between the boundaries of `g` read in `U`. -/
def imgS (ν : X) : (g : Shape I) →
    ((Diagram.pres RD k).obj (Diagram.ob RD ν g.dom) ⟶
      (Diagram.pres RD k).obj (Diagram.ob RD ν g.cod))
  | .dot i => Diagram.dg RD k ν _ _ [([], .dot (true, i), [])]
  | .cross i j => Diagram.dg RD k ν _ _ [([], .cross true i j, [])]
  | .cup i => Diagram.dg RD k ν _ _ [([], .cup (false, i), [])]
  | .cap i => Diagram.dg RD k ν _ _ [([], .cap (false, i), [])]
  | .lcross i j => Diagram.dg RD k ν _ _ (Diagram.crossrL j i)
  | .dcup i n =>
    if n < (Diagram.ip RD i ν).toNat then
      ∑ g ∈ Finset.range ((Diagram.ip RD i ν).toNat - n),
        Diagram.ccwU RD k ν i (-Diagram.ip RD i ν - 1 + g) ≫ Diagram.betaEF RD k i ν (n + g)
    else 0
  | .dcap i n =>
    if n < (-Diagram.ip RD i ν).toNat then
      Diagram.alphaFE RD k i ν ((-Diagram.ip RD i ν).toNat - 1 - n)
    else 0

theorem genDom_eq (ν : X) (g : Shape I) :
    StringDiagrams.LocalMap.genDom (κ D C hc) (g, ν) = Diagram.ob RD ν g.dom :=
  κ_obj_ob D C hc ν g.dom

theorem genCod_eq (ν : X) (g : Shape I) :
    StringDiagrams.LocalMap.genCod (κ D C hc) (g, ν) = Diagram.ob RD ν g.cod := by
  show (κ D C hc).obj ⟨(wt D ν g.dom : X), wd D ν g.cod⟩ = _
  rw [Shape.wt_dom_eq_wt_cod]
  exact κ_obj_ob D C hc ν g.cod

/-- The images of the generators, between the relabelled boundaries. -/
def img (g : Shape I × X) :
    (Diagram.pres RD k).obj (StringDiagrams.LocalMap.genDom (κ D C hc) g) ⟶
      (Diagram.pres RD k).obj (StringDiagrams.LocalMap.genCod (κ D C hc) g) :=
  eqToHom (congrArg (Diagram.pres RD k).obj (genDom_eq D C hc g.2 g.1)) ≫ imgS D C hc k g.2 g.1 ≫
    eqToHom (congrArg (Diagram.pres RD k).obj (genCod_eq D C hc g.2 g.1)).symm

theorem img_eq (g : Shape I) {ν ν' : X} (h : ν' = ν) :
    img D C hc k (g, ν) =
      eqToHom (congrArg (Diagram.pres RD k).obj (by rw [genDom_eq, h])) ≫ imgS D C hc k ν' g ≫
        eqToHom (congrArg (Diagram.pres RD k).obj (by rw [genCod_eq, h])) := by
  subst h; rfl

/-- The local map of the images of the generators. -/
abbrev locMap : StringDiagrams.LocalMap (sig D) (Diagram.pres RD k) :=
  StringDiagrams.LocalMap.ofGen (κ D C hc) (img D C hc k)

theorem whisk_transport {S : StringDiagrams.Signature} {R : Type*} [CommRing R]
    {Q : StringDiagrams.Presentation S R} {a b a' b' : StringDiagrams.Obj S}
    (f : Q.obj a ⟶ Q.obj b) (f' : Q.obj a' ⟶ Q.obj b') (ha : a = a') (hb : b = b')
    (hf : f = eqToHom (congrArg Q.obj ha) ≫ f' ≫ eqToHom (congrArg Q.obj hb).symm)
    {u u' : StringDiagrams.Obj S} {v v' : List S.Colour} (hu : u = u') (hv : v = v') :
    Q.whisk f u v = eqToHom (by rw [ha, hu, hv]) ≫ Q.whisk f' u' v' ≫ eqToHom (by rw [hb, hu, hv]) := by
  subst ha hb hu hv; simp [hf]

/-- **The image of a layer** `u ⊗ g ⊗ v` (rightmost region `μ`) is the image of `g` placed
between the strands `u` and `v`. -/
theorem map_mkD_single (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I))
    (h : SChain (u ++ g.dom ++ v) [(u, g, v)] (u ++ g.cod ++ v)) :
    (locMap D C hc k).functor.map (mkD D μ [(u, g, v)] h) =
      eqToHom (congrArg (Diagram.pres RD k).obj (κ_obj_ob D C hc μ _)) ≫
        Diagram.plcL RD k μ u v g.dom g.cod (imgS D C hc k (Diagram.wt RD μ v) g) ≫
          eqToHom (congrArg (Diagram.pres RD k).obj (κ_obj_ob D C hc μ _)).symm := by
  have hst : Diagram.wt RD (Diagram.wt RD μ v) g.cod = Diagram.wt RD (Diagram.wt RD μ v) g.dom := by
    rw [wt_eq, wt_eq, wt_eq, Shape.wt_dom_eq_wt_cod]
  rw [Diagram.plcL, dite_eq_left hst]
  show (locMap D C hc k).toInterpretation.functor.map _ = _
  dsimp only [mkD, layList, List.map]
  rw [StringDiagrams.Interpretation.functor_map_mk_cons,
    StringDiagrams.Interpretation.functor_map_mk_nil]
  simp only [StringDiagrams.LocalMap.toInterpretation_layer, StringDiagrams.LocalMap.ofGen_layer]
  have hv' : wt D μ v = Diagram.wt RD μ v := (wt_eq D C hc μ v).symm
  have hu : (κ D C hc).obj ⟨(wt D μ (u ++ g.dom ++ v) : X), wd D (wt D μ (g.dom ++ v)) u⟩ =
      Diagram.ob RD (Diagram.wt RD (Diagram.wt RD μ v) g.dom) u := by
    rw [List.append_assoc, wt_append, wt_append]
    exact (κ_obj_ob D C hc _ u).trans (by simp only [wt_eq])
  have hw : (κ D C hc).word (wd D μ v) = Diagram.wd RD μ v := κ_word_wd D C hc μ v
  erw [whisk_transport (img D C hc k (g, wt D μ v)) (imgS D C hc k (Diagram.wt RD μ v) g)
    (by rw [genDom_eq, hv']) (by rw [genCod_eq, hv']) (img_eq D C hc k g hv'.symm) hu hw]
  simp only [Diagram.plc, LinearMap.coe_mk, AddHom.coe_mk, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]


/-! ## Diagrams without `♦`-cups and `♦`-caps -/

/-- A shape other than a `♦`-cup or `♦`-cap: its image is a diagram. -/
def PlainShape : Shape I → Prop
  | .dcup _ _ => False
  | .dcap _ _ => False
  | _ => True

/-- The layers of the image of a layer with a plain shape. -/
def trLay : LayerData I → List (Diagram.LayerData I)
  | (u, .dot i, v) => [(u, .dot (true, i), v)]
  | (u, .cross i j, v) => [(u, .cross true i j, v)]
  | (u, .cup i, v) => [(u, .cup (false, i), v)]
  | (u, .cap i, v) => [(u, .cap (false, i), v)]
  | (u, .lcross i j, v) => (Diagram.crossrL j i).map (Diagram.whL u v)
  | (_, .dcup _ _, _) => []
  | (_, .dcap _ _, _) => []

theorem sChain_trLay (x : LayerData I) (hx : PlainShape x.2.1) :
    Diagram.SChain (x.1 ++ x.2.1.dom ++ x.2.2) (trLay x) (x.1 ++ x.2.1.cod ++ x.2.2) := by
  obtain ⟨u, g, v⟩ := x
  cases g with
  | dot i => exact ⟨rfl, rfl⟩
  | cross i j => exact ⟨rfl, rfl⟩
  | cup i => exact ⟨rfl, rfl⟩
  | cap i => exact ⟨rfl, rfl⟩
  | lcross i j =>
    exact Diagram.SChain.whisk (show Diagram.SChain [(false, i), (true, j)] (Diagram.crossrL j i)
      [(true, j), (false, i)] by schain) u v
  | dcup i n => exact hx.elim
  | dcap i n => exact hx.elim

theorem sChain_flatMap_trLay {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t)
    (hp : ∀ x ∈ ls, PlainShape x.2.1) : Diagram.SChain s (ls.flatMap trLay) t := by
  induction ls generalizing s with
  | nil => exact h
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    rw [List.flatMap_cons]
    exact (sChain_trLay x (hp x (by simp))).append
      (ih h fun y hy => hp y (List.mem_cons_of_mem _ hy))

theorem plcL_imgS (μ : X) (x : LayerData I) (hx : PlainShape x.2.1) :
    Diagram.plcL RD k μ x.1 x.2.2 x.2.1.dom x.2.1.cod (imgS D C hc k (Diagram.wt RD μ x.2.2) x.2.1) =
      Diagram.dg RD k μ _ _ (trLay x) := by
  obtain ⟨u, g, v⟩ := x
  cases g with
  | dot i => simp [imgS, Diagram.plcL_dg, trLay, Diagram.whL]
  | cross i j => simp [imgS, Diagram.plcL_dg, trLay, Diagram.whL]
  | cup i => simp [imgS, Diagram.plcL_dg, trLay, Diagram.whL]
  | cap i => simp [imgS, Diagram.plcL_dg, trLay, Diagram.whL]
  | lcross i j => exact Diagram.plcL_dg RD k μ u v _ _ _
  | dcup i n => exact hx.elim
  | dcap i n => exact hx.elim

/-- **The image of a diagram without `♦`-cups and `♦`-caps** is the diagram with the translated
layers. -/
theorem map_mkD_plain (μ : X) (ls : List (LayerData I)) {s t : List (Letter I)}
    (h : SChain s ls t) (hp : ∀ x ∈ ls, PlainShape x.2.1) :
    (locMap D C hc k).functor.map (mkD D μ ls h) =
      eqToHom (congrArg (Diagram.pres RD k).obj (κ_obj_ob D C hc μ s)) ≫
        Diagram.dg RD k μ s t (ls.flatMap trLay) ≫
          eqToHom (congrArg (Diagram.pres RD k).obj (κ_obj_ob D C hc μ t)).symm := by
  induction ls generalizing s with
  | nil =>
    obtain rfl : s = t := h
    rw [List.flatMap_nil, Diagram.dg_nil]
    show (locMap D C hc k).toInterpretation.functor.map _ = _
    dsimp only [mkD, layList, List.map]
    rw [StringDiagrams.Interpretation.functor_map_mk_nil]
    simp
  | cons x ls ih =>
    obtain ⟨u, g, v⟩ := x
    obtain ⟨rfl, h'⟩ := h
    have h₁ : SChain (u ++ g.dom ++ v) [(u, g, v)] (u ++ g.cod ++ v) := ⟨rfl, rfl⟩
    have hp' : ∀ y ∈ ls, PlainShape y.2.1 := fun y hy => hp y (List.mem_cons_of_mem _ hy)
    rw [show mkD D μ ((u, g, v) :: ls) ⟨rfl, h'⟩ = mkD D μ [(u, g, v)] h₁ ≫ mkD D μ ls h' from
      (mkD_comp D μ _ _ h₁ h').symm, Functor.map_comp, map_mkD_single, ih h' hp',
      plcL_imgS D C hc k μ (u, g, v) (hp (u, g, v) (by simp)), List.flatMap_cons,
      ← Diagram.dg_comp (sChain_trLay (u, g, v) (hp (u, g, v) (by simp)))
        (sChain_flatMap_trLay h' hp')]
    simp

theorem flatMap_trLay_dotsL (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℕ) :
    (dotsL u i v n).flatMap trLay =
      List.replicate n (u, (Diagram.Shape.dot (true, i) : Diagram.Shape I), v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dotsL, List.replicate_succ, List.flatMap_cons, List.replicate_succ, ← ih]
    rfl

theorem plain_dotsL (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℕ) :
    ∀ x ∈ dotsL u i v n, PlainShape x.2.1 := by
  intro x hx
  rw [dotsL, List.mem_replicate] at hx
  rw [hx.2]; trivial

variable (Sc : Scalars D k)

/-- The image of a normal-form diagram without `♦`-cups and `♦`-caps under the linear extension. -/
theorem lin_dg_plain (μ : X) (ls : List (LayerData I)) {s t : List (Letter I)}
    (h : SChain s ls t) (hp : ∀ x ∈ ls, PlainShape x.2.1) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map (dg D μ ls h) =
      eqToHom (congrArg (Diagram.pres RD k).obj (κ_obj_ob D C hc μ s)) ≫
        Diagram.dg RD k μ s t (ls.flatMap trLay) ≫
          eqToHom (congrArg (Diagram.pres RD k).obj (κ_obj_ob D C hc μ t)).symm := by
  rw [dg, StringDiagrams.freeLift_map_of, map_mkD_plain D C hc k μ ls h hp]

theorem lin_idg (μ : X) (t : List (Letter I)) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map (idg D (k := k) μ t) =
      eqToHom (congrArg (Diagram.pres RD k).obj (κ_obj_ob D C hc μ t)) ≫
        Diagram.dg RD k μ t t [] ≫
          eqToHom (congrArg (Diagram.pres RD k).obj (κ_obj_ob D C hc μ t)).symm := by
  rw [idg, StringDiagrams.freeLift_map_of, CategoryTheory.Functor.map_id, Diagram.dg_nil]
  simp

theorem rel_quadEq (i : I) (ν : X) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map (relation D Sc (.quadEq i ν)) = 0 := by
  simp only [relation]
  rw [lin_dg_plain D C hc k ν _ _ (by simp [crossL, PlainShape])]
  simp only [crossL, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil, trLay,
    List.append_nil]
  dsimp only [Rel.dom, Rel.cod]
  rw [Diagram.dg_sqEq]
  simp


theorem plain_crossL (u : List (Letter I)) (i j : I) (v : List (Letter I)) :
    ∀ x ∈ crossL u i j v, PlainShape x.2.1 := by
  simp [crossL, PlainShape]

theorem plain_sigmaL (i j : I) : ∀ x ∈ sigmaL i j, PlainShape x.2.1 := by
  simp [sigmaL, PlainShape]

theorem plain_lcrossL (i j : I) : ∀ x ∈ lcrossL i j, PlainShape x.2.1 := by
  simp [lcrossL, PlainShape]

theorem plain_epsL (i : I) (n : ℕ) : ∀ x ∈ epsL i n, PlainShape x.2.1 := by
  intro x hx
  rw [epsL, List.mem_append] at hx
  rcases hx with hx | hx
  · exact plain_dotsL _ _ _ _ x hx
  · simp at hx; rw [hx]; trivial

theorem plain_etaL (i : I) (n : ℕ) : ∀ x ∈ etaL i n, PlainShape x.2.1 := by
  intro x hx
  rw [etaL, List.mem_append] at hx
  rcases hx with hx | hx
  · simp at hx; rw [hx]; trivial
  · exact plain_dotsL _ _ _ _ x hx

theorem plain_append {l l' : List (LayerData I)} (h : ∀ x ∈ l, PlainShape x.2.1)
    (h' : ∀ x ∈ l', PlainShape x.2.1) : ∀ x ∈ l ++ l', PlainShape x.2.1 := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  exacts [h x hx, h' x hx]

/-- Discharges `∀ x ∈ ls, PlainShape x.2.1` for layer lists built from the named pieces. -/
macro "plain" : tactic => `(tactic| first
  | (repeat' apply plain_append) <;> first
      | exact plain_crossL _ _ _ _ | exact plain_dotsL _ _ _ _ | exact plain_sigmaL _ _
      | exact plain_lcrossL _ _ | exact plain_epsL _ _ | exact plain_etaL _ _
      | simp [PlainShape])

/-- The scalars of KL III: `tᵢⱼ = 1` and `sᵢⱼ^{pq} = 0`. -/
def IsKLScalars : Prop := (∀ i j, Sc.t i j = 1) ∧ ∀ i j p q, Sc.s i j p q = 0

theorem zsign_even (hD : IsEven D) (i j : I) : zsign k (D.parity i * D.parity j) = 1 := by
  simp [zsign, hD i]

theorem zsign_even' (hD : IsEven D) (i : I) (a : ZMod 2) : zsign k (D.parity i * a) = 1 := by
  simp [zsign, hD i]

theorem flatMap_trLay_crossL (u : List (Letter I)) (i j : I) (v : List (Letter I)) :
    (crossL u i j v).flatMap trLay = [(u, Diagram.Shape.cross true i j, v)] := rfl

theorem flatMap_trLay_sigmaL (i j : I) :
    (sigmaL i j).flatMap trLay = Diagram.crosslL j i := rfl

theorem flatMap_trLay_lcrossL (i j : I) :
    (lcrossL i j).flatMap trLay = Diagram.crossrL j i := by
  simp [lcrossL, trLay]

theorem flatMap_trLay_epsL (i : I) (n : ℕ) :
    (epsL i n).flatMap trLay =
      List.replicate n ([], Diagram.Shape.dot (true, i), [(false, i)]) ++
        [([], Diagram.Shape.cap (false, i), [])] := by
  rw [epsL, List.flatMap_append, flatMap_trLay_dotsL]; rfl

theorem flatMap_trLay_etaL (i : I) (n : ℕ) :
    (etaL i n).flatMap trLay =
      [([], Diagram.Shape.cup (false, i), [])] ++
        List.replicate n ([(false, i)], Diagram.Shape.dot (true, i), []) := by
  rw [etaL, List.flatMap_append, flatMap_trLay_dotsL]; rfl

/-- Rewrites the image of a relation built from diagrams without `♦`-cups and `♦`-caps as a
combination of KL III normal forms. -/
macro "reduce_rel" : tactic => `(tactic| (
  simp only [relation, Functor.map_sub, Functor.map_add, Functor.map_neg, Functor.map_smul,
    Functor.map_sum]
  simp (disch := plain) only [lin_dg_plain, lin_idg]
  simp only [List.flatMap_append, flatMap_trLay_crossL, flatMap_trLay_dotsL, flatMap_trLay_sigmaL,
    flatMap_trLay_lcrossL, flatMap_trLay_epsL, flatMap_trLay_etaL, List.cons_append,
    List.nil_append, List.append_nil, List.flatMap_cons, List.flatMap_nil, trLay, List.replicate_one]
  dsimp only [Rel.dom, Rel.cod]))

theorem rel_quadZero (hS : IsKLScalars D k Sc) (i j : I) (ν : X) (hij : i ≠ j) (hd : D.d i j = 0) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map
      (relation D Sc (.quadZero i j ν hij hd)) = 0 := by
  reduce_rel
  rw [Diagram.dg_sqNe _ _ _ _ _ hij, ite_eq_left ((dot_eq_zero_iff hc i j).2 hd), hS.1 i j]
  simp

theorem rel_quadNe (hS : IsKLScalars D k Sc) (i j : I) (ν : X) (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map
      (relation D Sc (.quadNe i j ν hij hd)) = 0 := by
  reduce_rel
  rw [Diagram.dg_sqNe _ _ _ _ _ hij, ite_eq_right (mt (dot_eq_zero_iff hc i j).1 hd), hS.1 i j,
    hS.1 j i, dij_eq_dn hc, dij_eq_dn hc]
  simp [hS.2, Preadditive.add_comp, Preadditive.comp_add]


theorem ip_eq (i : I) (ν : X) : Diagram.ip RD i ν = D.h i ν := rfl


theorem rel_slideL (hD : IsEven D) (i j : I) (ν : X) (hij : i ≠ j) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map (relation D Sc (.slideL i j ν hij)) = 0 := by
  reduce_rel
  rw [zsign_even D k hD, Diagram.dg_slideRNe _ _ _ _ _ hij]
  simp

theorem rel_slideLEq (hD : IsEven D) (i : I) (ν : X) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map (relation D Sc (.slideLEq i ν)) = 0 := by
  reduce_rel
  rw [zsign_even D k hD, Diagram.dg_slideREq]
  simp [Preadditive.add_comp, Preadditive.comp_add]

theorem rel_slideR (hD : IsEven D) (i j : I) (ν : X) (hij : i ≠ j) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map (relation D Sc (.slideR i j ν hij)) = 0 := by
  reduce_rel
  rw [zsign_even D k hD, Diagram.dg_slideLNe _ _ _ _ _ hij]
  simp

theorem rel_slideREq (hD : IsEven D) (i : I) (ν : X) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map (relation D Sc (.slideREq i ν)) = 0 := by
  reduce_rel
  rw [zsign_even D k hD, Diagram.dg_slideLEq]
  simp [Preadditive.add_comp, Preadditive.comp_add]

theorem rel_braid (i j l : I) (ν : X) (h : ¬(i = l ∧ i ≠ j)) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map (relation D Sc (.braid i j l ν h)) = 0 := by
  reduce_rel
  rw [Diagram.dg_braid _ _ _ _ _ _ h]
  simp

theorem rel_zigE (i : I) (ν : X) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map (relation D Sc (.zigE i ν)) = 0 := by
  reduce_rel
  have h : Diagram.dg RD k ν [((true, i) : Letter I)] [(true, i)]
      [([(true, i)], Diagram.Shape.cup (false, i), []), ([], Diagram.Shape.cap (false, i), [(true, i)])] =
        Diagram.dg RD k ν [((true, i) : Letter I)] [(true, i)] [] :=
    Diagram.dg_zigR' RD k ν ((false, i) : Letter I)
  rw [h]
  simp

theorem rel_zigF (i : I) (ν : X) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map (relation D Sc (.zigF i ν)) = 0 := by
  reduce_rel
  rw [Diagram.dg_zigL']
  simp

theorem rel_invNe₁ (i j : I) (ν : X) (hij : i ≠ j) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map (relation D Sc (.invNe₁ i j ν hij)) = 0 := by
  reduce_rel
  rw [Diagram.dg_downupEF _ _ _ _ (Ne.symm hij)]
  simp

theorem rel_invNe₂ (i j : I) (ν : X) (hij : i ≠ j) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map (relation D Sc (.invNe₂ i j ν hij)) = 0 := by
  reduce_rel
  rw [Diagram.dg_downupFE _ _ _ _ hij]
  simp

theorem rel_invP₂ (i : I) (ν : X) (hh : 0 ≤ D.h i ν) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map (relation D Sc (.invP₂ i ν hh)) = 0 := by
  reduce_rel
  have hh' : 0 ≤ Diagram.ip RD i ν := hh
  have h := Diagram.b0a0_EF (k := k) i ν hh'
  rw [Preadditive.comp_neg, Diagram.dg_comp (by schain) (by schain), neg_eq_iff_eq_neg] at h
  rw [h, ← Diagram.dg_nil]
  simp

theorem rel_invM₂ (i : I) (ν : X) (hh : D.h i ν ≤ 0) :
    (StringDiagrams.freeLift k (locMap D C hc k).functor).map (relation D Sc (.invM₂ i ν hh)) = 0 := by
  reduce_rel
  have hh' : Diagram.ip RD i ν ≤ 0 := hh
  have h := Diagram.b0a0_FE (k := k) i ν hh'
  rw [Preadditive.comp_neg, Diagram.dg_comp (by schain) (by schain), neg_eq_iff_eq_neg] at h
  rw [h, ← Diagram.dg_nil]
  simp


end OddMath.SKM.EvenBridge
