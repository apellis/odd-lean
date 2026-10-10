/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Presentation

/-!
# A calculus of local rewriting for normal-form diagrams of `𝔘(𝔤)`

Diagrams of `𝔘(𝔤)` in normal form (`mkD D μ ls h`, a list of layers `(u, g, v)` with rightmost
region `μ`; `OddMath.SKM.Basic`) are manipulated by local moves: a subdiagram, placed between
strands `u` and `v`, is replaced by an equal linear combination of subdiagrams. This file provides
the placement map, the rewriting principle and the super interchange law in normal form:

* `whL u v`: a layer datum placed between the strands `u` and `v`;
* `plc`, `plcL`: the `k`-linear map placing a 2-morphism between the strands `u` and `v`
  (whiskering in the presented category); on normal-form diagrams it acts by `whL u v`;
* `cl D Sc μ s t ls`: the class of the normal-form diagram with layers `ls` (or `0` if they do
  not chain from `s` to `t`), with `cl_comp`, `cl_nil`;
* `ctxL`, `ctxL_cl`, `cl_rw`, `cl_step`, `cl_stepL`: rewriting in context;
* `cl_swap`: the super interchange law for two adjacent layers,
  `(g on the left, then h on the right) = (-1)^{|g||h|} (h, then g)` (Brundan–Ellis, (1.1)–(1.3)).

The structure follows the even calculus of categorification-lean (`KL3.SlideCalculus`); the
only new ingredient is the Koszul sign of the interchange law.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X) {k : Type w} [CommRing k]
  (Sc : Scalars D k)

@[simp] theorem ob_start (μ : X) (t : List (Letter I)) : (ob D μ t).start = wt D μ t := rfl
@[simp] theorem ob_word (μ : X) (t : List (Letter I)) : (ob D μ t).word = wd D μ t := rfl

theorem ob_endR (μ : X) (t : List (Letter I)) : (ob D μ t).endR = μ := endR_wd D μ t

theorem wt_lay_dom (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    wt D μ (u ++ g.dom ++ v) = wt D μ (u ++ g.cod ++ v) := by
  simp only [List.append_assoc, wt_append, Shape.wt_dom_eq_wt_cod]

/-! ## The sign `(-1)^p` -/

theorem zsign_add {k : Type*} [CommRing k] (p q : ZMod 2) :
    zsign k (p + q) = zsign k p * zsign k q := by
  have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hz p with rfl | rfl <;> rcases hz q with rfl | rfl <;> simp [zsign]

theorem zsign_zero {k : Type*} [CommRing k] : zsign k 0 = 1 := by simp [zsign]

theorem zsign_natCast_mul {k : Type*} [CommRing k] (n : ℕ) (p : ZMod 2) :
    zsign k (p * n) = zsign k p ^ n := by
  induction n with
  | zero => simp [zsign_zero]
  | succ n ih => rw [Nat.cast_succ, mul_add, mul_one, zsign_add, ih, pow_succ]

/-! ## Whiskering of layer data -/

/-- The layer datum `x` placed between the strands `u` (left) and `v` (right). -/
def whL (u v : List (Letter I)) (x : LayerData I) : LayerData I := (u ++ x.1, x.2.1, x.2.2 ++ v)

@[simp] theorem whL_nil_nil (x : LayerData I) : whL [] [] x = x := by
  obtain ⟨a, g, b⟩ := x; simp [whL]

@[simp] theorem whL_whL (u v u' v' : List (Letter I)) (x : LayerData I) :
    whL u v (whL u' v' x) = whL (u ++ u') (v' ++ v) x := by
  obtain ⟨a, g, b⟩ := x; simp [whL]

@[simp] theorem map_whL_map_whL (u v u' v' : List (Letter I)) (L : List (LayerData I)) :
    (L.map (whL u' v')).map (whL u v) = L.map (whL (u ++ u') (v' ++ v)) := by
  simp [List.map_map, Function.comp_def]

theorem SChain.nil' (s : List (Letter I)) : SChain s [] s := rfl

theorem SChain.whisk {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t)
    (u v : List (Letter I)) : SChain (u ++ s ++ v) (ls.map (whL u v)) (u ++ t ++ v) := by
  induction ls generalizing s with
  | nil => cases h; rfl
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    refine ⟨by simp [whL], ?_⟩
    have := ih h
    simpa [whL] using this

/-- The weight of the left region is constant along a chain of layers. -/
theorem SChain.wt_eq (ν : X) {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    wt D ν t = wt D ν s := by
  induction ls generalizing s with
  | nil => cases h; rfl
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    rw [ih h, wt_lay_dom]

theorem SChain.wt_mem (ν : X) {s t : List (Letter I)} {ls : List (LayerData I)}
    (h : SChain s ls t) : ∀ x ∈ ls, wt D ν (x.1 ++ x.2.1.dom ++ x.2.2) = wt D ν s := by
  induction ls generalizing s with
  | nil => simp
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · rfl
    · rw [ih h y hy, wt_lay_dom]

theorem SChain.eq_target {s t t' : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t)
    (h' : SChain s ls t') : t = t' := by
  induction ls generalizing s with
  | nil => exact h.symm.trans h'
  | cons x ls ih => exact ih h.2 h'.2

theorem SChain.eq_source {b b' t : List (Letter I)} {ls : List (LayerData I)} (h : SChain b ls t)
    (h' : SChain b' ls t) : b = b' := by
  cases ls with
  | nil => exact h.trans h'.symm
  | cons x ls => exact h.1.trans h'.1.symm

theorem SChain.split {s t : List (Letter I)} {ls ms : List (LayerData I)}
    (h : SChain s (ls ++ ms) t) : ∃ a, SChain s ls a ∧ SChain a ms t := by
  induction ls generalizing s with
  | nil => exact ⟨s, rfl, h⟩
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    obtain ⟨a, h₁, h₂⟩ := ih h
    exact ⟨a, ⟨rfl, h₁⟩, h₂⟩

theorem SChain.of_whisk {u v s t : List (Letter I)} {ls : List (LayerData I)}
    (h : SChain (u ++ s ++ v) (ls.map (whL u v)) (u ++ t ++ v)) : SChain s ls t := by
  induction ls generalizing s with
  | nil =>
    have h' : u ++ s ++ v = u ++ t ++ v := h
    simpa using h'
  | cons x ls ih =>
    obtain ⟨h₁, h₂⟩ := h
    have e : s = x.1 ++ x.2.1.dom ++ x.2.2 := by
      have h₁' : u ++ (s ++ v) = u ++ ((x.1 ++ x.2.1.dom ++ x.2.2) ++ v) := by
        simpa [whL, List.append_assoc] using h₁
      exact List.append_cancel_right (List.append_cancel_left h₁')
    subst e
    refine ⟨rfl, ih ?_⟩
    simpa [whL] using h₂

/-- A placed layer in normal form. -/
theorem lay_whisker (μ : X) (u v a : List (Letter I)) (g : Shape I) (b s : List (Letter I))
    (hs : wt D (wt D μ v) (a ++ g.dom ++ b) = wt D (wt D μ v) s) :
    (lay D (wt D μ v) a g b).whisker (ob D (wt D (wt D μ v) s) u) (wd D μ v) =
      lay D μ (u ++ a) g (b ++ v) := by
  have hs' : wt D (wt D (wt D μ v) (g.dom ++ b)) a = wt D (wt D μ v) s := by
    rw [← wt_append, ← List.append_assoc]; exact hs
  refine Layer.ext ?_ ?_ ?_ ?_
  · simp only [Layer.whisker, ob_start, lay, List.append_assoc, wt_append] at hs ⊢
    rw [hs]
  · simp only [wt_append] at hs'
    simp only [Layer.whisker, ob_word, lay, List.append_assoc, wd_append, wt_append]
    rw [hs']
  · simp only [Layer.whisker, lay, wt_append]
  · simp only [Layer.whisker, lay, wd_append]

theorem layList_whisker (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    {ls : List (LayerData I)} (h : SChain s ls t) :
    (layList D (wt D μ v) ls).map (·.whisker (ob D (wt D (wt D μ v) s) u) (wd D μ v)) =
      layList D μ (ls.map (whL u v)) := by
  have hm := h.wt_mem D (wt D μ v)
  simp only [layList, List.map_map]
  refine List.map_congr_left fun x hx => ?_
  exact lay_whisker D μ u v x.1 x.2.1 x.2.2 s (hm x hx)

/-! ## Placement -/

theorem whiskerOK_ob (μ : X) (u v s : List (Letter I)) :
    (ob D (wt D μ v) s).WhiskerOK (ob D (wt D (wt D μ v) s) u) (wd D μ v) :=
  ⟨ok_wd D _ u, endR_wd D _ u, by rw [ob_endR]; exact ok_wd D μ v⟩

theorem ob_whisker (μ : X) (u v s s' : List (Letter I))
    (hs : wt D (wt D μ v) s' = wt D (wt D μ v) s) :
    (ob D (wt D μ v) s').whisker (ob D (wt D (wt D μ v) s) u) (wd D μ v) =
      ob D μ (u ++ s' ++ v) := by
  refine Obj.ext ?_ ?_
  · simp only [Obj.whisker_start, ob_start, List.append_assoc, wt_append, hs]
  · simp only [Obj.whisker_word, ob_word, List.append_assoc, wd_append, wt_append, hs]

/-- **Placement.** The `k`-linear map placing a 2-morphism `E_s 1_ν ⟶ E_t 1_ν`, with
`ν = μ + wt(v)`, between the strands `u` and `v`; the rightmost region becomes `μ`. -/
def plc (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    (hst : wt D (wt D μ v) t = wt D (wt D μ v) s) :
    ((pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)) →ₗ[k]
      ((pres D Sc).obj (ob D μ (u ++ s ++ v)) ⟶ (pres D Sc).obj (ob D μ (u ++ t ++ v))) where
  toFun f := eqToHom (congrArg (pres D Sc).obj (ob_whisker D μ u v s s rfl).symm) ≫
    (pres D Sc).whisk f (ob D (wt D (wt D μ v) s) u) (wd D μ v) ≫
      eqToHom (congrArg (pres D Sc).obj (ob_whisker D μ u v s t hst))
  map_add' f g := by
    rw [Presentation.whisk_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    rw [Presentation.whisk_smul, Linear.smul_comp, Linear.comp_smul]; rfl

/-- Placement acts on normal-form diagrams by placing every layer. -/
theorem plc_diag (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    (hst : wt D (wt D μ v) t = wt D (wt D μ v) s) (ls : List (LayerData I))
    (h : SChain s ls t) :
    plc D Sc μ u v hst ((pres D Sc).diag (mkD D (wt D μ v) ls h)) =
      (pres D Sc).diag (mkD D μ (ls.map (whL u v)) (h.whisk u v)) := by
  simp only [plc, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Presentation.whisk_diag _ _ _ _ (whiskerOK_ob D μ u v s)]
  rw [(pres D Sc).diag_eq_of_layers_eq' (mkD D μ (ls.map (whL u v)) (h.whisk u v))
    (Diagram.whisker (mkD D (wt D μ v) ls h) (ob D (wt D (wt D μ v) s) u) (wd D μ v)
      (whiskerOK_ob D μ u v s)) (ob_whisker D μ u v s s rfl).symm
      (ob_whisker D μ u v s t hst).symm ?_]
  rw [Diagram.layers_whisker, layers_mkD, layers_mkD, layList_whisker D μ u v h]

/-! ## Diagram classes without typing proofs -/

open Classical in
/-- The class in `𝔘(𝔤)` of the normal-form diagram with layers `ls` from `E_s 1_μ` to
`E_t 1_μ` (rightmost region `μ`), or `0` if the layers do not form such a diagram. -/
def cl (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t) :=
  if h : SChain s ls t then (pres D Sc).diag (mkD D μ ls h) else 0

variable {D Sc}

theorem cl_of {μ : X} {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    cl D Sc μ s t ls = (pres D Sc).diag (mkD D μ ls h) := dite_eq_left h

theorem cl_of_not {μ : X} {s t : List (Letter I)} {ls : List (LayerData I)}
    (h : ¬ SChain s ls t) : cl D Sc μ s t ls = 0 := dite_eq_right h

theorem cl_nil (μ : X) (s : List (Letter I)) : cl D Sc μ s s [] = 𝟙 _ := by
  rw [cl_of (show SChain s [] s from rfl)]
  exact ((pres D Sc).diag_eq_of_layers_eq rfl).trans ((pres D Sc).diag_id _)

theorem cl_comp {μ : X} {s t r : List (Letter I)} {A B : List (LayerData I)} (hA : SChain s A t)
    (hB : SChain t B r) : cl D Sc μ s t A ≫ cl D Sc μ t r B = cl D Sc μ s r (A ++ B) := by
  rw [cl_of hA, cl_of hB, cl_of (hA.append hB), ← Presentation.diag_comp, mkD_comp]

/-- The relations of `pres` in terms of classes: `lin (dg ...) = cl ...`. -/
theorem lin_dg {μ : X} {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    (pres D Sc).lin (dg (k := k) D μ ls h) = cl D Sc μ s t ls := by
  rw [cl_of h]; rfl

variable (D Sc)

open Classical in
/-- Placement between the strands `u` and `v`, as a `k`-linear map on all morphisms
`E_s 1_ν ⟶ E_t 1_ν` (`ν = μ + wt(v)`); it is `0` if `s` and `t` have different weights. -/
def plcL (μ : X) (u v s t : List (Letter I)) :
    ((pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)) →ₗ[k]
      ((pres D Sc).obj (ob D μ (u ++ s ++ v)) ⟶ (pres D Sc).obj (ob D μ (u ++ t ++ v))) :=
  if h : wt D (wt D μ v) t = wt D (wt D μ v) s then plc D Sc μ u v h else 0

theorem plcL_cl (μ : X) (u v s t : List (Letter I)) (A : List (LayerData I)) :
    plcL D Sc μ u v s t (cl D Sc (wt D μ v) s t A) =
      cl D Sc μ (u ++ s ++ v) (u ++ t ++ v) (A.map (whL u v)) := by
  by_cases hA : SChain s A t
  · rw [plcL, dite_eq_left (hA.wt_eq D _), cl_of hA, plc_diag, cl_of]
  · rw [cl_of_not hA, map_zero, cl_of_not (fun h => hA h.of_whisk)]

/-- **Rewriting in context**, as a `k`-linear map: place a 2-morphism `E_s 1_ν ⟶ E_t 1_ν`
(`ν = μ + wt(v)`) between the strands `u` and `v` and compose with the normal-form diagrams
`pre` below and `post` above. -/
def ctxL (μ : X) (s₀ t₀ : List (Letter I)) (pre : List (LayerData I)) (u v : List (Letter I))
    (post : List (LayerData I)) (s t : List (Letter I)) :
    ((pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)) →ₗ[k]
      ((pres D Sc).obj (ob D μ s₀) ⟶ (pres D Sc).obj (ob D μ t₀)) where
  toFun f := cl D Sc μ s₀ (u ++ s ++ v) pre ≫ plcL D Sc μ u v s t f ≫
    cl D Sc μ (u ++ t ++ v) t₀ post
  map_add' f g := by
    rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

variable {D Sc}

/-- Rewriting in context acts on normal-form diagrams by concatenation of layers. -/
theorem ctxL_cl (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u v : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (A : List (LayerData I)) :
    ctxL D Sc μ s₀ t₀ pre u v post s t (cl D Sc (wt D μ v) s t A) =
      cl D Sc μ s₀ t₀ (pre ++ A.map (whL u v) ++ post) := by
  show cl D Sc μ s₀ (u ++ s ++ v) pre ≫ plcL D Sc μ u v s t _ ≫
    cl D Sc μ (u ++ t ++ v) t₀ post = _
  rw [plcL_cl]
  by_cases hA : SChain s A t
  · rw [cl_comp (hA.whisk u v) hpost, cl_comp hpre ((hA.whisk u v).append hpost),
      List.append_assoc]
  · rw [cl_of_not (fun h => hA h.of_whisk), Limits.zero_comp, Limits.comp_zero, cl_of_not]
    intro h
    obtain ⟨a, h₁, h₂⟩ := SChain.split h
    obtain ⟨b, h₃, h₄⟩ := SChain.split h₁
    obtain rfl := h₃.eq_target hpre
    obtain rfl := h₂.eq_source hpost
    exact hA h₄.of_whisk

/-- **The rewriting principle.** If `cl ν s t A = F` (`ν = μ + wt(v)`), then the diagram
`pre ++ A ++ post`, with `A` placed between the strands `u` and `v`, equals the image of `F`
under `ctxL`. -/
theorem cl_rw (μ : X) {s₀ t₀ : List (Letter I)} {pre : List (LayerData I)}
    {u v : List (Letter I)} {post : List (LayerData I)} {s t : List (Letter I)}
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    {A : List (LayerData I)} {F : (pres D Sc).obj (ob D (wt D μ v) s) ⟶
      (pres D Sc).obj (ob D (wt D μ v) t)} (E : cl D Sc (wt D μ v) s t A = F) :
    cl D Sc μ s₀ t₀ (pre ++ A.map (whL u v) ++ post) = ctxL D Sc μ s₀ t₀ pre u v post s t F := by
  rw [← E, ctxL_cl μ hpre hpost]

/-- **One step of a certificate chain.** If `cl ν s t A = cl ν s t B` (`ν = μ + wt(v)`), then in
any diagram in which `A` occurs between the strands `u` and `v`, `A` may be replaced by `B`. -/
theorem cl_step (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A B L L' : List (LayerData I)}
    (E : cl D Sc (wt D μ v) s t A = cl D Sc (wt D μ v) s t B)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (hL : L = pre ++ A.map (whL u v) ++ post) (hL' : L' = pre ++ B.map (whL u v) ++ post) :
    cl D Sc μ s₀ t₀ L = cl D Sc μ s₀ t₀ L' := by
  rw [hL, hL', cl_rw μ hpre hpost E, ctxL_cl μ hpre hpost]

/-- One step of a certificate chain whose right-hand side is a linear combination. -/
theorem cl_stepL (μ : X) {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A L : List (LayerData I)}
    {F : (pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)}
    (E : cl D Sc (wt D μ v) s t A = F)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (hL : L = pre ++ A.map (whL u v) ++ post) :
    cl D Sc μ s₀ t₀ L = ctxL D Sc μ s₀ t₀ pre u v post s t F := by
  rw [hL, cl_rw μ hpre hpost E]

/-! ## The super interchange law in normal form -/

theorem interchange_sign (g h : Shape I) (ν ν' : X) (m : List (Col I X)) (r : X) :
    (((⟨r, (g, ν'), m, (h, ν)⟩ : InterchangeData (sig D)).sign : ℤ) : k) =
      zsign k (g.parity D * h.parity D) := by
  simp only [InterchangeData.sign, sig, zsign]
  have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hz (g.parity D) with ha | ha <;> rcases hz (h.parity D) with hb | hb <;>
    simp [ha, hb]

variable (D Sc) in
/-- The super interchange law for two adjacent layers with empty outer context: the generator
`g` on the left, the strands `m`, the generator `h` on the right. -/
theorem swap_diag₀ (ν : X) (m : List (Letter I)) (g h : Shape I) {s t : List (Letter I)}
    (H₁ : SChain s [([], g, m ++ h.dom), (g.cod ++ m, h, [])] t)
    (H₂ : SChain s [(g.dom ++ m, h, []), ([], g, m ++ h.cod)] t) :
    (pres D Sc).diag (mkD D ν _ H₁) =
      zsign k (g.parity D * h.parity D) • (pres D Sc).diag (mkD D ν _ H₂) := by
  obtain ⟨rfl, -, rfl⟩ := H₁
  have hm : wt D ν (m ++ h.cod) = wt D ν (m ++ h.dom) := by
    rw [wt_append, wt_append, Shape.wt_dom_eq_wt_cod]
  let x : InterchangeData (sig D) :=
    ⟨(wt D ν (g.dom ++ m ++ h.dom) : X), (g, wt D ν (m ++ h.dom)), wd D (wt D ν h.dom) m,
      (h, ν)⟩
  have e₁ : x.gh₁ = lay D ν [] g (m ++ h.dom) := by
    refine Layer.ext ?_ ?_ ?_ ?_ <;>
      simp [x, InterchangeData.gh₁, lay, sig, wd_append, wt_append]
  have e₂ : x.gh₂ = lay D ν (g.cod ++ m) h [] := by
    refine Layer.ext ?_ ?_ ?_ ?_ <;>
      simp [x, InterchangeData.gh₂, lay, sig, wd_append, wt_append, Shape.wt_dom_eq_wt_cod]
  have e₃ : x.hg₁ = lay D ν (g.dom ++ m) h [] := by
    refine Layer.ext ?_ ?_ ?_ ?_ <;>
      simp [x, InterchangeData.hg₁, lay, sig, wd_append, wt_append]
  have e₄ : x.hg₂ = lay D ν [] g (m ++ h.cod) := by
    refine Layer.ext ?_ ?_ ?_ ?_
    · simp [x, InterchangeData.hg₂, lay, wt_append, Shape.wt_dom_eq_wt_cod]
    · simp [x, InterchangeData.hg₂, lay]
    · simp only [x, InterchangeData.hg₂, lay, hm]
    · simp [x, InterchangeData.hg₂, lay, sig, wd_append, wt_append, Shape.wt_dom_eq_wt_cod]
  have hx : x.Valid := ⟨e₁ ▸ lay_valid D _ _ _ _, e₂ ▸ lay_valid D _ _ _ _,
    e₃ ▸ lay_valid D _ _ _ _, e₄ ▸ lay_valid D _ _ _ _⟩
  have hw : x.dom.WhiskerOK (Obj.nil x.start) [] := ⟨trivial, rfl, by
    show (sig D).ok (x.dom.endR) []
    trivial⟩
  have key := (pres D Sc).diag_interchange x hx (Obj.nil x.start) [] hw rfl rfl
  rw [interchange_sign] at key
  have ha : ob D ν ([] ++ g.dom ++ (m ++ h.dom)) = x.dom.whisker (Obj.nil x.start) [] := by
    refine Obj.ext ?_ ?_
    · simp [x, ob]
    · simp [x, ob, InterchangeData.dom, Obj.whisker, sig, wd_append, wt_append]
  have hb : ob D ν (g.cod ++ m ++ h.cod ++ []) = x.cod.whisker (Obj.nil x.start) [] := by
    refine Obj.ext ?_ ?_
    · simp [x, ob, wt_append, Shape.wt_dom_eq_wt_cod]
    · simp [x, ob, InterchangeData.cod, Obj.whisker, sig, wd_append, wt_append,
        Shape.wt_dom_eq_wt_cod]
  rw [(pres D Sc).diag_eq_of_layers_eq' (mkD D ν _ _) (Diagram.cast
      (Diagram.whisker (InterchangeData.ghDiagram hx) (Obj.nil x.start) [] hw) rfl rfl) ha hb ?_,
    (pres D Sc).diag_eq_of_layers_eq' (mkD D ν _ H₂) (Diagram.cast
      (Diagram.whisker (InterchangeData.hgDiagram hx) (Obj.nil x.start) [] hw) rfl rfl) ha hb ?_,
    key, Linear.smul_comp, Linear.comp_smul]
  · simp only [layers_mkD, layList, List.map_cons, List.map_nil, Diagram.layers_cast,
      Diagram.layers_whisker, InterchangeData.hgDiagram, Diagram.layers_mk, ← e₃, ← e₄]
    simp [Layer.whisker]
    exact ⟨rfl, rfl⟩
  · simp only [layers_mkD, layList, List.map_cons, List.map_nil, Diagram.layers_cast,
      Diagram.layers_whisker, InterchangeData.ghDiagram, Diagram.layers_mk, ← e₁, ← e₂]
    simp [Layer.whisker]
    exact ⟨rfl, rfl⟩

theorem cl_swap₀ (ν : X) (m : List (Letter I)) (g h : Shape I) {s t : List (Letter I)} :
    cl D Sc ν s t [([], g, m ++ h.dom), (g.cod ++ m, h, [])] =
      zsign k (g.parity D * h.parity D) • cl D Sc ν s t [(g.dom ++ m, h, []), ([], g, m ++ h.cod)] := by
  by_cases H₁ : SChain s [([], g, m ++ h.dom), (g.cod ++ m, h, [])] t
  · have H₂ : SChain s [(g.dom ++ m, h, []), ([], g, m ++ h.cod)] t := by
      obtain ⟨rfl, -, rfl⟩ := H₁
      simp
    rw [cl_of H₁, cl_of H₂]
    exact swap_diag₀ D Sc ν m g h H₁ H₂
  · have H₂ : ¬ SChain s [(g.dom ++ m, h, []), ([], g, m ++ h.cod)] t := by
      intro H; apply H₁
      obtain ⟨rfl, -, rfl⟩ := H
      simp
    rw [cl_of_not H₁, cl_of_not H₂, smul_zero]

/-- **The super interchange law in normal form** (Brundan–Ellis, (1.3)): two adjacent layers
whose generators `g` (left) and `h` (right) are separated by the strands `m` can be exchanged,
at the cost of the sign `(-1)^{|g||h|}`. -/
theorem cl_swap (μ : X) (s t a m b : List (Letter I)) (g h : Shape I) :
    cl D Sc μ s t [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] =
      zsign k (g.parity D * h.parity D) •
        cl D Sc μ s t [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] := by
  have i₁ : SChain s [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] t ↔
      s = a ++ (g.dom ++ m ++ h.dom) ++ b ∧ t = a ++ (g.cod ++ m ++ h.cod) ++ b := by
    simp only [sChain_cons, sChain_nil, List.append_assoc, true_and]
    exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
  have i₂ : SChain s [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] t ↔
      s = a ++ (g.dom ++ m ++ h.dom) ++ b ∧ t = a ++ (g.cod ++ m ++ h.cod) ++ b := by
    simp only [sChain_cons, sChain_nil, List.append_assoc, true_and]
    exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
  by_cases hc : s = a ++ (g.dom ++ m ++ h.dom) ++ b ∧ t = a ++ (g.cod ++ m ++ h.cod) ++ b
  · obtain ⟨rfl, rfl⟩ := hc
    have E := congrArg (ctxL D Sc μ (a ++ (g.dom ++ m ++ h.dom) ++ b)
      (a ++ (g.cod ++ m ++ h.cod) ++ b) [] a b [] _ _) (cl_swap₀ (D := D) (Sc := Sc) (s := g.dom ++ m ++ h.dom) (t := g.cod ++ m ++ h.cod) (wt D μ b) m g h)
    rw [map_smul, ctxL_cl μ (SChain.nil' _) (SChain.nil' _),
      ctxL_cl μ (SChain.nil' _) (SChain.nil' _)] at E
    simpa [whL] using E
  · rw [cl_of_not (fun h' => hc (i₁.1 h')), cl_of_not (fun h' => hc (i₂.1 h')), smul_zero]

end OddMath.SKM
