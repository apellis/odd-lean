/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PsiInversionRelations
import StringDiagrams.InterchangeLayers

/-!
# Defining relations in the kernel of ψ

Brundan–Ellis, *Super Kac–Moody 2-categories*, Definition 1.5 and Proposition 9.4.
The seven-generator linear evaluation kills the defining tensor ideal, including
every user relation and super-interchange in arbitrary compatible horizontal and
linear vertical contexts. `psiLin_homRel` supplies equality of evaluations for the
existing presentation congruence. Quotient-functor packaging is a separate step.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-- Every defining relation of the presentation is killed by the seven-shape evaluation. -/
theorem psiLin_relation (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (R : Rel D) (ν : X) (hs : wt D R.ν R.dom = ν) (hr : wt D R.ν R.cod = ν) :
    psiLin (sy := sy) (hc := hc) t cs ν R.ν hs hr (relation D Sc R) = 0 := by
  cases R with
  | quadEq i μ => subst ν; exact psiLin_quadEq t ht cs μ i
  | quadZero i j μ hij hd => subst ν; exact psiLin_quadZero t ht cs μ i j hij hd
  | quadNe i j μ hij hd => subst ν; exact psiLin_quadNe t ht cs μ i j hij hd
  | slideL i j μ hij => subst ν; exact psiLin_slideL t ht cs μ i j hij
  | slideR i j μ hij => subst ν; exact psiLin_slideR t ht cs μ i j hij
  | slideLEq i μ => subst ν; exact psiLin_slideLEq t ht cs μ i
  | slideREq i μ => subst ν; exact psiLin_slideREq t ht cs μ i
  | braid i j l μ hij => subst ν; exact psiLin_braid t ht cs μ i j l hij
  | braidEq i j μ hij => subst ν; exact psiLin_braidEq t ht cs μ i j hij
  | zigE i μ => subst ν; exact psiLin_zigE t cs μ i
  | zigF i μ => subst ν; exact psiLin_zigF t cs μ i
  | _ => apply psiLin_inversion t ht cs; trivial

/-- Defining relations vanish between arbitrary linear vertical contexts. -/
theorem psiLin_relation_context (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (R : Rel D) (ν : X) (hs : wt D R.ν R.dom = ν) (hr : wt D R.ν R.cod = ν)
    {a b : List (Letter I)} (ha : wt D R.ν a = ν) (hb : wt D R.ν b = ν)
    (f : LinDiagram k (ob D R.ν a) (ob D R.ν R.dom))
    (g : LinDiagram k (ob D R.ν R.cod) (ob D R.ν b)) :
    psiLin (sy := sy) (hc := hc) t cs ν R.ν ha hb (f ≫ relation D Sc R ≫ g) = 0 := by
  rw [psiLin_comp t cs ν R.ν ha hs hb, psiLin_comp t cs ν R.ν hs hr hb,
    psiLin_relation t ht cs R ν hs hr]
  simp


/-- Each interchange generator of the presentation is killed after boundary retyping. -/
theorem psiLin_interchange (t : k) (cs : CScalars Sc) (ν μ : X)
    (x : InterchangeData (sig D)) (hx : x.Valid) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (ha : x.dom = ob D μ s) (hb : x.cod = ob D μ r) :
    psiLin (sy := sy) (hc := hc) t cs ν μ hs hr
      (LinDiagram.cast (InterchangeData.rel k hx) ha hb) = 0 := by
  have hgh : psiLayers (Diagram.cast (InterchangeData.ghDiagram hx) ha hb) =
      [([], x.g.1, x.mid.map Col.l ++ x.h.1.dom),
        (x.g.1.cod ++ x.mid.map Col.l, x.h.1, [])] := by
    simp only [psiLayers, Diagram.layers_cast, InterchangeData.ghDiagram, Diagram.layers_mk,
      List.map_cons, List.map_nil, InterchangeData.gh₁, InterchangeData.gh₂,
      List.map_append, sig, wd_map_l]
  have hhg : psiLayers (Diagram.cast (InterchangeData.hgDiagram hx) ha hb) =
      [(x.g.1.dom ++ x.mid.map Col.l, x.h.1, []),
        ([], x.g.1, x.mid.map Col.l ++ x.h.1.cod)] := by
    simp only [psiLayers, Diagram.layers_cast, InterchangeData.hgDiagram, Diagram.layers_mk,
      List.map_cons, List.map_nil, InterchangeData.hg₁, InterchangeData.hg₂,
      List.map_append, sig, wd_map_l]
  have hC := psiLayers_chain (Diagram.cast (InterchangeData.ghDiagram hx) ha hb)
  rw [hgh] at hC
  have hsword : s = x.g.1.dom ++ x.mid.map Col.l ++ x.h.1.dom := by
    simpa only [List.nil_append, List.append_assoc] using hC.1
  have hrword : r = x.g.1.cod ++ x.mid.map Col.l ++ x.h.1.cod := by
    simpa only [List.append_nil] using hC.2.2.symm
  subst s r
  simp only [InterchangeData.rel, LinDiagram.cast_sub, LinDiagram.cast_smul,
    LinDiagram.cast_of, map_sub, map_smul, psiLin_single, one_smul, psiDiagram]
  simp only [hgh, hhg]
  have he : (x.sign : k) = zsign k (x.g.1.parity D * x.h.1.parity D) :=
    interchange_sign x.g.1 x.h.1 x.h.2 x.g.2 x.mid x.start
  rw [psiRaw_swap₀, he, sub_self]


/-- All imposed relations, including super-interchange, vanish after boundary retyping. -/
theorem psiLin_allRel (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    (R : (pres D Sc).AllRel) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (ha : R.dom = ob D μ s) (hb : R.cod = ob D μ r) :
    psiLin (sy := sy) (hc := hc) t cs ν μ hs hr (LinDiagram.cast R.rel ha hb) = 0 := by
  cases R with
  | user R =>
    change ob D R.ν R.dom = ob D μ s at ha
    change ob D R.ν R.cod = ob D μ r at hb
    have hμ : R.ν = μ := by
      simpa only [ob_endR] using congrArg Obj.endR ha
    subst μ
    have es := ob_injective ha
    have er := ob_injective hb
    subst s r
    simpa only [Presentation.AllRel.rel, LinDiagram.cast_rfl, pres] using
      psiLin_relation t ht cs R ν hs hr
  | interchange x hx => exact psiLin_interchange t cs ν μ x hx hs hr ha hb

private theorem psiRel_weight (R : Rel D) : wt D R.ν R.cod = wt D R.ν R.dom := by
  cases R <;> simp [Rel.ν, Rel.dom, Rel.cod, wt_cons, sh, up, dn] <;> abel

private theorem psiAllRel_dom_ok (R : (pres D Sc).AllRel) : R.dom.Ok := by
  cases R with
  | user R => exact ok_wd D R.ν R.dom
  | interchange x hx =>
    simpa only [Presentation.AllRel.dom, InterchangeData.dom, InterchangeData.gh₁,
      Layer.dom, List.nil_append, List.append_assoc] using hx.gh₁.dom_obj_ok

private theorem psiAllRel_cod_ok (R : (pres D Sc).AllRel) : R.cod.Ok := by
  cases R with
  | user R => exact ok_wd D R.ν R.cod
  | interchange x hx =>
    simpa only [Presentation.AllRel.cod, InterchangeData.cod, InterchangeData.gh₂,
      Layer.cod, List.append_nil] using hx.gh₂.cod_obj_ok

private theorem psiAllRel_start (R : (pres D Sc).AllRel) : R.cod.start = R.dom.start := by
  cases R with
  | user R => exact psiRel_weight R
  | interchange x hx => rfl

private theorem psiAllRel_endR (R : (pres D Sc).AllRel) : R.cod.endR = R.dom.endR := by
  cases R with
  | user R => exact (ob_endR D R.ν R.cod).trans (ob_endR D R.ν R.dom).symm
  | interchange x hx => exact (Diagram.chain (InterchangeData.ghDiagram hx)).endR_eq


private theorem psiLin_weight_zero (t : k) (cs : CScalars Sc) (ν ν' μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (hs' : wt D μ s = ν') (hr' : wt D μ r = ν') (e : ν = ν')
    (f : LinDiagram k (ob D μ s) (ob D μ r))
    (hf : psiLin (sy := sy) (hc := hc) t cs ν' μ hs' hr' f = 0) :
    psiLin (sy := sy) (hc := hc) t cs ν μ hs hr f = 0 := by
  cases e
  exact hf

private theorem psiWhisker_cast {A B A' B' C E : Obj (sig D)}
    (f : LinDiagram k A B) (ea : A = A') (eb : B = B')
    (u u' : Obj (sig D)) (v v' : List (Col I X)) (eu : u = u') (ev : v = v')
    (hw : A.WhiskerOK u v) (hw' : A'.WhiskerOK u' v')
    (ha : A.whisker u v = C) (hb : B.whisker u v = E)
    (ha' : A'.whisker u' v' = C) (hb' : B'.whisker u' v' = E) :
    LinDiagram.cast (LinDiagram.whisker f u v hw) ha hb =
      LinDiagram.cast (LinDiagram.whisker (LinDiagram.cast f ea eb) u' v' hw') ha' hb' := by
  subst A' B' u' v'
  simp only [LinDiagram.cast_rfl]

/-- Every imposed relation remains in the kernel in any compatible horizontal context. -/
theorem psiLin_allRel_whisker (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    (R : (pres D Sc).AllRel) (u : Obj (sig D)) (v : List (Col I X))
    (hw : R.dom.WhiskerOK u v) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (ha : R.dom.whisker u v = ob D μ s) (hb : R.cod.whisker u v = ob D μ r) :
    psiLin (sy := sy) (hc := hc) t cs ν μ hs hr
      (LinDiagram.cast (LinDiagram.whisker R.rel u v hw) ha hb) = 0 := by
  let a := R.dom.word.map Col.l
  let b := R.cod.word.map Col.l
  let l := u.word.map Col.l
  let q := v.map Col.l
  have he : (sig D).endR R.dom.endR v = μ := by
    have he := (congrArg Obj.endR ha).trans (ob_endR D μ s)
    change (sig D).endR u.start (u.word ++ R.dom.word ++ (show List (sig D).Colour from v)) = μ at he
    rw [Signature.endR_append, Signature.endR_append] at he
    change (sig D).endR ((sig D).endR u.endR R.dom.word) v = μ at he
    rw [hw.2.1] at he
    exact he
  obtain ⟨ev, hv⟩ := word_eq_wd (D := D) R.dom.endR v hw.2.2
  rw [he] at ev hv
  obtain ⟨ewA, eνA⟩ := word_eq_wd (D := D) R.dom.start R.dom.word (psiAllRel_dom_ok R)
  obtain ⟨ewB, eνB⟩ := word_eq_wd (D := D) R.cod.start R.cod.word (psiAllRel_cod_ok R)
  change R.dom.word = wd D R.dom.endR a at ewA
  change R.dom.start = wt D R.dom.endR a at eνA
  change R.cod.word = wd D R.cod.endR b at ewB
  change R.cod.start = wt D R.cod.endR b at eνB
  rw [hv] at ewA eνA
  rw [psiAllRel_endR R, hv] at ewB eνB
  rw [psiAllRel_start R] at eνB
  have eab : wt D (wt D μ q) b = wt D (wt D μ q) a := eνB.symm.trans eνA
  have ea : R.dom = ob D (wt D μ q) a := Obj.ext eνA ewA
  have eb : R.cod = ob D (wt D μ q) b := Obj.ext
    ((psiAllRel_start R).trans eνB) ewB
  obtain ⟨ewu, eνu⟩ := word_eq_wd (D := D) u.start u.word hw.1
  change u.word = wd D u.endR l at ewu
  change u.start = wt D u.endR l at eνu
  rw [hw.2.1, eνA] at ewu eνu
  have eu : u = ob D (wt D (wt D μ q) a) l := Obj.ext eνu ewu
  have es : s = l ++ a ++ q := by
    have e := congrArg (fun z : Obj (sig D) => z.word.map Col.l) ha
    simpa only [Obj.whisker_word, ob_word, List.map_append, wd_map_l] using e.symm
  have er : r = l ++ b ++ q := by
    have e := congrArg (fun z : Obj (sig D) => z.word.map Col.l) hb
    simpa only [Obj.whisker_word, ob_word, List.map_append, wd_map_l] using e.symm
  subst s r
  apply psiLin_weight_zero t cs ν (wt D (wt D (wt D μ q) a) l) μ hs hr
    (by rw [wt_append, wt_append]) (by rw [wt_append, wt_append, eab])
    (hs.symm.trans (by rw [wt_append, wt_append]))
  rw [psiWhisker_cast R.rel ea eb u (ob D (wt D (wt D μ q) a) l) v (wd D μ q) eu ev hw
    (whiskerOK_ob D μ l q a) ha hb (ob_whisker D μ l q a a rfl) (ob_whisker D μ l q a b eab)]
  rw [psiLin_place t cs μ l q a b eab,
    psiLin_allRel t ht cs _ _ R rfl eab ea eb, map_zero]


private theorem psiObj_normal (A : Obj (sig D)) (hA : A.Ok) (μ : X) (he : A.endR = μ) :
    A = ob D μ (A.word.map Col.l) := by
  obtain ⟨hw, hs⟩ := word_eq_wd (D := D) A.start A.word hA
  change A.word = wd D A.endR (A.word.map Col.l) at hw
  change A.start = wt D A.endR (A.word.map Col.l) at hs
  rw [he] at hw hs
  exact Obj.ext hs hw

private theorem psiDiagram_cod_normal {μ : X} {s : List (Letter I)} {A : Obj (sig D)}
    (d : ob D μ s ⟶ A) : A = ob D μ (A.word.map Col.l) :=
  psiObj_normal A ((Diagram.chain d).ok (ok_wd D μ s)) μ
    ((Diagram.chain d).endR_eq.trans (ob_endR D μ s))

private theorem psiDiagram_dom_normal {μ : X} {s : List (Letter I)} {A : Obj (sig D)}
    (d : A ⟶ ob D μ s) : A = ob D μ (A.word.map Col.l) := by
  have hA : A.Ok := by
    have hc := Diagram.chain d
    cases he : d.layers with
    | nil => rw [he] at hc; cases hc; exact ok_wd D μ s
    | cons L ls => rw [he] at hc; exact hc.2.1 ▸ hc.1.dom_obj_ok
  exact psiObj_normal A hA μ ((Diagram.chain d).endR_eq.symm.trans (ob_endR D μ s))

private theorem psiSandwich_cast {A B A' B' C E : Obj (sig D)}
    (pre : LinDiagram k C A) (f : LinDiagram k A B) (post : LinDiagram k B E)
    (ea : A = A') (eb : B = B') :
    pre ≫ f ≫ post = LinDiagram.cast pre rfl ea ≫ LinDiagram.cast f ea eb ≫
      LinDiagram.cast post eb rfl := by
  subst A' B'
  simp only [LinDiagram.cast_rfl]

/-- Every generator of the presentation's tensor ideal is killed by linear evaluation. -/
theorem psiLin_idealGen (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    (R : (pres D Sc).AllRel) (u : Obj (sig D)) (v : List (Col I X))
    (hw : R.dom.WhiskerOK u v) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (pre : LinDiagram k (ob D μ s) (R.dom.whisker u v))
    (post : LinDiagram k (R.cod.whisker u v) (ob D μ r)) :
    psiLin (sy := sy) (hc := hc) t cs ν μ hs hr
      (pre ≫ LinDiagram.whisker R.rel u v hw ≫ post) = 0 := by
  induction pre using Finsupp.induction_linear with
  | zero => simp
  | add f f' ih ih' =>
    erw [Preadditive.add_comp]
    simp only [map_add, ih, ih', add_zero]
  | single d c =>
    induction post using Finsupp.induction_linear with
    | zero => simp
    | add g g' ih ih' =>
      erw [Preadditive.comp_add, Preadditive.comp_add]
      simp only [map_add, ih, ih', add_zero]
    | single e c' =>
      have ea := psiDiagram_cod_normal d
      have eb := psiDiagram_dom_normal e
      have hma : wt D μ ((R.dom.whisker u v).word.map Col.l) = ν :=
        (congrArg Obj.start ea).symm.trans ((Diagram.chain d).start_eq.trans hs)
      have hmb : wt D μ ((R.cod.whisker u v).word.map Col.l) = ν :=
        (congrArg Obj.start eb).symm.trans ((Diagram.chain e).start_eq.symm.trans hr)
      rw [psiSandwich_cast _ _ _ ea eb]
      rw [psiLin_comp t cs ν μ hs hma hr, psiLin_comp t cs ν μ hma hmb hr,
        psiLin_allRel_whisker t ht cs ν μ R u v hw hma hmb ea eb]
      simp

/-- The entire defining tensor ideal lies in the kernel of the seven-generator evaluation. -/
theorem psiLin_ideal (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    {f : LinDiagram k (ob D μ s) (ob D μ r)}
    (hf : f ∈ (pres D Sc).ideal (ob D μ s) (ob D μ r)) :
    psiLin (sy := sy) (hc := hc) t cs ν μ hs hr f = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨R, u, v, hw, pre, post⟩ := hf
    exact psiLin_idealGen t ht cs ν μ R u v hw hs hr pre post
  | zero => exact map_zero _
  | add f g _ _ ih ih' => rw [map_add, ih, ih', add_zero]
  | smul c f _ ih => rw [map_smul, ih, smul_zero]


/-- The linear evaluation respects the congruence defining the presented category. -/
theorem psiLin_homRel (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    {f g : LinDiagram k (ob D μ s) (ob D μ r)} (hfg : (pres D Sc).homRel f g) :
    psiLin (sy := sy) (hc := hc) t cs ν μ hs hr f = psiLin t cs ν μ hs hr g := by
  have h := psiLin_ideal (sy := sy) (hc := hc) t ht cs ν μ hs hr hfg
  rw [map_sub, sub_eq_zero] at h
  exact h

end OddMath.SKM
