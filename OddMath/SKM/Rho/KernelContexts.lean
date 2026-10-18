import OddMath.SKM.Rho.Interchange
import StringDiagrams.InterchangeLayers

/-!
# Kernel Contexts for ρ

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

private theorem rhoRel_weight (R : Rel D) : wt D R.ν R.cod = wt D R.ν R.dom := by
  cases R <;> simp [Rel.ν, Rel.dom, Rel.cod, wt_cons, sh, up, dn] <;> abel

private theorem rhoAllRel_dom_ok (R : (pres D Sc).AllRel) : R.dom.Ok := by
  cases R with
  | user R => exact ok_wd D R.ν R.dom
  | interchange x hx =>
    simpa only [Presentation.AllRel.dom, InterchangeData.dom, InterchangeData.gh₁,
      Layer.dom, List.nil_append, List.append_assoc] using hx.gh₁.dom_obj_ok

private theorem rhoAllRel_cod_ok (R : (pres D Sc).AllRel) : R.cod.Ok := by
  cases R with
  | user R => exact ok_wd D R.ν R.cod
  | interchange x hx =>
    simpa only [Presentation.AllRel.cod, InterchangeData.cod, InterchangeData.gh₂,
      Layer.cod, List.append_nil] using hx.gh₂.cod_obj_ok

private theorem rhoAllRel_start (R : (pres D Sc).AllRel) : R.cod.start = R.dom.start := by
  cases R with
  | user R => exact rhoRel_weight R
  | interchange x hx => rfl

private theorem rhoAllRel_endR (R : (pres D Sc).AllRel) : R.cod.endR = R.dom.endR := by
  cases R with
  | user R => exact (ob_endR D R.ν R.cod).trans (ob_endR D R.ν R.dom).symm
  | interchange x hx => exact (Diagram.chain (InterchangeData.ghDiagram hx)).endR_eq

private theorem rhoLin_weight_zero (t : k) (ν ν' μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (hs' : wt D μ s = ν') (hr' : wt D μ r = ν') (e : ν = ν')
    (f : LinDiagram k (ob D μ s) (ob D μ r))
    (hf : rhoLin (sy := sy) (hc := hc) t ν' μ hs' hr' f = 0) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hr f = 0 := by
  cases e
  exact hf

private theorem rhoWhisker_cast {A B A' B' C E : Obj (sig D)}
    (f : LinDiagram k A B) (ea : A = A') (eb : B = B')
    (u u' : Obj (sig D)) (v v' : List (Col I X)) (eu : u = u') (ev : v = v')
    (hw : A.WhiskerOK u v) (hw' : A'.WhiskerOK u' v')
    (ha : A.whisker u v = C) (hb : B.whisker u v = E)
    (ha' : A'.whisker u' v' = C) (hb' : B'.whisker u' v' = E) :
    LinDiagram.cast (LinDiagram.whisker f u v hw) ha hb =
      LinDiagram.cast (LinDiagram.whisker (LinDiagram.cast f ea eb) u' v' hw') ha' hb' := by
  subst A' B' u' v'
  simp only [LinDiagram.cast_rfl]

theorem rhoLin_allRel_whisker (t : k) (ν μ : X)
    (R : (pres D Sc).AllRel)
    (hR : ∀ (ν μ : X) {s r : List (Letter I)}
      (hs : wt D μ s = ν) (hr : wt D μ r = ν)
      (ha : R.dom = ob D μ s) (hb : R.cod = ob D μ r),
      rhoLin (sy := sy) (hc := hc) t ν μ hs hr (LinDiagram.cast R.rel ha hb) = 0)
    (u : Obj (sig D)) (v : List (Col I X))
    (hw : R.dom.WhiskerOK u v) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (ha : R.dom.whisker u v = ob D μ s) (hb : R.cod.whisker u v = ob D μ r) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hr
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
  obtain ⟨ewA, eνA⟩ := word_eq_wd (D := D) R.dom.start R.dom.word (rhoAllRel_dom_ok R)
  obtain ⟨ewB, eνB⟩ := word_eq_wd (D := D) R.cod.start R.cod.word (rhoAllRel_cod_ok R)
  change R.dom.word = wd D R.dom.endR a at ewA
  change R.dom.start = wt D R.dom.endR a at eνA
  change R.cod.word = wd D R.cod.endR b at ewB
  change R.cod.start = wt D R.cod.endR b at eνB
  rw [hv] at ewA eνA
  rw [rhoAllRel_endR R, hv] at ewB eνB
  rw [rhoAllRel_start R] at eνB
  have eab : wt D (wt D μ q) b = wt D (wt D μ q) a := eνB.symm.trans eνA
  have ea : R.dom = ob D (wt D μ q) a := Obj.ext eνA ewA
  have eb : R.cod = ob D (wt D μ q) b := Obj.ext
    ((rhoAllRel_start R).trans eνB) ewB
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
  apply rhoLin_weight_zero t ν (wt D (wt D (wt D μ q) a) l) μ hs hr
    (by rw [wt_append, wt_append]) (by rw [wt_append, wt_append, eab])
    (hs.symm.trans (by rw [wt_append, wt_append]))
  rw [rhoWhisker_cast R.rel ea eb u (ob D (wt D (wt D μ q) a) l) v (wd D μ q) eu ev hw
    (whiskerOK_ob D μ l q a) ha hb (ob_whisker D μ l q a a rfl) (ob_whisker D μ l q a b eab)]
  rw [rhoLin_place t μ l q a b eab,
    hR _ _ rfl eab ea eb, map_zero]

private theorem rhoObj_normal (A : Obj (sig D)) (hA : A.Ok) (μ : X) (he : A.endR = μ) :
    A = ob D μ (A.word.map Col.l) := by
  obtain ⟨hw, hs⟩ := word_eq_wd (D := D) A.start A.word hA
  change A.word = wd D A.endR (A.word.map Col.l) at hw
  change A.start = wt D A.endR (A.word.map Col.l) at hs
  rw [he] at hw hs
  exact Obj.ext hs hw

private theorem rhoDiagram_cod_normal {μ : X} {s : List (Letter I)} {A : Obj (sig D)}
    (d : ob D μ s ⟶ A) : A = ob D μ (A.word.map Col.l) :=
  rhoObj_normal A ((Diagram.chain d).ok (ok_wd D μ s)) μ
    ((Diagram.chain d).endR_eq.trans (ob_endR D μ s))

private theorem rhoDiagram_dom_normal {μ : X} {s : List (Letter I)} {A : Obj (sig D)}
    (d : A ⟶ ob D μ s) : A = ob D μ (A.word.map Col.l) := by
  have hA : A.Ok := by
    have hc := Diagram.chain d
    cases he : d.layers with
    | nil => rw [he] at hc; cases hc; exact ok_wd D μ s
    | cons L ls => rw [he] at hc; exact hc.2.1 ▸ hc.1.dom_obj_ok
  exact rhoObj_normal A hA μ ((Diagram.chain d).endR_eq.symm.trans (ob_endR D μ s))

private theorem rhoSandwich_cast {A B A' B' C E : Obj (sig D)}
    (pre : LinDiagram k C A) (f : LinDiagram k A B) (post : LinDiagram k B E)
    (ea : A = A') (eb : B = B') :
    pre ≫ f ≫ post = LinDiagram.cast pre rfl ea ≫ LinDiagram.cast f ea eb ≫
      LinDiagram.cast post eb rfl := by
  subst A' B'
  simp only [LinDiagram.cast_rfl]

theorem rhoLin_idealGen (t : k) (ν μ : X)
    (R : (pres D Sc).AllRel)
    (hR : ∀ (ν μ : X) {s r : List (Letter I)}
      (hs : wt D μ s = ν) (hr : wt D μ r = ν)
      (ha : R.dom = ob D μ s) (hb : R.cod = ob D μ r),
      rhoLin (sy := sy) (hc := hc) t ν μ hs hr (LinDiagram.cast R.rel ha hb) = 0)
    (u : Obj (sig D)) (v : List (Col I X))
    (hw : R.dom.WhiskerOK u v) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (pre : LinDiagram k (ob D μ s) (R.dom.whisker u v))
    (post : LinDiagram k (R.cod.whisker u v) (ob D μ r)) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hr
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
      have ea := rhoDiagram_cod_normal d
      have eb := rhoDiagram_dom_normal e
      have hma : wt D μ ((R.dom.whisker u v).word.map Col.l) = ν :=
        (congrArg Obj.start ea).symm.trans ((Diagram.chain d).start_eq.trans hs)
      have hmb : wt D μ ((R.cod.whisker u v).word.map Col.l) = ν :=
        (congrArg Obj.start eb).symm.trans ((Diagram.chain e).start_eq.symm.trans hr)
      rw [rhoSandwich_cast _ _ _ ea eb]
      rw [rhoLin_comp t ν μ hs hma hr, rhoLin_comp t ν μ hma hmb hr,
        rhoLin_allRel_whisker t ν μ R hR u v hw hma hmb ea eb]
      simp

end OddMath.SKM.RhoEvaluator
