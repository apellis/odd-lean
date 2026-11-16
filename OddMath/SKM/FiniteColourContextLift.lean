/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.FiniteColourIdealRestriction

/-!
# Finite-subtype lifts of contextual ideal generators

The contextual-generator step of `SwappedActionAssembly`, §8, for
Brundan–Ellis Definition 1.5. Raw labels, whiskering and pre/post diagrams
are retained, over any commutative ring and with the original weight group.
This is not yet the finite-span derivation theorem.
-/

noncomputable section
namespace OddMath.SKM.FiniteColour
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X) (J : Finset I)
variable {k : Type w} [CommRing k] (Sc : Scalars D k)

/-- Inclusion on raw relation labels, before expanding coefficients. -/
def includeAllRel : (pres (D.restrictColours J) (Sc.restrictColours D J)).AllRel →
    (pres D Sc).AllRel
  | .user r => .user (relationLabel D J r)
  | .interchange x hx => .interchange (includeInterchange D J x)
      ((includeInterchange_valid_iff D J x).mpr hx)

/-- The supported local lift also recovers its raw relation label. -/
theorem supported_allRel_lift (r : (pres D Sc).AllRel)
    (hr : allRelColours D Sc r ⊆ J) :
    ∃ s : (pres (D.restrictColours J) (Sc.restrictColours D J)).AllRel,
      includeAllRel D J Sc s = r ∧
      ∃ (ha : (inclusion D J).obj s.dom = r.dom)
        (hb : (inclusion D J).obj s.cod = r.cod),
        LinDiagram.cast ((inclusion D J).toLayerMap.lin s.rel) ha hb = r.rel := by
  cases r with
  | user r =>
    obtain ⟨s, hs, ha, hb, h⟩ := inclusion_user_relation D J Sc r hr
    exact ⟨.user s, congrArg Presentation.AllRel.user hs, ha, hb, h⟩
  | interchange x hx =>
    obtain ⟨y, hy, ha, hb, he, _, _, _, h⟩ :=
      supported_interchange_lift D J (k := k) x hr hx
    refine ⟨.interchange y hy, ?_, ha, hb, h⟩
    change Presentation.AllRel.interchange (includeInterchange D J y) _ = .interchange x hx
    cases he
    rfl

/-- Whiskering compatibility is reflected by finite-colour inclusion. -/
theorem inclusion_whiskerOK_iff (a l : Obj (sig (D.restrictColours J)))
    (r : List (sig (D.restrictColours J)).Colour) :
    ((inclusion D J).obj a).WhiskerOK ((inclusion D J).obj l)
      ((inclusion D J).word r) ↔ a.WhiskerOK l r := by
  change ((sig D).ok l.start ((inclusion D J).word l.word) ∧
    (sig D).endR l.start ((inclusion D J).word l.word) = a.start ∧
    (sig D).ok ((sig D).endR a.start ((inclusion D J).word a.word))
      ((inclusion D J).word r)) ↔ _
  rw [inclusion_ok_iff]
  have hl := (inclusion D J).endR_map l.start l.word
  have ha := (inclusion D J).endR_map a.start a.word
  change (sig D).endR l.start ((inclusion D J).word l.word) =
    (sig (D.restrictColours J)).endR l.start l.word at hl
  change (sig D).endR a.start ((inclusion D J).word a.word) =
    (sig (D.restrictColours J)).endR a.start a.word at ha
  rw [hl, ha, inclusion_ok_iff]
  rfl

private theorem lin_cast_inclusion {a b a' b' : Obj (sig (D.restrictColours J))}
    {a'' b'' : Obj (sig D)} (f : LinDiagram k a b)
    (ha : a = a') (hb : b = b')
    (ha' : (inclusion D J).obj a' = a'') (hb' : (inclusion D J).obj b' = b'') :
    LinDiagram.cast ((inclusion D J).toLayerMap.lin (LinDiagram.cast f ha hb)) ha' hb' =
      LinDiagram.cast ((inclusion D J).toLayerMap.lin f)
        ((congrArg (inclusion D J).obj ha).trans ha')
        ((congrArg (inclusion D J).obj hb).trans hb') := by
  cases ha
  cases hb
  simp only [LinDiagram.cast_rfl]

/-- Supported free linear expressions lift at any prescribed matching endpoints. -/
theorem supported_linear_lift_at {a b : Obj (sig D)} (f : LinDiagram k a b)
    (hf : linearColours D f ⊆ J) (a' b' : Obj (sig (D.restrictColours J)))
    (ha : (inclusion D J).obj a' = a) (hb : (inclusion D J).obj b' = b) :
    ∃ f' : LinDiagram k a' b',
      LinDiagram.cast ((inclusion D J).toLayerMap.lin f') ha hb = f := by
  classical
  have hsa : wordColours a.word ⊆ J :=
    (Finset.subset_union_left.trans Finset.subset_union_left).trans hf
  have hsb : wordColours b.word ⊆ J :=
    (Finset.subset_union_right.trans Finset.subset_union_left).trans hf
  let f₀ := restrictLinear D J f hf
  have ea : restrictObj D J a hsa = a' :=
    inclusion_obj_injective D J ((obj_restrictObj D J a hsa).trans ha.symm)
  have eb : restrictObj D J b hsb = b' :=
    inclusion_obj_injective D J ((obj_restrictObj D J b hsb).trans hb.symm)
  refine ⟨LinDiagram.cast f₀ ea eb, ?_⟩
  rw [lin_cast_inclusion]
  exact include_restrictLinear D J f hf

private theorem cast_whisker {S : Signature} {a b a' b' l l' : Obj S}
    {r r' : List S.Colour} (f : LinDiagram k a b)
    (ha : a = a') (hb : b = b') (hl : l = l') (hr : r = r')
    (hw : a.WhiskerOK l r) (hw' : a'.WhiskerOK l' r')
    (hd : a.whisker l r = a'.whisker l' r')
    (hc : b.whisker l r = b'.whisker l' r') :
    LinDiagram.cast (LinDiagram.whisker f l r hw) hd hc =
      LinDiagram.whisker (LinDiagram.cast f ha hb) l' r' hw' := by
  cases ha
  cases hb
  cases hl
  cases hr
  simp only [LinDiagram.cast_rfl]

private theorem cast_trans {S : Signature} {a b a' b' a'' b'' : Obj S}
    (f : LinDiagram k a b) (ha : a = a') (hb : b = b')
    (ha' : a' = a'') (hb' : b' = b'') :
    LinDiagram.cast (LinDiagram.cast f ha hb) ha' hb' =
      LinDiagram.cast f (ha.trans ha') (hb.trans hb') := by
  cases ha
  cases hb
  simp only [LinDiagram.cast_rfl]

/-- Inclusion commutes with whiskering at independently specified common endpoints. -/
theorem inclusion_whisker_at {a b l : Obj (sig (D.restrictColours J))}
    {r : List (sig (D.restrictColours J)).Colour}
    {a' b' l' : Obj (sig D)} {r' : List (sig D).Colour}
    (f : LinDiagram k a b) (ha : (inclusion D J).obj a = a')
    (hb : (inclusion D J).obj b = b') (hl : (inclusion D J).obj l = l')
    (hr : (inclusion D J).word r = r') (hw : a.WhiskerOK l r)
    (hw' : a'.WhiskerOK l' r')
    (hd : (inclusion D J).obj (a.whisker l r) = a'.whisker l' r')
    (hc : (inclusion D J).obj (b.whisker l r) = b'.whisker l' r') :
    LinDiagram.cast ((inclusion D J).toLayerMap.lin (LinDiagram.whisker f l r hw)) hd hc =
      LinDiagram.whisker (LinDiagram.cast ((inclusion D J).toLayerMap.lin f) ha hb)
        l' r' hw' := by
  have ed : ((inclusion D J).obj a).whisker ((inclusion D J).obj l)
      ((inclusion D J).word r) = a'.whisker l' r' := by rw [ha, hl, hr]
  have ec : ((inclusion D J).obj b).whisker ((inclusion D J).obj l)
      ((inclusion D J).word r) = b'.whisker l' r' := by rw [hb, hl, hr]
  have h := congrArg (fun q => LinDiagram.cast q ed ec) (inclusion_lin_whisker D J f l r hw)
  rw [cast_trans] at h
  exact h.trans (cast_whisker _ ha hb hl hr _ hw' ed ec)

/-- A lift records the raw context as well as its full composite expression. -/
structure ContextLift {a b : Obj (sig D)} (c : RelationContext D Sc a b) where
  source : Obj (sig (D.restrictColours J))
  target : Obj (sig (D.restrictColours J))
  context : RelationContext (D.restrictColours J) (Sc.restrictColours D J) source target
  source_eq : (inclusion D J).obj source = a
  target_eq : (inclusion D J).obj target = b
  rel_eq : includeAllRel D J Sc context.rel = c.rel
  left_eq : (inclusion D J).obj context.left = c.left
  right_eq : (inclusion D J).word context.right = c.right
  dom_eq : (inclusion D J).obj (context.rel.dom.whisker context.left context.right) =
    c.rel.dom.whisker c.left c.right
  cod_eq : (inclusion D J).obj (context.rel.cod.whisker context.left context.right) =
    c.rel.cod.whisker c.left c.right
  pre_eq : LinDiagram.cast ((inclusion D J).toLayerMap.lin context.pre) source_eq dom_eq = c.pre
  post_eq : LinDiagram.cast ((inclusion D J).toLayerMap.lin context.post) cod_eq target_eq = c.post
  value_eq : LinDiagram.cast ((inclusion D J).toLayerMap.lin context.value)
    source_eq target_eq = c.value

/-- Every completely supported contextual ideal generator has a finite-subtype
lift, with no assumptions on roots or on the commutative coefficient ring. -/
theorem supported_context_lift {a b : Obj (sig D)} (c : RelationContext D Sc a b)
    (hc : c.colours ⊆ J) : Nonempty (ContextLift D J Sc c) := by
  have support : wordColours a.word ⊆ J ∧ wordColours b.word ⊆ J ∧
      wordColours c.left.word ⊆ J ∧ wordColours c.right ⊆ J ∧
      linearColours D c.pre ⊆ J ∧ linearColours D c.rel.rel ⊆ J ∧
      linearColours D c.post ⊆ J ∧ allRelColours D Sc c.rel ⊆ J := by
    simpa only [RelationContext.colours, Finset.union_subset_iff, and_assoc] using hc
  obtain ⟨ha, hb, hl, hr, hp, _, hq, hs⟩ := support
  obtain ⟨s, hs, sd, sc, sr⟩ := supported_allRel_lift D J Sc c.rel hs
  let a' := restrictObj D J a ha
  let b' := restrictObj D J b hb
  let l := restrictObj D J c.left hl
  let r := restrictWord J c.right hr
  have ea : (inclusion D J).obj a' = a := obj_restrictObj D J a ha
  have eb : (inclusion D J).obj b' = b := obj_restrictObj D J b hb
  have el : (inclusion D J).obj l = c.left := obj_restrictObj D J c.left hl
  have er : (inclusion D J).word r = c.right := word_restrictWord J c.right hr
  have hw : s.dom.WhiskerOK l r := by
    apply (inclusion_whiskerOK_iff D J _ _ _).mp
    rw [sd, el, er]
    exact c.compatible
  have ed : (inclusion D J).obj (s.dom.whisker l r) = c.rel.dom.whisker c.left c.right := by
    rw [(inclusion D J).obj_whisker, sd, el, er]
  have ec : (inclusion D J).obj (s.cod.whisker l r) = c.rel.cod.whisker c.left c.right := by
    rw [(inclusion D J).obj_whisker, sc, el, er]
  obtain ⟨p, ep⟩ := supported_linear_lift_at D J c.pre hp a' _ ea ed
  obtain ⟨q, eq⟩ := supported_linear_lift_at D J c.post hq _ b' ec eb
  let c' : RelationContext (D.restrictColours J) (Sc.restrictColours D J) a' b' :=
    ⟨s, l, r, hw, p, q⟩
  refine ⟨⟨a', b', c', ea, eb, hs, el, er, ed, ec, ep, eq, ?_⟩⟩
  change LinDiagram.cast ((inclusion D J).toLayerMap.lin
    (p ≫ LinDiagram.whisker s.rel l r hw ≫ q)) ea eb = c.value
  rw [inclusion_cast_comp D J ea ed eb, inclusion_cast_comp D J ed ec eb,
    ep, eq, inclusion_whisker_at D J s.rel sd sc el er hw c.compatible ed ec, sr]
  rfl

/-- The lifted expression is an actual generator of the restricted presentation ideal. -/
theorem ContextLift.idealGen {a b : Obj (sig D)} {c : RelationContext D Sc a b}
    (L : ContextLift D J Sc c) :
    (pres (D.restrictColours J) (Sc.restrictColours D J)).IdealGen L.context.value :=
  Presentation.IdealGen.intro L.context.rel L.context.left L.context.right
    L.context.compatible L.context.pre L.context.post

end OddMath.SKM.FiniteColour
