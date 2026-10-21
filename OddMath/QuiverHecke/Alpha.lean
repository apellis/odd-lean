/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.LabelRelations
import OddMath.SKM.Calculus

/-!
# The upward map of BE2 (11.7)

Weight labelling respects arbitrary horizontal contexts. This is needed to
map the presentation ideal, not only its unwhiskered defining relations.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Reachable boundaries have the same labelled leftmost weight. -/
theorem label_weight_eq (μ : X) {a b : Obj (sig D)} (h : Nonempty (a ⟶ b)) :
    SKM.wt D μ (upWord b.word) = SKM.wt D μ (upWord a.word) := by
  obtain ⟨f⟩ := h
  exact (Diagram.chain ((label D μ).map f)).start_eq

/-- Placing a labelled diagram changes its rightmost weight by the right context. -/
def labelWhisker : LayerMap.WhiskerData (label D) where
  Admissible _ := True
  admissible_interchange _ := trivial
  idx μ _ _ v := SKM.wt D μ (upWord v)
  left μ a u v := SKM.ob D (SKM.wt D (SKM.wt D μ (upWord v)) (upWord a.word))
    (upWord u.word)
  right μ _ _ v := SKM.wd D μ (upWord v)
  whiskerOK := by
    intro μ a u v _ _
    exact SKM.whiskerOK_ob D μ (upWord u.word) (upWord v) (upWord a.word)
  obj_whisker := by
    intro μ a u v _ _ b hf
    simpa only [label, Obj.whisker_word, upWord_append] using
      SKM.ob_whisker D μ (upWord u.word) (upWord v) (upWord a.word) (upWord b.word)
        (label_weight_eq D _ hf)
  layer_whisker := by
    intro μ a u v _ _ L _ hf
    have hs := label_weight_eq D (SKM.wt D μ (upWord v)) hf
    have hs' : SKM.wt D (SKM.wt D μ (upWord v))
        (@upWord I L.left ++ L.gen.toSKM.dom ++ @upWord I L.right) =
        SKM.wt D (SKM.wt D μ (upWord v)) (upWord a.word) := by
      simpa only [Layer.dom, sig, upWord_append, upWord_dom] using hs
    simpa only [label, Layer.whisker, upWord_append] using
      (SKM.lay_whisker D μ (upWord u.word) (upWord v) (@upWord I L.left) L.gen.toSKM
        (@upWord I L.right) (upWord a.word) hs').symm

/-- The corresponding local interchange datum with weight labels. -/
def labelInterchange (μ : X) (x : InterchangeData (sig D)) : InterchangeData (SKM.sig D) where
  start := (show X from SKM.wt D μ (@upWord I
    (List.append (α := I) (List.append (α := I) x.g.dom x.mid) x.h.dom)))
  g := (x.g.toSKM, SKM.wt D μ (@upWord I (List.append (α := I) x.mid x.h.dom)))
  mid := SKM.wd D (SKM.wt D μ (upWord x.h.dom)) (@upWord I x.mid)
  h := (x.h.toSKM, μ)

/-- Labelling respects the ambient Koszul interchange relation. -/
theorem label_interchange (μ : X) {x : InterchangeData (sig D)} (hx : x.Valid) :
    (freeLift k ((label D μ).toPresented (SKM.pres D Sc) fun _ => 1)).map
      (InterchangeData.rel k hx) = 0 := by
  refine (label D μ).toPresented_interchange (SKM.pres D Sc) (fun _ => 1) hx
    (labelInterchange D μ x) ?_ ?_ ?_ ?_ ?_
  all_goals
    cases hg : x.g <;> cases hh : x.h <;>
      simp [label, labelInterchange, InterchangeData.gh₁, InterchangeData.gh₂,
        InterchangeData.hg₁, InterchangeData.hg₂, InterchangeData.sign,
        sig, SKM.sig, SKM.lay, Shape.dom, Shape.cod, Shape.toSKM, Shape.parity,
        SKM.Shape.dom, SKM.Shape.cod, SKM.Shape.parity, upWord, hg, hh,
        SKM.wt_append, SKM.wd_append, SKM.wt, SKM.wd, SKM.sh,
        add_comm, add_left_comm, add_assoc]

/-- The upward functor of (11.7), before collecting fixed-length matrix blocks. -/
def alpha (μ : X) : H D Sc ⥤ (SKM.pres D Sc).Presented :=
  LayerMap.lift (pres D Sc) (labelWhisker D) (fun _ => trivial)
    (label_rel D Sc) (fun μ _ hx => label_interchange D Sc μ hx) μ

instance alpha_additive (μ : X) : (alpha D Sc μ).Additive :=
  LayerMap.lift_additive _ _ _ _ _
instance alpha_linear (μ : X) : (alpha D Sc μ).Linear k :=
  LayerMap.lift_linear _ _ _ _ _

/-- On objects, the rightmost weight is exactly the specified weight. -/
@[simp] theorem alpha_obj (μ : X) (s : List I) :
    (alpha D Sc μ).obj ((pres D Sc).obj (ob D s)) =
      (SKM.pres D Sc).obj (SKM.ob D μ (upWord s)) := rfl

/-- On diagrams, `α` is weight labelling with coefficient one. -/
@[simp] theorem alpha_diag (μ : X) {a b : Obj (sig D)} (f : a ⟶ b) :
    (alpha D Sc μ).map ((pres D Sc).diag f) =
      (SKM.pres D Sc).diag ((label D μ).map f) := by
  simp only [alpha, LayerMap.lift_diag, Diagram.weight_one, one_smul]

/-- The upward map preserves parity. -/
theorem alpha_mem_parity (μ : X) {a b : Obj (sig D)}
    {f : (pres D Sc).obj a ⟶ (pres D Sc).obj b} {p : ZMod 2}
    (hf : f ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) a b p) :
    (alpha D Sc μ).map f ∈ (SKM.pres D Sc).homDeg
      (Presentation.parityDeg (SKM.sig D)) ((label D μ).obj a) ((label D μ).obj b) p :=
  LayerMap.lift_mem_homDeg (labelWhisker D) (fun _ => trivial) (label_rel D Sc)
    (fun μ _ hx => label_interchange D Sc μ hx) μ (label_parity D μ) hf

/-- The upward map preserves the integer degree. -/
theorem alpha_mem_degree (sy : SKM.Symmetrizer D) (μ : X) {a b : Obj (sig D)}
    {f : (pres D Sc).obj a ⟶ (pres D Sc).obj b} {d : ℤ}
    (hf : f ∈ (pres D Sc).homDeg (gdeg D sy) a b d) :
    (alpha D Sc μ).map f ∈ (SKM.pres D Sc).homDeg
      (SKM.gdeg D sy) ((label D μ).obj a) ((label D μ).obj b) d :=
  LayerMap.lift_mem_homDeg (labelWhisker D) (fun _ => trivial) (label_rel D Sc)
    (fun μ _ hx => label_interchange D Sc μ hx) μ (label_degree D sy μ) hf

end OddMath.QuiverHecke
