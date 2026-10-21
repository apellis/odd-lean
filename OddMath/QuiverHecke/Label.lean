/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Grading
import StringDiagrams.LayerMap.Basic

/-!
# Labelling upward diagrams by a rightmost weight

BE2, arXiv:1701.04133v2, (11.7). This is the free-diagram part of the
map: every weight-free dot and crossing acquires the region labels
uniquely determined by the word and the fixed rightmost weight.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)

/-- Regard a colour word as an all-upward signed word. -/
def upWord (t : List I) : List (SKM.Letter I) := t.map SKM.up

@[simp] theorem upWord_append (s t : List I) : upWord (s ++ t) = upWord s ++ upWord t :=
  List.map_append
@[simp] theorem upWord_dom (g : Shape I) : upWord g.dom = g.toSKM.dom := by cases g <;> rfl
@[simp] theorem upWord_cod (g : Shape I) : upWord g.cod = g.toSKM.cod := by cases g <;> rfl

/-- Add the unique weight labels to an upward layer. -/
def label (μ : X) : LayerMap (sig D) (SKM.sig D) where
  obj a := SKM.ob D μ (upWord a.word)
  layer L := SKM.lay D μ (upWord L.left) L.gen.toSKM (upWord L.right)
  valid _ := SKM.lay_valid D _ _ _ _
  dom_eq := by
    intro L _
    rw [SKM.lay_dom]
    cases hg : L.gen <;> simp [Layer.dom, upWord, sig, Shape.toSKM, Shape.dom, SKM.Shape.dom, hg]
  cod_eq := by
    intro L _
    rw [SKM.lay_cod]
    cases hg : L.gen <;> simp [Layer.cod, upWord, sig, Shape.toSKM, Shape.cod, SKM.Shape.cod, hg]

/-- Label a normal-form list of upward layers. -/
def upLayers (ls : List (LayerData I)) : List (SKM.LayerData I) :=
  ls.map fun x => (upWord x.1, x.2.1.toSKM, upWord x.2.2)

theorem SChain.up {s t : List I} {ls : List (LayerData I)} (h : SChain s ls t) :
    SKM.SChain (upWord s) (upLayers ls) (upWord t) := by
  induction ls generalizing s with
  | nil => cases h; rfl
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    exact ⟨by simp only [upWord_append, upWord_dom],
      by simpa only [upWord_append, upWord_cod, upLayers] using ih h⟩

theorem label_mkD (μ : X) {s t : List I} (ls : List (LayerData I)) (h : SChain s ls t) :
    (label D μ).map (mkD D ls h) = SKM.mkD D μ (upLayers ls) h.up := by
  apply Diagram.ext
  simp only [LayerMap.layers_map, layers_mkD, SKM.layers_mkD, layList, SKM.layList,
    upLayers, List.map_map]
  rfl

/-- Labelling preserves the parity of every generator. -/
theorem label_parity (μ : X) :
    (label D μ).PreservesDeg (Presentation.parityDeg (sig D))
      (Presentation.parityDeg (SKM.sig D)) := by
  intro L _
  rw [SKM.parityDeg_sig, parityDeg_sig]
  change L.gen.toSKM.parity D = L.gen.parity D
  cases L.gen <;> rfl

/-- Labelling preserves the integer degree of every generator. -/
theorem label_degree (sy : SKM.Symmetrizer D) (μ : X) :
    (label D μ).PreservesDeg (gdeg D sy) (SKM.gdeg D sy) := by
  intro L _
  change SKM.gdeg D sy (L.gen.toSKM, SKM.wt D μ (upWord L.right)) = gdeg D sy L.gen
  cases L.gen <;> rfl

/-- The same upward relation with a rightmost weight label. -/
def Rel.toSKM (μ : X) : Rel D → SKM.Rel D
  | .quadEq i => .quadEq i μ
  | .quadZero i j h hz => .quadZero i j μ h hz
  | .quadNe i j h hz => .quadNe i j μ h hz
  | .slideL i j h => .slideL i j μ h
  | .slideLEq i => .slideLEq i μ
  | .slideR i j h => .slideR i j μ h
  | .slideREq i => .slideREq i μ
  | .braid i j k h => .braid i j k μ h
  | .braidEq i j h => .braidEq i j μ h

@[simp] theorem Rel.toSKM_dom (μ : X) (r : Rel D) :
    (r.toSKM D μ).dom = upWord r.dom := by cases r <;> rfl
@[simp] theorem Rel.toSKM_cod (μ : X) (r : Rel D) :
    (r.toSKM D μ).cod = upWord r.cod := by cases r <;> rfl
@[simp] theorem Rel.toSKM_weight (μ : X) (r : Rel D) :
    (r.toSKM D μ).ν = μ := by cases r <;> rfl

@[simp] theorem upLayers_append (ls ms : List (LayerData I)) :
    upLayers (ls ++ ms) = upLayers ls ++ upLayers ms := List.map_append
@[simp] theorem upLayers_dots (u : List I) (i : I) (v : List I) (n : ℕ) :
    upLayers (dotsL u i v n) = SKM.dotsL (upWord u) i (upWord v) n := by
  simp [upLayers, dotsL, SKM.dotsL, Shape.toSKM]
@[simp] theorem upLayers_cross (u : List I) (i j : I) (v : List I) :
    upLayers (crossL u i j v) = SKM.crossL (upWord u) i j (upWord v) := rfl

end OddMath.QuiverHecke
