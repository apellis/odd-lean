/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.FiniteColourContextRestriction

/-!
# Finite-colour derivations in the diagram presentation

The finite-derivation step of `SwappedActionAssembly`, §8, for
Brundan–Ellis Definition 1.5. The weight group and all region labels
are unchanged by restriction.
-/

noncomputable section
namespace OddMath.SKM.FiniteColour
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X) (J : Finset I)
variable {k : Type w} [CommRing k] (Sc : Scalars D k)
local instance : DecidableEq I := Classical.decEq I

private theorem fold_contains {α : Type*} (s : List α) (c : α → Finset I)
    (x : α) (hx : x ∈ s) (A : Finset I) : c x ⊆ s.foldl (fun B y => B ∪ c y) A := by
  induction s generalizing A with
  | nil => cases hx
  | cons y s ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · have grow (t : List α) (B : Finset I) : B ⊆ t.foldl (fun C z => C ∪ c z) B := by
        induction t generalizing B with
        | nil => exact Finset.Subset.rfl
        | cons z t ih => exact Finset.subset_union_left.trans (ih _)
      exact Finset.subset_union_right.trans (grow s _)
    · exact ih hx _

private theorem linear_diagram_supported {a b : Obj (sig D)} (f : LinDiagram k a b)
    (hf : linearColours D f ⊆ J) (d : a ⟶ b) (hd : d ∈ f.support) :
    diagramColours D d ⊆ J := by
  intro i hi
  apply hf
  exact Finset.mem_union_right _ (fold_contains (s := f.support.toList)
    (c := diagramColours D) d (Finset.mem_toList.mpr hd) ∅ hi)

private theorem linear_source_supported {a b : Obj (sig D)} (f : LinDiagram k a b)
    (hf : linearColours D f ⊆ J) : wordColours a.word ⊆ J :=
  Finset.Subset.trans (Finset.subset_union_left.trans Finset.subset_union_left) hf

private theorem linear_target_supported {a b : Obj (sig D)} (f : LinDiagram k a b)
    (hf : linearColours D f ⊆ J) : wordColours b.word ⊆ J :=
  Finset.Subset.trans (Finset.subset_union_right.trans Finset.subset_union_left) hf

/-- Restriction of a diagram at fixed, common restricted endpoints. -/
def restrictDiagramAt {a b : Obj (sig D)} (d : a ⟶ b)
    (ha : wordColours a.word ⊆ J) (hb : wordColours b.word ⊆ J)
    (hd : diagramColours D d ⊆ J) :
    restrictObj D J a ha ⟶ restrictObj D J b hb :=
  Diagram.cast (restrictDiagram D J d hd)
    (inclusion_obj_injective D J ((obj_restrictObj D J a _).trans
      (obj_restrictObj D J a _).symm))
    (inclusion_obj_injective D J ((obj_restrictObj D J b _).trans
      (obj_restrictObj D J b _).symm))

/-- Inclusion of a restricted diagram at its canonical common endpoints. -/
theorem include_restrictDiagramAt {a b : Obj (sig D)} (d : a ⟶ b)
    (ha : wordColours a.word ⊆ J) (hb : wordColours b.word ⊆ J)
    (hd : diagramColours D d ⊆ J) :
    Diagram.cast ((inclusion D J).toLayerMap.map (restrictDiagramAt D J d ha hb hd))
      (obj_restrictObj D J a ha) (obj_restrictObj D J b hb) = d := by
  apply Diagram.ext
  exact layers_restrictLayers D J (Diagram.layers d)
    (diagram_layer_supported D J d hd)

/-- A supported free linear combination, at the canonical common restricted endpoints. -/
def restrictLinear {a b : Obj (sig D)} (f : LinDiagram k a b)
    (hf : linearColours D f ⊆ J) :
    LinDiagram k (restrictObj D J a (linear_source_supported D J f hf))
      (restrictObj D J b (linear_target_supported D J f hf)) := by
  let t : (a ⟶ b) →₀ k := f
  exact ∑ d : t.support, t d.val • LinDiagram.of
    (restrictDiagramAt D J d.val (linear_source_supported D J f hf)
      (linear_target_supported D J f hf)
      (linear_diagram_supported D J f hf d.val d.property))

/-- Linear inclusion recovers every supported combination at its fixed endpoints. -/
theorem include_restrictLinear {a b : Obj (sig D)} (f : LinDiagram k a b)
    (hf : linearColours D f ⊆ J) :
    LinDiagram.cast ((inclusion D J).toLayerMap.lin (restrictLinear D J f hf))
      (obj_restrictObj D J a (linear_source_supported D J f hf))
      (obj_restrictObj D J b (linear_target_supported D J f hf)) = f := by
  let t : (a ⟶ b) →₀ k := f
  let aa := restrictObj D J a (linear_source_supported D J f hf)
  let bb := restrictObj D J b (linear_target_supported D J f hf)
  let ha : (inclusion D J).toLayerMap.obj aa = a :=
    obj_restrictObj D J a (linear_source_supported D J f hf)
  let hb : (inclusion D J).toLayerMap.obj bb = b :=
    obj_restrictObj D J b (linear_target_supported D J f hf)
  change Finsupp.mapDomain (fun d : (inclusion D J).toLayerMap.obj
      (restrictObj D J a (linear_source_supported D J f hf)) ⟶
      (inclusion D J).toLayerMap.obj
      (restrictObj D J b (linear_target_supported D J f hf)) =>
      Diagram.cast d ha hb)
      (Finsupp.mapDomain (inclusion D J).toLayerMap.map
        (∑ d : t.support, t d.val • LinDiagram.of
          (restrictDiagramAt D J d.val (linear_source_supported D J f hf)
            (linear_target_supported D J f hf)
            (linear_diagram_supported D J f hf d.val d.property)))) = t
  rw [← Finsupp.mapDomain_comp, Finsupp.mapDomain_finsetSum]
  calc
    _ = ∑ d : t.support, Finsupp.single d.val (t d.val) := by
      apply Finset.sum_congr rfl
      intro d _
      change Finsupp.mapDomain
        ((fun d => Diagram.cast d ha hb) ∘ (inclusion D J).toLayerMap.map)
        (t d.val • Finsupp.single (restrictDiagramAt D J d.val
          (linear_source_supported D J f hf) (linear_target_supported D J f hf)
          (linear_diagram_supported D J f hf d.val d.property)) (1 : k)) =
        Finsupp.single d.val (t d.val)
      rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single,
        Finsupp.smul_single_one]
      exact congrArg (fun e => Finsupp.single e (t d.val))
        (include_restrictDiagramAt D J d.val
          (linear_source_supported D J f hf) (linear_target_supported D J f hf)
          (linear_diagram_supported D J f hf d.val d.property))
    _ = t := by
      exact (Finset.sum_subtype t.support (fun x => Iff.rfl)
        (fun x => Finsupp.single x (t x))).symm.trans (Finsupp.sum_single t)

/-- Inclusion respects composition of arbitrary free linear combinations. -/
theorem inclusion_lin_comp {a b c : Obj (sig (D.restrictColours J))}
    (f : LinDiagram k a b) (g : LinDiagram k b c) :
    (inclusion D J).toLayerMap.lin (f ≫ g) =
      (inclusion D J).toLayerMap.lin f ≫ (inclusion D J).toLayerMap.lin g := by
  let φ := (inclusion D J).toLayerMap
  induction f using Finsupp.induction_linear with
  | zero => simp [LayerMap.lin, Finsupp.mapDomain_zero]
  | add f₁ f₂ h₁ h₂ =>
    rw [Preadditive.add_comp, LayerMap.lin_add, h₁, h₂,
      LayerMap.lin_add, Preadditive.add_comp]
  | single d r =>
    induction g using Finsupp.induction_linear with
    | zero => simp [LayerMap.lin, Finsupp.mapDomain_zero]
    | add g₁ g₂ h₁ h₂ =>
      rw [Preadditive.comp_add, LayerMap.lin_add, h₁, h₂,
        LayerMap.lin_add, Preadditive.comp_add]
    | single e s =>
      rw [Free.single_comp_single k (Obj (sig (D.restrictColours J))) d e r s]
      simp only [LayerMap.lin, Finsupp.mapDomain_single,
        Free.single_comp_single k (Obj (sig D)), LayerMap.map_comp]

/-- The linear inclusion preserves composition after coherent endpoint transports. -/
theorem inclusion_cast_comp {a b c : Obj (sig (D.restrictColours J))}
    {a' b' c' : Obj (sig D)}
    (ha : (inclusion D J).obj a = a')
    (hb : (inclusion D J).obj b = b')
    (hc : (inclusion D J).obj c = c')
    (f : LinDiagram k a b) (g : LinDiagram k b c) :
    LinDiagram.cast ((inclusion D J).toLayerMap.lin (f ≫ g)) ha hc =
      LinDiagram.cast ((inclusion D J).toLayerMap.lin f) ha hb ≫
        LinDiagram.cast ((inclusion D J).toLayerMap.lin g) hb hc := by
  cases ha
  cases hb
  cases hc
  simp only [LinDiagram.cast_rfl, inclusion_lin_comp]

/-- Inclusion of a whiskered free diagram, including its boundary transport. -/
theorem inclusion_diagram_whisker {a b : Obj (sig (D.restrictColours J))}
    (d : a ⟶ b) (u : Obj (sig (D.restrictColours J)))
    (v : List (sig (D.restrictColours J)).Colour) (hw : a.WhiskerOK u v) :
    Diagram.cast ((inclusion D J).toLayerMap.map (Diagram.whisker d u v hw))
      ((inclusion D J).obj_whisker a u v)
      ((inclusion D J).obj_whisker b u v) =
        Diagram.whisker ((inclusion D J).toLayerMap.map d)
          ((inclusion D J).obj u) ((inclusion D J).word v)
          ((inclusion D J).whiskerOK hw) := by
  apply Diagram.ext
  simp only [Diagram.layers_cast, LayerMap.layers_map, Diagram.layers_whisker,
    List.map_map]
  apply List.map_congr_left
  intro L _
  exact (inclusion D J).layer_whisker L u v

/-- Whiskering commutes with inclusion of arbitrary free linear combinations. -/
theorem inclusion_lin_whisker {a b : Obj (sig (D.restrictColours J))}
    (f : LinDiagram k a b) (u : Obj (sig (D.restrictColours J)))
    (v : List (sig (D.restrictColours J)).Colour) (hw : a.WhiskerOK u v) :
    LinDiagram.cast ((inclusion D J).toLayerMap.lin (LinDiagram.whisker f u v hw))
      ((inclusion D J).obj_whisker a u v)
      ((inclusion D J).obj_whisker b u v) =
        LinDiagram.whisker ((inclusion D J).toLayerMap.lin f)
          ((inclusion D J).obj u) ((inclusion D J).word v)
          ((inclusion D J).whiskerOK hw) := by
  change Finsupp.mapDomain (fun d => Diagram.cast d
      ((inclusion D J).obj_whisker a u v) ((inclusion D J).obj_whisker b u v))
      (Finsupp.mapDomain (inclusion D J).toLayerMap.map
        (Finsupp.mapDomain (fun d => Diagram.whisker d u v hw) f)) =
    Finsupp.mapDomain (fun d => Diagram.whisker d
        ((inclusion D J).obj u) ((inclusion D J).word v)
        ((inclusion D J).whiskerOK hw))
      (Finsupp.mapDomain (inclusion D J).toLayerMap.map f)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp,
    ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro d _
  exact inclusion_diagram_whisker D J d u v hw

end OddMath.SKM.FiniteColour
