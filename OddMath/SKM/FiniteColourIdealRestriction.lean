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

end OddMath.SKM.FiniteColour
