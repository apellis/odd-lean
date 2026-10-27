/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.FiniteColourIdealDescent

/-!
# Finite-colour equality in the diagram presentation

The finite-derivation step of `SwappedActionAssembly`, §8, for Brundan–Ellis
Definition 1.5. An equality of specified free-linear diagrams in the full
presentation already holds in some finite-subtype presentation containing the
support of both inputs and of its contextual derivation. No fixed inclusion
of presented categories is asserted faithful.
-/

noncomputable section
namespace OddMath.SKM.FiniteColour
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X) (J : Finset I)
variable {k : Type w} [CommRing k] (Sc : Scalars D k)

private theorem shape_injective : Function.Injective (shape J) := by
  intro g h e
  cases g <;> cases h <;> simp_all [shape, Subtype.ext_iff]

omit [AddCommGroup X] in
private theorem colour_injective : Function.Injective (colour (X := X) J) := by
  rintro ⟨⟨e, i, hi⟩, r⟩ ⟨⟨f, j, hj⟩, s⟩ h
  cases h
  rfl

private theorem layer_injective : Function.Injective (inclusion D J).layer := by
  intro L M h
  apply Layer.ext
  · exact congrArg (fun N : Layer (sig D) => N.start) h
  · exact List.map_injective_iff.mpr (colour_injective J)
      (congrArg (fun N : Layer (sig D) => N.left) h)
  · apply Prod.ext
    · exact shape_injective J (congrArg (fun N : Layer (sig D) => N.gen.1) h)
    · exact congrArg (fun N : Layer (sig D) => N.gen.2) h
  · exact List.map_injective_iff.mpr (colour_injective J)
      (congrArg (fun N : Layer (sig D) => N.right) h)

/-- Inclusion of free diagrams is injective, prior to quotienting by relations. -/
theorem inclusion_diagram_injective {a b : Obj (sig (D.restrictColours J))} :
    Function.Injective ((inclusion D J).toLayerMap.map (a := a) (b := b)) := by
  intro f g h
  apply Diagram.ext
  exact List.map_injective_iff.mpr (layer_injective D J)
    (congrArg Diagram.layers h)

/-- Inclusion of free-linear diagrams is injective over any commutative ring,
including the zero ring. This does not claim injectivity after presentation. -/
theorem inclusion_linear_injective {a b : Obj (sig (D.restrictColours J))} :
    Function.Injective ((inclusion D J).toLayerMap.lin (R := k) (a := a) (b := b)) :=
  Finsupp.mapDomain_injective (inclusion_diagram_injective D J)

/-- Enlarging a finite contextual witness preserves its ideal membership. -/
theorem finiteColourIdeal_mono {a b : Obj (sig D)} {J K : Finset I}
    (h : J ⊆ K) : finiteColourIdeal D Sc a b J ≤ finiteColourIdeal D Sc a b K := by
  apply Submodule.span_mono
  rintro f ⟨c, hc, rfl⟩
  exact ⟨c, hc.trans h, rfl⟩

/-- Equality of specified free-linear expressions in the full SKM presentation
is witnessed in a finite-subtype presentation at restricted endpoints. The
finite set retains both input supports, even when their common summands cancel
in the difference. -/
theorem eq_finiteColourPresentation {a b : Obj (sig D)}
    (f g : LinDiagram k a b) (h : (pres D Sc).lin f = (pres D Sc).lin g) :
    ∃ J : Finset I, linearColours D f ⊆ J ∧ linearColours D g ⊆ J ∧
      ∃ a' b' : Obj (sig (D.restrictColours J)),
        ∃ (ha : (inclusion D J).obj a' = a)
          (hb : (inclusion D J).obj b' = b),
          ∃ f' g' : LinDiagram k a' b',
            LinDiagram.cast ((inclusion D J).toLayerMap.lin f') ha hb = f ∧
            LinDiagram.cast ((inclusion D J).toLayerMap.lin g') ha hb = g ∧
            (pres (D.restrictColours J) (Sc.restrictColours D J)).lin f' =
              (pres (D.restrictColours J) (Sc.restrictColours D J)).lin g' := by
  classical
  obtain ⟨J₀, hw⟩ := eq_finiteColourIdeal D Sc f g h
  let J := J₀ ∪ linearColours D f ∪ linearColours D g
  have hf : linearColours D f ⊆ J :=
    Finset.subset_union_right.trans Finset.subset_union_left
  have hg : linearColours D g ⊆ J := Finset.subset_union_right
  have hw' : f - g ∈ finiteColourIdeal D Sc a b J :=
    finiteColourIdeal_mono D Sc (Finset.subset_union_left.trans Finset.subset_union_left) hw
  let a' := restrictObj D J a (by
    exact (Finset.subset_union_left.trans Finset.subset_union_left).trans hf)
  let b' := restrictObj D J b (by
    exact (Finset.subset_union_right.trans Finset.subset_union_left).trans hf)
  have ha := obj_restrictObj D J a (by
    exact (Finset.subset_union_left.trans Finset.subset_union_left).trans hf)
  have hb := obj_restrictObj D J b (by
    exact (Finset.subset_union_right.trans Finset.subset_union_left).trans hf)
  obtain ⟨f', ef⟩ := supported_linear_lift_at D J f hf a' b' ha hb
  obtain ⟨g', eg⟩ := supported_linear_lift_at D J g hg a' b' ha hb
  obtain ⟨d', hd', ed⟩ := supported_ideal_lift_at D J Sc a' b' ha hb hw'
  have heq : d' = f' - g' := inclusion_linear_injective D J (k := k) (by
    have ed' := ed
    rw [← ef, ← eg] at ed'
    cases ha
    cases hb
    simpa only [LinDiagram.cast_rfl, LayerMap.lin_sub] using ed')
  refine ⟨J, hf, hg, a', b', ha, hb, f', g', ef, eg, ?_⟩
  exact ((pres (D.restrictColours J) (Sc.restrictColours D J)).lin_eq_iff f' g').mpr
    (heq ▸ hd')

end OddMath.SKM.FiniteColour
