/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Action
import OddMath.QuiverHecke.Alpha

/-! # The swapped action of an affine layer

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §6: the upward functor
`alpha D Sc μ` sends a layer of the affine quiver Hecke presentation to the labelled
super Kac–Moody layer (`label D μ`). For a layer representation `Q` satisfying the defining
relations, the upward module action of the image of an affine layer is therefore the map of the
labelled layer, transported along the equalities of its boundary objects
(`SwappedObligations.upwardModuleAction_act_layer`). For the swapped representation of a
probe–reservoir datum this map is the layer map of the swapped generators
(`ProbeReservoir.SwappedRelationData.upwardModuleAction_act_layer`).

This is the identification used in `docs/Nondegeneracy/SwappedVacuumCoordinates.md` §5 to
compute the vacuum-corner evaluation layer by layer.

Main declarations: `LayerRep.toLocal_functor_map_layer`,
`SwappedObligations.upwardModuleAction_act_layer`,
`ProbeReservoir.SwappedRelationData.upwardModuleAction_act_layer`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u w w₀ w₁ w₂ w₃

namespace LayerRep

variable {S : Signature.{w₀, w₁, w₂}} {R : Type w} [CommRing R]
  (Q : LayerRep.{w, w₀, w₁, w₂, w₃} S R)

/-- The image of a single layer under the functor of a layer representation is the map of the
layer, transported along the equalities of its boundary objects. -/
theorem toLocal_functor_map_layer (L : Layer S) (hv : L.Valid) {a b : Obj S} (ha : L.dom = a)
    (hb : L.cod = b) (x : Q.M a) :
    (Q.toLocal.functor.map (Diagram.layer L hv ha hb)).hom x =
      cast (congrArg Q.M hb) (Q.act L (cast (congrArg Q.M ha.symm) x)) := by
  subst ha hb
  rw [LocalInterpretation.functor_map_layer_hom]
  exact Q.toLocal_layer L x

end LayerRep

section Obligations

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : Datum I X} {Sc : Scalars D k} {Q : LayerRep.{u, u, u, u, u} (SKM.sig D) k}

namespace SwappedObligations

variable (h : SwappedObligations Sc Q)

/-- **The upward action of an affine layer** is the map of the labelled super Kac–Moody layer,
transported along the boundary equalities of the labelling. -/
theorem upwardModuleAction_act_layer (μ : X) (L : Layer (QuiverHecke.sig D)) (hv : L.Valid)
    (v : (h.upwardModuleAction μ).V L.dom.word) :
    (h.upwardModuleAction μ).act L.dom.word L.cod.word
        ((alpha D Sc μ).map ((QuiverHecke.pres D Sc).diag (Diagram.ofLayer L hv))) v =
      cast (congrArg Q.M ((label D μ).cod_eq hv))
        (Q.act ((label D μ).layer L) (cast (congrArg Q.M ((label D μ).dom_eq hv).symm) v)) := by
  rw [h.upwardModuleAction_act, alpha_diag]
  unfold SwappedObligations.functor
  rw [Presentation.lift_diag, LayerMap.map_ofLayer]
  exact Q.toLocal_functor_map_layer _ _ _ _ v

end SwappedObligations

end Obligations

namespace ProbeReservoir

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k} {P : ProbeReservoir k B D Sc}

namespace SwappedRelationData

variable {c : P.CrossCoeff} {L : P.LeftwardData} (h : P.SwappedRelationData c L)
  (Gs Ys : ∀ s, P.H s)

/-- **The swapped action of an affine layer** is the swapped layer map of the labelled super
Kac–Moody layer, transported along the boundary equalities of the labelling. -/
theorem upwardModuleAction_act_layer (μ : X) (L' : Layer (QuiverHecke.sig D)) (hv : L'.Valid)
    (v : (h.upwardModuleAction Gs Ys μ).V L'.dom.word) :
    (h.upwardModuleAction Gs Ys μ).act L'.dom.word L'.cod.word
        ((alpha D Sc μ).map ((QuiverHecke.pres D Sc).diag (Diagram.ofLayer L' hv))) v =
      cast (congrArg (P.Mod Gs Ys) ((label D μ).cod_eq hv))
        (P.layerMap (P.swappedGens c L) ((label D μ).layer L')
          (cast (congrArg (P.Mod Gs Ys) ((label D μ).dom_eq hv).symm) v)) :=
  (h.obligations Gs Ys).upwardModuleAction_act_layer μ L' hv v

end SwappedRelationData

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
