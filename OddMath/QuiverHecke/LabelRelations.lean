/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Label
import StringDiagrams.Biadjunction.Zigzag

/-! Comparison of the independent quiver Hecke relations with the upward SKM relations. -/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

@[simp] theorem label_dg (μ : X) {s t : List I} (ls : List (LayerData I)) (h : SChain s ls t) :
    (label D μ).lin (dg (k := k) D ls h) = SKM.dg D μ (upLayers ls) h.up := by
  rw [dg, LayerMap.lin_of, label_mkD]

@[simp] theorem label_idg (μ : X) (s : List I) :
    (label D μ).lin (idg (k := k) D s) = SKM.idg D μ (upWord s) := by
  rw [idg, LayerMap.lin_of, LayerMap.map_id]
  rfl

private theorem lin_sum (μ : X) {a b : Obj (sig D)} {ι : Type*}
    (s : Finset ι) (f : ι → LinDiagram k a b) :
    (label D μ).lin (∑ i ∈ s, f i) = ∑ i ∈ s, (label D μ).lin (f i) :=
  map_sum ((label D μ).linMap a b) f s

/-- Every defining relation of `H` is exactly an upward relation in `U(g)` after labelling. -/
theorem label_rel (μ : X) (r : Rel D) :
    (freeLift k ((label D μ).toPresented (SKM.pres D Sc) fun _ => 1)).map
      ((pres D Sc).rel r) = 0 := by
  rw [LayerMap.freeLift_toPresented_one]
  have h := (SKM.pres D Sc).lin_rel_self (r.toSKM D μ)
  cases r <;>
    simp only [pres, relation, Rel.toSKM, SKM.pres, SKM.relation,
      LayerMap.lin_sub, LayerMap.lin_smul, lin_sum, label_dg, label_idg,
      upLayers_append, upLayers_dots, upLayers_cross, upWord, List.map_nil, List.map_cons,
      Rel.dom, Rel.cod, SKM.Rel.dom, SKM.Rel.cod, SKM.Rel.ν] at h ⊢ <;>
    convert h using 1

end OddMath.QuiverHecke
