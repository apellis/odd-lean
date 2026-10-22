/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.HeckeCorner
import OddMath.QuiverHecke.IndecomposableCorners

/-!
# Local corners of indecomposable summands of words

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, top step of the width
induction. For an even degree-zero idempotent `z` of a word `E_s` in `H` whose summand
`Q^0 Π^0 (s, z)` of `Ḣ_{q,π}` is indecomposable, the homogeneous corners `z H_γ z` form a local
corner (`localCorner_of_isIndec`). The two inputs of `localCorner_heCorner` are Corollary 11.4
for one summand (`cornerTypeM_of_isIndec`): the residue field of the corner is `k`, and the
corner has no odd degree-zero unit.
-/

noncomputable section

open CategoryTheory StringDiagrams GradedSupercategory KrullSchmidt
open OddMath.SKM.Summands OddMath.SKM.GradedWalk

namespace OddMath.QuiverHecke

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : SKM.Datum I X}
  {k : Type w} [Field k] {Sc : SKM.Scalars D k} {sy : SKM.Symmetrizer D}
  {hc : Sc.Homogeneous} {s : List I}

/-- **The corners of an indecomposable summand are local** (BE2, proof of Theorem 11.7, from
Corollary 11.4). -/
theorem localCorner_of_isIndec {z : End (hObj D Sc sy hc s)} (hz : z ≫ z = z)
    (hz0 : z ∈ homPiece D Sc sy hc s s 0 0) (hind : IsIndec (RZ hz hz0)) :
    ∃ a lo : ℕ, LocalCorner (heCorner z) z (heRad hind) a lo := by
  obtain ⟨hres, hodd⟩ := cornerTypeM_of_isIndec (k := k) hz hz0 hind
  refine localCorner_heCorner hind (fun a ha => ?_) (fun x hx u hu hxu hux => ?_)
  · obtain ⟨c, hc⟩ := hres a ha.1 ha.2
    exact ⟨c, hc⟩
  · exact hodd x u hx.1 hu.1 hx.2 hu.2 hux hxu

end OddMath.QuiverHecke
