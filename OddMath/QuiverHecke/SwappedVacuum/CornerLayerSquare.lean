/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedVacuum.TransformedIdeal
import OddMath.QuiverHecke.HalfTurn.ContextualOldGenerators

/-! # Inputs of the corner layer square

`docs/Nondegeneracy/SwappedVacuumCoordinates.md` §§5–7. Two elementary facts used to
assemble the generator square `ev_layer` of a `VacuumCornerEvaluation` from the layer
observations:

* the transformed ideal `K_(N,T)(s, t)` is closed under right composition with any
  coefficient-extended morphism (`TransformedIdeal.comp_mem`), so the square holds
  trivially for vanishing classes;
* the presented single layer `Diagram.ofLayer L` of `H` is the contextual affine
  generator `ContextualOldGenerators.layerDiagram L.left L.gen L.right`, and its unit
  coefficient extension is the corresponding `sourceCoefficientHom 1`
  (`coefficientHom_one_ofLayer`).
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- The transformed ideal is closed under right composition. -/
theorem TransformedIdeal.comp_mem {cutoff : I → ℕ} {T : Set (SKM.SYM D k)} {s t t' : List I}
    {f : coefficientObj D Sc s ⟶ coefficientObj D Sc t}
    (hf : f ∈ TransformedIdeal D Sc cutoff T s t)
    (g : coefficientObj D Sc t ⟶ coefficientObj D Sc t') :
    f ≫ g ∈ TransformedIdeal D Sc cutoff T s t' := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, r, hr, a, b, rfl⟩ := hx
    exact Submodule.subset_span ⟨v, hv, r, hr, a, b ≫ g, by simp only [Category.assoc]⟩
  | zero => rw [Limits.zero_comp]; exact zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact add_mem hx hy
  | smul c x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hx

/-- The unit coefficient extension of a presented single layer is the source
coefficient extension of its contextual affine generator. -/
theorem coefficientHom_one_ofLayer (L : Layer (sig D)) (hv : L.Valid) :
    coefficientHom D Sc 1 (t := L.dom.word) (t' := L.cod.word)
        ((pres D Sc).diag (Diagram.ofLayer L hv)) =
      sourceCoefficientHom D Sc 1
        (ContextualOldGenerators.layerDiagram D Sc L.left L.gen L.right) := by
  simp only [sourceCoefficientHom, map_one]
  rfl

end OddMath.QuiverHecke
