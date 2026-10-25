/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.WeightedCoefficientSeparation
import OddMath.SKM.BubbleCoefficientGenerators

/-! # Actual ideal closure and coefficient relations for weighted separation -/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

theorem weightedRelationSpan_comp {t v t' : List I} {N : ℕ}
    {f : coefficientObj D Sc t ⟶ coefficientObj D Sc v}
    (hf : f ∈ WeightedRelationSpan D Sc t v N)
    (g : coefficientObj D Sc v ⟶ coefficientObj D Sc t') :
    f ≫ g ∈ WeightedRelationSpan D Sc t t' N := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨w, hw, r, hr, a, b, rfl⟩ := hf
    exact Submodule.subset_span ⟨w, hw, r, hr, a, b ≫ g, by simp only [Category.assoc]⟩
  | zero => simp
  | add f h _ _ hf hh =>
    rw [Preadditive.add_comp]
    exact Submodule.add_mem _ hf hh
  | smul c f _ hf =>
    rw [Linear.smul_comp]
    exact Submodule.smul_mem _ c hf

/-- Left ideal closure on the fixed strand-number component. -/
theorem comp_weightedRelationSpan {t v t' : List I} {N : ℕ}
    (htv : t.length = v.length)
    (f : coefficientObj D Sc t ⟶ coefficientObj D Sc v)
    {g : coefficientObj D Sc v ⟶ coefficientObj D Sc t'}
    (hg : g ∈ WeightedRelationSpan D Sc v t' N) :
    f ≫ g ∈ WeightedRelationSpan D Sc t t' N := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨w, hw, r, hr, a, b, rfl⟩ := hg
    exact Submodule.subset_span ⟨w, hw.trans htv.symm, r, hr, f ≫ a, b,
      by simp only [Category.assoc]⟩
  | zero => simp
  | add g h _ _ hg hh =>
    rw [Preadditive.comp_add]
    exact Submodule.add_mem _ hg hh
  | smul c g _ hg =>
    rw [Linear.comp_smul]
    exact Submodule.smul_mem _ c hg

theorem coefficient_cl_nil (t : List I) : cl D Sc t t [] (sChain_pl t []) = 𝟙 _ := by
  rw [cl, ← Presentation.diag_id]
  exact Presentation.diag_eq_of_layers_eq _ (by simp [pl, layList])

/-- Coefficient-only truncation relations participate in the same genuine
ideal as the deformed first-dot polynomial. -/
theorem highCoefficient_identity_mem_relationSpan (t : List I) {N : ℕ}
    {a : SKM.SYM D k} (ha : a ∈ SKM.SYM.CoefficientAtLeast D k N) :
    sourceCoefficientHom D Sc a (𝟙 ((pres D Sc).obj (ob D t))) ∈
      WeightedRelationSpan D Sc t t N := by
  have he := highCoefficient_word_mem_score D Sc (t := t) (t' := t) ha [] (sChain_pl t [])
  simp [coefficient_cl_nil, positionedScore, wordScore, crossCount] at he
  exact Submodule.subset_span ⟨t, rfl, _, he, 𝟙 _, 𝟙 _, by simp⟩

/-- The actual ELV even-cutoff coefficient relation belongs to the same ideal
as the weighted cyclotomic polynomial, with its independent colour retained. -/
theorem elvTopRelation_mem_relationSpan (t : List I)
    (i : {i : I // D.parity i = 1}) (r : ℕ) :
    sourceCoefficientHom D Sc (SKM.SYM.delta D k i * SKM.SYM.e D k i.1 r)
      (𝟙 ((pres D Sc).obj (ob D t))) ∈
      WeightedRelationSpan D Sc t t (2 * (r + 1)) := by
  apply highCoefficient_identity_mem_relationSpan
  exact SKM.SYM.coefficientAtLeast_antitone D k (Nat.le_succ _)
    (SKM.SYM.elvTopRelation_mem_coefficientAtLeast D k i r)

/-- Setting the top elementary coefficient to zero, the exterior-flat
alternative for an even cutoff, also satisfies the same separation bound. -/
theorem oddTopElementary_mem_relationSpan (t : List I)
    (i : {i : I // D.parity i = 1}) (r : ℕ) :
    sourceCoefficientHom D Sc (SKM.SYM.e D k i.1 r)
      (𝟙 ((pres D Sc).obj (ob D t))) ∈
      WeightedRelationSpan D Sc t t (2 * (r + 1)) := by
  apply highCoefficient_identity_mem_relationSpan
  simpa [SKM.SYM.elementaryWeight, i.property] using
    SKM.SYM.elementary_mem_coefficientAtLeast D k i.1 r

end OddMath.QuiverHecke
