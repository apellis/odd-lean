/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldRightContext

/-!
# Append-old relations over the ELV coefficient category

This is the append-strand counterpart of the old relation span used in
`DeformedGlobalQP.md`: extend an old cyclotomic ideal element by an identity
strand on the right, then allow an arbitrary ambient continuation. The span
uses the full ELV Hom spaces, with every cutoff and exterior coefficient intact.

The span is stable under ambient postcomposition and under precomposition by
right extensions of old morphisms. These are relation-space statements only;
no balance for the moving-strand map or descent of a prescribed map is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Append an identity strand to an old ideal element and allow any ambient continuation. -/
def appendRelations (i : I) (v w : List I) :
    Submodule k (hom D Sc cutoff (v ++ [i]) w) :=
  Submodule.span k {f | ∃ t, ∃ r : hom D Sc cutoff v t,
    r ∈ ideal D Sc cutoff v t ∧ ∃ h : hom D Sc cutoff (t ++ [i]) w,
      rightContext D Sc cutoff [i] v t r ≫ h = f}

/-- The append-old quotient, without imposing a moving-strand cyclotomic relation. -/
abbrev AppendTarget (i : I) (v w : List I) :=
  hom D Sc cutoff (v ++ [i]) w ⧸ appendRelations D Sc cutoff i v w

/-- The canonical linear projection to the append-old quotient. -/
def appendProjection (i : I) (v w : List I) :
    hom D Sc cutoff (v ++ [i]) w →ₗ[k] AppendTarget D Sc cutoff i v w :=
  (appendRelations D Sc cutoff i v w).mkQ

/-- Every right-extended old ideal element followed by a continuation is a relation. -/
theorem appendRelations_mem (i : I) {v t w : List I}
    {r : hom D Sc cutoff v t} (hr : r ∈ ideal D Sc cutoff v t)
    (h : hom D Sc cutoff (t ++ [i]) w) :
    rightContext D Sc cutoff [i] v t r ≫ h ∈ appendRelations D Sc cutoff i v w :=
  Submodule.subset_span ⟨t, r, hr, h, rfl⟩

/-- In particular, the right extension itself belongs to the append-old span. -/
theorem rightContext_mem_appendRelations (i : I) {v t : List I}
    {r : hom D Sc cutoff v t} (hr : r ∈ ideal D Sc cutoff v t) :
    rightContext D Sc cutoff [i] v t r ∈ appendRelations D Sc cutoff i v (t ++ [i]) := by
  simpa only [Category.comp_id] using appendRelations_mem D Sc cutoff i hr (𝟙 _)

/-- The ambient continuation can be postcomposed by an arbitrary ELV morphism. -/
theorem appendRelations_comp (i : I) {v t w : List I}
    {r : hom D Sc cutoff (v ++ [i]) t} (hr : r ∈ appendRelations D Sc cutoff i v t)
    (h : hom D Sc cutoff t w) : r ≫ h ∈ appendRelations D Sc cutoff i v w := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨s, b, hb, a, rfl⟩ := hr
    exact Submodule.subset_span ⟨s, b, hb, a ≫ h, by simp only [Category.assoc]⟩
  | zero => simp
  | add r s _ _ hr hs =>
    rw [Preadditive.add_comp]
    exact Submodule.add_mem _ hr hs
  | smul c r _ hr =>
    rw [Linear.smul_comp]
    exact Submodule.smul_mem _ c hr

/-- Precomposition is allowed for right extensions of old morphisms, not arbitrary ambient ones. -/
theorem comp_appendRelations (i : I) {u v w : List I}
    (a : hom D Sc cutoff u v) {r : hom D Sc cutoff (v ++ [i]) w}
    (hr : r ∈ appendRelations D Sc cutoff i v w) :
    rightContext D Sc cutoff [i] u v a ≫ r ∈ appendRelations D Sc cutoff i u w := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨t, b, hb, h, rfl⟩ := hr
    apply Submodule.subset_span
    refine ⟨t, a ≫ b, comp_ideal D Sc cutoff a hb, h, ?_⟩
    rw [rightContext_comp, Category.assoc]
  | zero => simp
  | add r s _ _ hr hs =>
    rw [Preadditive.comp_add]
    exact Submodule.add_mem _ hr hs
  | smul c r _ hr =>
    rw [Linear.comp_smul]
    exact Submodule.smul_mem _ c hr

/-- Append-old relations lie in the enlarged old cyclotomic ideal. -/
theorem appendRelations_le_ideal (i : I) (v w : List I) :
    appendRelations D Sc cutoff i v w ≤ ideal D Sc cutoff (v ++ [i]) w := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, r, hr, h, rfl⟩
  exact ideal_comp D Sc cutoff (ideal_rightContext D Sc cutoff [i] hr) h

/-- The quotient kills each canonical append-old relation. -/
theorem appendProjection_old_ideal (i : I) {v t w : List I}
    {r : hom D Sc cutoff v t} (hr : r ∈ ideal D Sc cutoff v t)
    (h : hom D Sc cutoff (t ++ [i]) w) :
    appendProjection D Sc cutoff i v w (rightContext D Sc cutoff [i] v t r ≫ h) = 0 := by
  change (appendRelations D Sc cutoff i v w).mkQ _ = 0
  exact (Submodule.Quotient.mk_eq_zero (appendRelations D Sc cutoff i v w)).mpr
    (appendRelations_mem D Sc cutoff i hr h)

/-- No relations beyond the specified span are hidden in the projection. -/
theorem appendProjection_eq_zero_iff (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    appendProjection D Sc cutoff i v w h = 0 ↔ h ∈ appendRelations D Sc cutoff i v w :=
  Submodule.Quotient.mk_eq_zero _

/-- Every append-old quotient class has an ambient representative. -/
theorem appendProjection_surjective (i : I) (v w : List I) :
    Function.Surjective (appendProjection D Sc cutoff i v w) := Submodule.mkQ_surjective _

end OddMath.QuiverHecke.ELVOld
