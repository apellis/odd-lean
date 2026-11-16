/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.UpwardCoefficientDetection

/-! # Bounded cyclic recovery for upward coefficient independence

A conditional consumer for the vacuum recovery step in the nondegeneracy
programme. The word pair and degree are fixed before choosing a cutoff.
No total window function on all words at a given cutoff is required.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u w
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

/-- Cyclic recovery for one word pair and one degree bound. There are no
requirements at other word pairs or at smaller cutoffs. The two actions are
only required to respect source precomposition. Normalization is a formula
on coefficient generators, not an automorphism of the truncated quotient. -/
structure BoundedCyclicRecovery (μ : X) (t t' : List I) (d : ℕ) (cutoff : I → ℕ) where
  V : Type w
  W : Type w
  [addV : AddCommGroup V]
  [moduleV : Module k V]
  [addW : AddCommGroup W]
  [moduleW : Module k W]
  sourceAct : UpwardHom D Sc μ t t →ₗ[k] Module.End k V
  act : UpwardHom D Sc μ t t' →ₗ[k] (V →ₗ[k] W)
  act_comp : ∀ (f : UpwardHom D Sc μ t t) (g : UpwardHom D Sc μ t t'),
    act (f ≫ g) = (act g).comp (sourceAct f)
  vacuum : V
  bubbles : SKM.SYM D k →ₐ[k] Module.End k V
  bubbles_eq : ∀ a, bubbles a =
    sourceAct (SKM.bubAt D Sc μ (upWord t) (SKM.betaSYM cs μ a))
  reservoir : SKM.SYM D k →ₐ[k] Module.End k V
  elementary : ∀ i n, bubbles (SKM.SYM.e D k i n) = reservoir (SKM.SYM.e D k i n)
  exterior : ∀ i, bubbles (SKM.SYM.delta D k i) = reservoir (SKM.SYM.delta D k i)
  recover : W →ₗ[k]
    ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸ ELVRelationSpan D Sc cutoff t t')
  affine_coordinates : ∀ (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')),
    sourceCoefficientHom D Sc a f ∈ ExtendedAtMost D Sc t t' d →
    recover (act ((alpha D Sc μ).map f) (reservoir a vacuum)) =
      (ELVRelationSpan D Sc cutoff t t').mkQ (sourceCoefficientHom D Sc a f)

attribute [instance] BoundedCyclicRecovery.addV BoundedCyclicRecovery.moduleV
  BoundedCyclicRecovery.addW BoundedCyclicRecovery.moduleW

namespace BoundedCyclicRecovery
variable {D Sc cs} {μ : X} {t t' : List I} {d : ℕ} {cutoff : I → ℕ}
  (E : BoundedCyclicRecovery D Sc cs μ t t' d cutoff)

theorem normalized_bubbles : E.bubbles = E.reservoir := by
  apply SKM.SYM.hom_ext
  intro g
  cases g with
  | inl p => exact E.elementary p.1 p.2
  | inr i => exact E.exterior i

/-- Observe a morphism by acting on the chosen vacuum and recovering coordinates. -/
def observe : UpwardHom D Sc μ t t' →ₗ[k]
    ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸ ELVRelationSpan D Sc cutoff t t') where
  toFun f := E.recover (E.act f E.vacuum)
  map_add' := by intros; simp
  map_smul' := by intros; simp

/-- Source placement fixes the order: first the coefficient, then the affine map. -/
theorem observe_source (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    (hf : sourceCoefficientHom D Sc a f ∈ ExtendedAtMost D Sc t t' d) :
    E.observe (upwardCoefficientMap D Sc cs μ t t' (sourceCoefficientHom D Sc a f)) =
      (ELVRelationSpan D Sc cutoff t t').mkQ (sourceCoefficientHom D Sc a f) := by
  rw [upwardCoefficientMap_source]
  change E.recover (E.act (_ ≫ _) E.vacuum) = _
  rw [E.act_comp]
  change E.recover (E.act _ (E.sourceAct _ E.vacuum)) = _
  rw [← E.bubbles_eq, E.normalized_bubbles]
  exact E.affine_coordinates a f hf

/-- The pure coefficient identity extends over the bounded joint PBW span. -/
theorem observe_coefficient (f : coefficientObj D Sc t ⟶ coefficientObj D Sc t')
    (hf : f ∈ ExtendedAtMost D Sc t t' d) :
    E.observe (upwardCoefficientMap D Sc cs μ t t' f) =
      (ELVRelationSpan D Sc cutoff t t').mkQ f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨a, i⟩, hi, rfl⟩ := hf
    rw [extensionBasis_apply]
    apply E.observe_source
    rw [← extensionBasis_apply]
    exact Submodule.subset_span ⟨(a, i), hi, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul r x _ hx => simpa only [map_smul] using congrArg (r • ·) hx

end BoundedCyclicRecovery

/-- Conditional upward independence at a prescribed weight and word pair.
For each degree choose a colourwise cutoff, a common lower bound and recovery
at that pair and degree only. No action, vacuum or recovery is assumed injective
or nonzero. Construction of these cyclic data remains a separate obligation. -/
theorem upwardCoefficientMap_injective_of_bounded_cyclic_recovery
    (μ : X) (t t' : List I)
    (h : ∀ d, ∃ cutoff : I → ℕ, ∃ N : ℕ,
      (∀ i, N ≤ cutoff i) ∧ d + 2 * t.length.choose 2 < N ∧
      Nonempty (BoundedCyclicRecovery D Sc cs μ t t' d cutoff)) :
    Function.Injective (upwardCoefficientMap D Sc cs μ t t') := by
  suffices hzero : ∀ f, upwardCoefficientMap D Sc cs μ t t' f = 0 → f = 0 by
    intro f g hfg
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hfg, sub_self]
  intro f hf
  obtain ⟨d, hd⟩ := exists_mem_extendedAtMost D Sc t t' f
  obtain ⟨cutoff, N, hN, hb, ⟨E⟩⟩ := h d
  have he := E.observe_coefficient f hd
  have hz : (ELVRelationSpan D Sc cutoff t t').mkQ f = 0 := by
    simpa [hf] using he.symm
  have hinj := elv_quotient_injective_on_extendedAtMost D Sc (t := t) (t' := t')
    (d := d) hN hb
  exact congrArg Subtype.val (hinj (a₁ := ⟨f, hd⟩) (a₂ := 0) (by simpa using hz))

end OddMath.QuiverHecke
