/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSourceWord
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumHomAction

/-! # Evaluation of an entire extended vacuum word

`wordIsoAt_doubleEvaluation` identifies the existing entire-word isomorphism
with two independently specified successive representable evaluations after
mapping the existing prefix isomorphism twice. The terminal-content cast is
retained. This supplies the recursive-word side of the comparison needed for
the source-and-reservoir Hom action. It does not yet identify these maps with
the named `wordPairCoordinates` or prove that combined crossing action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.VacuumSourceComparison
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem iteratedForward_total (β : Multiset I) (σ τ : List I)
    (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N ((β + (σ : Multiset I)) + (τ : Multiset I))) :
    iteratedForward D Sc cutoff N β σ τ _ rfl v w =
      (((contentInduction D Sc cutoff N (β + (σ : Multiset I)) τ).map
        (InductionRepresentable.iso D Sc cutoff N β σ v).hom) ≫
        (InductionRepresentable.iso D Sc cutoff N (β + (σ : Multiset I)) τ
          ((contentAppend D Sc cutoff N β σ).obj v)).hom).total w := by
  rw [Superfunctor.comp_total]
  have hz := Superfunctor.app_eq_zero_of_mem
    (IsSuperfunctor.map_mem
      (F := contentInduction D Sc cutoff N (β + (σ : Multiset I)) τ)
      (representableIso_even D Sc cutoff N β σ v))
    (show (1 : ZMod 2) ≠ 0 by decide) w
  simp only [SuperNatTrans.total, hz, add_zero]
  simp only [InductionRepresentable.iso, InductionRepresentable.forwardTransform_app,
    ite_true, one_ne_zero, ite_false, add_zero]
  rfl

private theorem module_comp_total {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M L P : Superfunctor k C (SVec k)} (f : M ⟶ L) (g : L ⟶ P) (w : C) :
    (f ≫ g).total w = g.total w ∘ₗ f.total w := Superfunctor.comp_total f g w

/-- The existing recursive isomorphism for the whole extended word, before
transport to a separately named terminal content. -/
theorem wordIso_total_pair (ρ : List I) (i j : I)
    (w : ContentCategory D Sc cutoff N (VacuumRepresentable.content (j :: i :: ρ))) :
    (VacuumRepresentable.wordIso D Sc cutoff N (j :: i :: ρ)).hom.total w =
      iteratedForward D Sc cutoff N (VacuumRepresentable.content ρ) [i] [j] _ rfl
        (VacuumRepresentable.wordObject D Sc cutoff N ρ) w ∘ₗ
      (((contentE D Sc cutoff N (VacuumRepresentable.content ρ) i ⋙
        contentE D Sc cutoff N (VacuumRepresentable.content (i :: ρ)) j).map
          (VacuumRepresentable.wordIso D Sc cutoff N ρ).hom).total w) := by
  rw [iteratedForward_total]
  erw [← module_comp_total]
  congr 1
  simp only [VacuumRepresentable.wordIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rfl

/-- Two successive evaluations, independently of the full-word isomorphism. -/
def wordDoubleEvaluationAt (ρ : List I) (i j : I) (γ : Multiset I)
    (he : VacuumRepresentable.content (j :: i :: ρ) = γ)
    (w : ContentCategory D Sc cutoff N γ) :
    (VacuumRepresentable.wordModuleAt D Sc cutoff N (j :: i :: ρ) γ he).obj w →ₗ[k]
      (VacuumRepresentable.wordObjectAt D Sc cutoff N (j :: i :: ρ) γ he ⟶ w) := by
  subst γ
  exact iteratedForward D Sc cutoff N (VacuumRepresentable.content ρ) [i] [j] _ rfl
    (VacuumRepresentable.wordObject D Sc cutoff N ρ) w ∘ₗ
    (((contentE D Sc cutoff N (VacuumRepresentable.content ρ) i ⋙
      contentE D Sc cutoff N (VacuumRepresentable.content (i :: ρ)) j).map
        (VacuumRepresentable.wordIso D Sc cutoff N ρ).hom).total w)

/-- Compatibility for the entire extended word, not only its prefix. -/
theorem wordIsoAt_doubleEvaluation (ρ : List I) (i j : I) (γ : Multiset I)
    (he : VacuumRepresentable.content (j :: i :: ρ) = γ)
    (w : ContentCategory D Sc cutoff N γ) :
    (VacuumRepresentable.wordIsoAt D Sc cutoff N (j :: i :: ρ) γ he).hom.total w =
      wordDoubleEvaluationAt D Sc cutoff N ρ i j γ he w := by
  subst γ
  exact wordIso_total_pair D Sc cutoff N ρ i j w

end OddMath.QuiverHecke.ELVOld.VacuumSourceComparison
