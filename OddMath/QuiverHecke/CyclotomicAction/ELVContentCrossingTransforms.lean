/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleCrossingNormalization

/-! # Natural families of independently induced content crossings

The three-factor braid fields in Brundan–Ellis Definition 1.5 require
supernatural transformations. The data here are the independently induced
pair morphisms; their naturality follows from their checked source comparison.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem supernatural_congr
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {p : ZMod 2}
    {x y : ∀ M, F.obj M ⟶ G.obj M}
    (hx : IsSupernatural k p x) (h : ∀ M, x M = y M) :
    IsSupernatural k p y := by
  have hxy := funext h
  cases hxy
  exact hx

private theorem supernatural_total
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M}
    (hx : IsSupernatural k p x) (M : C) :
    hx.toSuperNatTrans.total M = x M := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

section Prefix
variable (β : Multiset I) (i j l : I) (δ γ : Multiset I)
  (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
  (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
  (h : β + ([i,j,l] : Multiset I) = γ)
  (ht : β + ([j,i,l] : Multiset I) = γ)
  (hγ : δ + ([l] : Multiset I) = γ)

/-- Naturality of the independently induced prefix pair morphisms. -/
theorem contentPrefixCrossMorphism_supernatural :
    IsSupernatural k (D.parity i * D.parity j)
      (fun M => contentPrefixCrossMorphism D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ M) :=
  supernatural_congr
    ((contentETripleTransform D Sc cutoff N (β := β) (γ := γ)
      (i := i) (j := j) (l := l) (a := j) (b := i) (c := l)
      h ht (contentTriplePrefixAffine_mem D Sc i j l)).isSupernatural
        (D.parity i * D.parity j))
    (contentETripleTransform_prefix_cross D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ)

/-- The component data are the pair morphisms induced through the third factor. -/
def contentPrefixCrossTransform :
    SuperNatTrans k (contentETripleTo D Sc cutoff N β j i l γ ht)
      (contentETripleTo D Sc cutoff N β i j l γ h) :=
  (contentPrefixCrossMorphism_supernatural D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ).toSuperNatTrans

theorem contentPrefixCrossTransform_component (M : ContentModules D Sc cutoff N β) :
    (contentPrefixCrossTransform D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ).app
      (D.parity i * D.parity j) M =
    contentPrefixCrossMorphism D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ M :=
  congrFun (IsSupernatural.toSuperNatTrans_app
    (contentPrefixCrossMorphism_supernatural D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ)) M

theorem contentPrefixCrossTransform_total (M : ContentModules D Sc cutoff N β) :
    (contentPrefixCrossTransform D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ).total M =
    contentPrefixCrossMorphism D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ M :=
  supernatural_total
    (contentPrefixCrossMorphism_supernatural D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ) M

/-- Total evaluation is the independently constructed component used by the braid. -/
theorem contentPrefixCrossTransform_evaluation
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentPrefixCrossTransform D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ).total M).total z =
    contentPrefixCrossComponent D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ M z :=
  congrArg (fun f => f.total z)
    (contentPrefixCrossTransform_total D Sc cutoff N β i j l δ γ hδ hδ' h ht hγ M)
end Prefix
end OddMath.QuiverHecke.ELVOld
