/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairTensor

/-! # Whiskered single-letter dots and the pair quadratic

The canonical transported positioned dots equal independently constructed
single-letter actions. The inner dot uses induction on the existing
`contentInductionDot`; the outer dot retains the explicit target-content
recast. The original-Sc ordered quadratic is consequently a relation in
these independently whiskered dots, not merely in conjugated block dots.
Triple crossing and associativity coherence are separate obligations.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Evaluation of induction on a homogeneous module map. The statement keeps
the actual induced SVec objects on the left and the raw formula on the right. -/
theorem contentInductionMap_total_of_mem
    {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {F G : Superfunctor k C (SVec k)} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (z : B) :
    ((BalancedInduction.induction J).map f).total z = BalancedInduction.mapComponent J f p z := by
  have hm := Supercategory.map_mem (BalancedInduction.induction J) hf
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 1) (by decide), add_zero]
    rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 0) (by decide), zero_add]
    rfl

/-- The component of the actual induction transformation has the raw balanced
formula. This comparison is generic in both content equalities. -/
theorem contentInductionTransform_total {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    {p : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentInductionTransform D Sc cutoff N hσ hτ ha).app p M).total z =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M z := by
  have h := congrFun (IsSupernatural.toSuperNatTrans_app
    (BalancedInduction.transformComponent_supernatural
      (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha))) M
  have ht :
      ((BalancedInduction.transformLinear_supernatural
        (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M).toSuperNatTrans).total z =
        BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M z := by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]
  exact (congrArg (fun f => f.total z) h).trans ht

theorem contentInductionDot_component (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β) :
    (contentInductionDot D Sc cutoff N β i).app (D.parity i) M =
      BalancedInduction.transformComponent
        (contentAppendTo_supernatural D Sc cutoff N rfl rfl (firstDot_parity D Sc i [])) M := by
  exact congrFun (IsSupernatural.toSuperNatTrans_app
    (BalancedInduction.transformComponent_supernatural
      (contentAppendTo_supernatural D Sc cutoff N rfl rfl (firstDot_parity D Sc i [])))) M

/-- The first single-letter dot, acted on by the actual second induction functor. -/
def contentEPairInnerDot (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I))) :
    Module.End k (ContentEPairSpace D Sc cutoff N β i j _ rfl M w) :=
  ((contentInductionTo D Sc cutoff N (β + ([i] : Multiset I)) [j]
      (β + ([i,j] : Multiset I)) (contentPair_sum β i j).symm).map
    ((contentInductionDot D Sc cutoff N β i).app (D.parity i) M)).total w

/-- The actual single-letter dot component at the explicitly recast target. -/
def contentEPairOuterDot (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I))) :
    Module.End k (ContentEPairSpace D Sc cutoff N β i j _ rfl M w) :=
  ((contentInductionTransform D Sc cutoff N
    (β := β + ([i] : Multiset I)) (γ := β + ([i,j] : Multiset I))
    (contentPair_sum β i j).symm (contentPair_sum β i j).symm
    (firstDot_parity D Sc j [])).app (D.parity j)
    (BalancedInduction.induced (contentAppendTo D Sc cutoff N β [i] _ rfl) M)).total w

end OddMath.QuiverHecke.ELVOld

