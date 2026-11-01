/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleCrossingNormalization

/-! # The suffix pair crossing as a natural family

This supplies the other independently induced crossing family required by the
three-factor braid fields of Brundan–Ellis Definition 1.5.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Total components detect a supernatural transformation, without a
homogeneity assumption. Used twice for module-valued natural families. -/
theorem BalancedInduction.supernatural_ext_total
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {f g : SuperNatTrans k F G}
    (h : ∀ M, f.total M = g.total M) : f = g := by
  apply SuperNatTrans.ext
  funext p M
  have hp (t : SuperNatTrans k F G) : proj k p (t.total M) = t.app p M := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact proj_eq_of_add rfl (t.app_mem 0 M) (t.app_mem 1 M)
    · exact proj_eq_of_add (add_comm _ _) (t.app_mem 1 M)
        (by simpa using t.app_mem 0 M)
  rw [← hp f, ← hp g, h M]

/-- One target witness for the suffix pair on the first induced module. -/
theorem contentSuffix_target_eq (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) :
    (β + ([i] : Multiset I)) + ([j,l] : Multiset I) = γ := by
  rw [add_assoc]
  exact h

section Suffix
variable (β : Multiset I) (i j l : I) (γ : Multiset I)
  (h : β + ([i,j,l] : Multiset I) = γ)
  (ht : β + ([i,l,j] : Multiset I) = γ)

/-- The independent pair component on the first single-letter induction. -/
def contentSuffixCrossMorphism (M : ContentModules D Sc cutoff N β) :
    (contentETripleTo D Sc cutoff N β i l j γ ht).obj M ⟶
      (contentETripleTo D Sc cutoff N β i j l γ h).obj M :=
  (contentEPairCrossTransform D Sc cutoff N (β + ([i] : Multiset I)) j l γ
    (contentSuffix_target_eq β i j l γ h) (contentSuffix_target_eq β i l j γ ht)).app
    (D.parity j * D.parity l)
    ((contentE D Sc cutoff N β i).obj M)

/-- The source comparison is used to prove naturality of the independent family. -/
theorem contentSuffixCrossMorphism_source (M : ContentModules D Sc cutoff N β) :
    (contentETripleTransform D Sc cutoff N (β := β) (γ := γ)
      (i := i) (j := j) (l := l) (a := i) (b := l) (c := j) h ht
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
        (contentCrossAffine_mem D Sc j l))).app (D.parity j * D.parity l) M =
    contentSuffixCrossMorphism D Sc cutoff N β i j l γ h ht M := by
  apply BalancedInduction.supernatural_ext_total
  intro z
  exact (contentETripleTransform_total D Sc cutoff N
    (β := β) (γ := γ) (i := i) (j := j) (l := l) (a := i) (b := l) (c := j) h ht
    (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
      (contentCrossAffine_mem D Sc j l)) M z).trans
    ((contentETripleMap_suffix_cross D Sc cutoff N β i j l γ h ht
      (contentSuffix_target_eq β i j l γ h) (contentSuffix_target_eq β i l j γ ht) M z).trans
      (contentEPairCross_total D Sc cutoff N (β + ([i] : Multiset I)) j l γ
        (contentSuffix_target_eq β i j l γ h) (contentSuffix_target_eq β i l j γ ht)
        ((contentE D Sc cutoff N β i).obj M) z).symm)

/-- Naturality follows with no naturality premise on the independent component. -/
theorem contentSuffixCrossMorphism_supernatural :
    IsSupernatural k (D.parity j * D.parity l)
      (fun M => contentSuffixCrossMorphism D Sc cutoff N β i j l γ h ht M) := by
  have hx := (contentETripleTransform D Sc cutoff N (β := β) (γ := γ)
    (i := i) (j := j) (l := l) (a := i) (b := l) (c := j) h ht
    (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
      (contentCrossAffine_mem D Sc j l))).isSupernatural (D.parity j * D.parity l)
  have he := funext (contentSuffixCrossMorphism_source D Sc cutoff N β i j l γ h ht)
  exact he ▸ hx

def contentSuffixCrossTransform :
    SuperNatTrans k (contentETripleTo D Sc cutoff N β i l j γ ht)
      (contentETripleTo D Sc cutoff N β i j l γ h) :=
  (contentSuffixCrossMorphism_supernatural D Sc cutoff N β i j l γ h ht).toSuperNatTrans

private theorem family_total
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M}
    (hx : IsSupernatural k p x) (M : C) :
    hx.toSuperNatTrans.total M = x M := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

theorem contentSuffixCrossTransform_total (M : ContentModules D Sc cutoff N β) :
    (contentSuffixCrossTransform D Sc cutoff N β i j l γ h ht).total M =
    contentSuffixCrossMorphism D Sc cutoff N β i j l γ h ht M :=
  family_total (contentSuffixCrossMorphism_supernatural D Sc cutoff N β i j l γ h ht) M

/-- The total family evaluates to the suffix component used by the braid. -/
theorem contentSuffixCrossTransform_evaluation
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentSuffixCrossTransform D Sc cutoff N β i j l γ h ht).total M).total z =
    contentWhiskeredSuffixCross D Sc cutoff N β i j l γ h ht M z := by
  have h1 := congrArg (fun f => f.total z)
    (contentSuffixCrossTransform_total D Sc cutoff N β i j l γ h ht M)
  have h2 := congrArg (fun f => f.total z)
    (contentSuffixCrossMorphism_source D Sc cutoff N β i j l γ h ht M)
  exact h1.trans (h2.symm.trans
    ((contentETripleTransform_total D Sc cutoff N
      (β := β) (γ := γ) (i := i) (j := j) (l := l) (a := i) (b := l) (c := j) h ht
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
        (contentCrossAffine_mem D Sc j l)) M z).trans
      (contentWhiskeredSuffixCross_comparison D Sc cutoff N β i j l γ h ht M z).symm))
end Suffix
end OddMath.QuiverHecke.ELVOld
