/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCrossingTransforms
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSuffixCrossingTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVContentUncorrectedBraid

/-! # The uncorrected braid of independent supernatural crossing families

Brundan–Ellis Definition 1.5: this is the whole natural-family relation, before
transport to the weight-product functors. Both paths retain the independently
induced prefix and suffix components.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem double_total_vcomp
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G H : C ⥤ Superfunctor k B (SVec.{u} k)}
    (s : SuperNatTrans k F G) (t : SuperNatTrans k G H) (M : C) (z : B) :
    ((s.vcomp t).total M).total z = (s.total M).total z ≫ (t.total M).total z := by
  rw [SuperNatTrans.vcomp_total, Superfunctor.comp_total]

private theorem double_total_three
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F₀ F₁ F₂ F₃ : C ⥤ Superfunctor k B (SVec.{u} k)}
    (s : SuperNatTrans k F₀ F₁) (t : SuperNatTrans k F₁ F₂)
    (r : SuperNatTrans k F₂ F₃) (M : C) (z : B) :
    (((s.vcomp t).vcomp r).total M).total z =
      ((s.total M).total z ≫ (t.total M).total z) ≫ (r.total M).total z := by
  rw [double_total_vcomp, double_total_vcomp]

private theorem svec_comp3_congr {A B C E : SVec.{u} k}
    {f f' : A ⟶ B} {g g' : B ⟶ C} {h h' : C ⟶ E}
    (hf : f = f') (hg : g = g') (hh : h = h') :
    (f ≫ g) ≫ h = (f' ≫ g') ≫ h' := by
  cases hf
  cases hg
  cases hh
  rfl

def contentBraidLeftTransform (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h0 : β + ([i,j,l] : Multiset I) = γ)
    (h1 : β + ([j,i,l] : Multiset I) = γ)
    (h2 : β + ([j,l,i] : Multiset I) = γ)
    (h3 : β + ([l,j,i] : Multiset I) = γ)
    (δij : Multiset I)
    (hij : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δij)
    (hji : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δij)
    (hijγ : δij + ([l] : Multiset I) = γ)
    (δjl : Multiset I)
    (hjl : (β + ([j] : Multiset I)) + ([l] : Multiset I) = δjl)
    (hlj : (β + ([l] : Multiset I)) + ([j] : Multiset I) = δjl)
    (hjlγ : δjl + ([i] : Multiset I) = γ) :
    SuperNatTrans k (contentETripleTo D Sc cutoff N β l j i γ h3)
      (contentETripleTo D Sc cutoff N β i j l γ h0) :=
  ((contentPrefixCrossTransform D Sc cutoff N β j l i δjl γ hjl hlj h2 h3 hjlγ).vcomp
    (contentSuffixCrossTransform D Sc cutoff N β j i l γ h1 h2)).vcomp
    (contentPrefixCrossTransform D Sc cutoff N β i j l δij γ hij hji h0 h1 hijγ)

def contentBraidRightTransform (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h0 : β + ([i,j,l] : Multiset I) = γ)
    (h4 : β + ([i,l,j] : Multiset I) = γ)
    (h5 : β + ([l,i,j] : Multiset I) = γ)
    (h3 : β + ([l,j,i] : Multiset I) = γ)
    (δil : Multiset I)
    (hil : (β + ([i] : Multiset I)) + ([l] : Multiset I) = δil)
    (hli : (β + ([l] : Multiset I)) + ([i] : Multiset I) = δil)
    (hilγ : δil + ([j] : Multiset I) = γ) :
    SuperNatTrans k (contentETripleTo D Sc cutoff N β l j i γ h3)
      (contentETripleTo D Sc cutoff N β i j l γ h0) :=
  ((contentSuffixCrossTransform D Sc cutoff N β l i j γ h5 h3).vcomp
    (contentPrefixCrossTransform D Sc cutoff N β i l j δil γ hil hli h4 h5 hilγ)).vcomp
    (contentSuffixCrossTransform D Sc cutoff N β i j l γ h0 h4)


theorem contentBraidLeftTransform_evaluation (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h0 : β + ([i,j,l] : Multiset I) = γ)
    (h1 : β + ([j,i,l] : Multiset I) = γ)
    (h2 : β + ([j,l,i] : Multiset I) = γ)
    (h3 : β + ([l,j,i] : Multiset I) = γ)
    (δij : Multiset I)
    (hij : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δij)
    (hji : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δij)
    (hijγ : δij + ([l] : Multiset I) = γ)
    (δjl : Multiset I)
    (hjl : (β + ([j] : Multiset I)) + ([l] : Multiset I) = δjl)
    (hlj : (β + ([l] : Multiset I)) + ([j] : Multiset I) = δjl)
    (hjlγ : δjl + ([i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentBraidLeftTransform D Sc cutoff N β i j l γ h0 h1 h2 h3 δij hij hji hijγ δjl hjl hlj hjlγ).total M).total z =
      contentWhiskeredBraidLeft D Sc cutoff N β i j l γ h0 h1 h2 h3 δij hij hji hijγ δjl hjl hlj hjlγ M z := by
  exact (double_total_three
    (contentPrefixCrossTransform D Sc cutoff N β j l i δjl γ hjl hlj h2 h3 hjlγ)
    (contentSuffixCrossTransform D Sc cutoff N β j i l γ h1 h2)
    (contentPrefixCrossTransform D Sc cutoff N β i j l δij γ hij hji h0 h1 hijγ)
    M z).trans (svec_comp3_congr
    (A := ((contentETripleTo D Sc cutoff N β l j i γ h3).obj M).obj z)
    (B := ((contentETripleTo D Sc cutoff N β j l i γ h2).obj M).obj z)
    (C := ((contentETripleTo D Sc cutoff N β j i l γ h1).obj M).obj z)
    (E := ((contentETripleTo D Sc cutoff N β i j l γ h0).obj M).obj z)
    (contentPrefixCrossTransform_evaluation D Sc cutoff N β j l i δjl γ hjl hlj h2 h3 hjlγ M z)
    (contentSuffixCrossTransform_evaluation D Sc cutoff N β j i l γ h1 h2 M z)
    (contentPrefixCrossTransform_evaluation D Sc cutoff N β i j l δij γ hij hji h0 h1 hijγ M z))


theorem contentBraidRightTransform_evaluation (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h0 : β + ([i,j,l] : Multiset I) = γ)
    (h4 : β + ([i,l,j] : Multiset I) = γ)
    (h5 : β + ([l,i,j] : Multiset I) = γ)
    (h3 : β + ([l,j,i] : Multiset I) = γ)
    (δil : Multiset I)
    (hil : (β + ([i] : Multiset I)) + ([l] : Multiset I) = δil)
    (hli : (β + ([l] : Multiset I)) + ([i] : Multiset I) = δil)
    (hilγ : δil + ([j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentBraidRightTransform D Sc cutoff N β i j l γ h0 h4 h5 h3 δil hil hli hilγ).total M).total z =
      contentWhiskeredBraidRight D Sc cutoff N β i j l γ h0 h4 h5 h3 δil hil hli hilγ M z := by
  exact (double_total_three
    (contentSuffixCrossTransform D Sc cutoff N β l i j γ h5 h3)
    (contentPrefixCrossTransform D Sc cutoff N β i l j δil γ hil hli h4 h5 hilγ)
    (contentSuffixCrossTransform D Sc cutoff N β i j l γ h0 h4)
    M z).trans (svec_comp3_congr
    (A := ((contentETripleTo D Sc cutoff N β l j i γ h3).obj M).obj z)
    (B := ((contentETripleTo D Sc cutoff N β l i j γ h5).obj M).obj z)
    (C := ((contentETripleTo D Sc cutoff N β i l j γ h4).obj M).obj z)
    (E := ((contentETripleTo D Sc cutoff N β i j l γ h0).obj M).obj z)
    (contentSuffixCrossTransform_evaluation D Sc cutoff N β l i j γ h5 h3 M z)
    (contentPrefixCrossTransform_evaluation D Sc cutoff N β i l j δil γ hil hli h4 h5 hilγ M z)
    (contentSuffixCrossTransform_evaluation D Sc cutoff N β i j l γ h0 h4 M z))

/-- The whole supernatural braid on independently induced crossings, outside
    the repeated-outer correction case. -/
theorem contentBraidTransform_braid (β : Multiset I) (i j l : I)
    (hb : ¬ (i = l ∧ i ≠ j)) (γ : Multiset I)
    (h0 : β + ([i,j,l] : Multiset I) = γ)
    (h1 : β + ([j,i,l] : Multiset I) = γ)
    (h2 : β + ([j,l,i] : Multiset I) = γ)
    (h3 : β + ([l,j,i] : Multiset I) = γ)
    (h4 : β + ([i,l,j] : Multiset I) = γ)
    (h5 : β + ([l,i,j] : Multiset I) = γ)
    (δij : Multiset I)
    (hij : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δij)
    (hji : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δij)
    (hijγ : δij + ([l] : Multiset I) = γ)
    (δil : Multiset I)
    (hil : (β + ([i] : Multiset I)) + ([l] : Multiset I) = δil)
    (hli : (β + ([l] : Multiset I)) + ([i] : Multiset I) = δil)
    (hilγ : δil + ([j] : Multiset I) = γ)
    (δjl : Multiset I)
    (hjl : (β + ([j] : Multiset I)) + ([l] : Multiset I) = δjl)
    (hlj : (β + ([l] : Multiset I)) + ([j] : Multiset I) = δjl)
    (hjlγ : δjl + ([i] : Multiset I) = γ)
    : contentBraidLeftTransform D Sc cutoff N β i j l γ h0 h1 h2 h3 δij hij hji hijγ δjl hjl hlj hjlγ =
      contentBraidRightTransform D Sc cutoff N β i j l γ h0 h4 h5 h3 δil hil hli hilγ := by
  apply BalancedInduction.supernatural_ext_total
  intro M
  apply BalancedInduction.supernatural_ext_total
  intro z
  exact (contentBraidLeftTransform_evaluation D Sc cutoff N β i j l γ h0 h1 h2 h3 δij hij hji hijγ δjl hjl hlj hjlγ M z).trans
    ((contentWhiskered_braid D Sc cutoff N β i j l hb γ h0 h1 h2 h3 h4 h5
      δij hij hji hijγ δil hil hli hilγ δjl hjl hlj hjlγ M z).trans
      (contentBraidRightTransform_evaluation D Sc cutoff N β i j l γ h0 h4 h5 h3 δil hil hli hilγ M z).symm)
end OddMath.QuiverHecke.ELVOld
