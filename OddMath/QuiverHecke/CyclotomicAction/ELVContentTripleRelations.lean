/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Whiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMixedPolynomial

/-! # Canonical triple-E transport of the corrected mixed braid

Advances `DeformedActionAssembly.md` §6 with an even all-module comparison
from three successive single-letter E functors to block induction. Intermediate
and final content equalities are explicit. The same recursively constructed
comparison is used at every word, so both three-crossing paths transport
coherently; the checked source maps and both equal-crossing minus signs are
retained. The polynomial has exactly original Sc and three ordered dot powers.
The linear arrows are evaluated genuine supernatural transformations, and the
residual twist on the entire coefficient/diagram kernel is stated explicitly.

This proves path compatibility for these canonical transported source maps.
It does not yet identify them with independently whiskered pair crossings/dots
or prove equality of the two possible recursive associativity comparisons.
No weight assembly, local inversions or nondegeneracy is claimed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem evenComparison_trans
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G H : C ⥤ B} (e : F ≅ G) (f : G ≅ H) (M : C)
    (he : EvenComparisonAt (k := k) e M) (hf : EvenComparisonAt (k := k) f M) :
    EvenComparisonAt (k := k) (e ≪≫ f) M :=
  ⟨comp_mem he.1 hf.1, comp_mem hf.2 he.2⟩

private theorem evenComparison_whisker
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : C ⥤ B} (e : F ≅ G) (K : B ⥤ E)
    [K.Additive] [K.Linear k] [IsSuperfunctor k K] (M : C)
    (he : EvenComparisonAt (k := k) e M) :
    EvenComparisonAt (k := k) (Functor.isoWhiskerRight e K) M :=
  ⟨Supercategory.map_mem K he.1, Supercategory.map_mem K he.2⟩

private theorem tripleIso_transport
    {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {A B E F : Superfunctor k C (SVec k)} (e : A ≅ B) (f : E ≅ F)
    (a : B ⟶ F) (w : C) (b : B.obj w →ₗ[k] F.obj w) (h : a.total w = b) :
    ((e.hom ≫ a) ≫ f.inv).total w =
      (moduleIsoLinearEquiv f w).symm.toLinearMap.comp
        (b.comp (moduleIsoLinearEquiv e w).toLinearMap) := by
  rw [Superfunctor.comp_total, Superfunctor.comp_total, h]
  rfl

private theorem tripleComparison_app
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G F' G' : C ⥤ B}
    [F.Additive] [F.Linear k] [G.Additive] [G.Linear k]
    [F'.Additive] [F'.Linear k] [G'.Additive] [G'.Linear k]
    (e : F' ≅ F) (f : G' ≅ G)
    (he : ∀ M, EvenComparisonAt (k := k) e M)
    (hf : ∀ M, EvenComparisonAt (k := k) f M)
    {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M} (hx : IsSupernatural k p x) (M : C) :
    ((evenComparison_supernatural e f he hf hx).toSuperNatTrans.app p M) =
      (e.hom.app M ≫ x M) ≫ f.inv.app M :=
  congrFun (IsSupernatural.toSuperNatTrans_app (evenComparison_supernatural e f he hf hx)) M

private theorem tripleHomogeneous_total
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M}
    (hx : IsSupernatural k p x) (M : C) : hx.toSuperNatTrans.total M = x M := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

theorem contentAppend_compTo_eq (β : Multiset I) (σ : List I) (δ : Multiset I)
    (hδ : β + (σ : Multiset I) = δ) (τ : List I) (γ : Multiset I)
    (hγ : δ + (τ : Multiset I) = γ)
    (h : β + ((σ ++ τ : List I) : Multiset I) = γ) :
    contentAppendTo D Sc cutoff N β σ δ hδ ⋙ contentAppendTo D Sc cutoff N δ τ γ hγ =
      contentAppendTo D Sc cutoff N β (σ ++ τ) γ h := by
  subst δ
  exact contentAppend_comp_eq D Sc cutoff N β σ τ γ hγ h

/-- The intermediate content equality is explicit as well. -/
def contentInductionCompTo (β : Multiset I) (σ : List I) (δ : Multiset I)
    (hδ : β + (σ : Multiset I) = δ) (τ : List I) (γ : Multiset I)
    (hγ : δ + (τ : Multiset I) = γ) (h : β + ((σ ++ τ : List I) : Multiset I) = γ) :
    contentInductionTo D Sc cutoff N β σ δ hδ ⋙ contentInductionTo D Sc cutoff N δ τ γ hγ ≅
      contentInductionTo D Sc cutoff N β (σ ++ τ) γ h := by
  subst δ
  exact contentInductionComp D Sc cutoff N β σ τ γ hγ h

theorem contentInductionCompTo_mem (β : Multiset I) (σ : List I) (δ : Multiset I)
    (hδ : β + (σ : Multiset I) = δ) (τ : List I) (γ : Multiset I)
    (hγ : δ + (τ : Multiset I) = γ) (h : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) :
    EvenComparisonAt (k := k) (contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h) M := by
  subst δ
  exact contentInductionComp_mem D Sc cutoff N β σ τ γ hγ h M

/-- Three actual single-letter E functors; only the final content is recast. -/
abbrev contentETripleTo (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) :=
  (contentE D Sc cutoff N β i ⋙ contentE D Sc cutoff N (β + ([i] : Multiset I)) j) ⋙
    contentInductionTo D Sc cutoff N ((β + ([i] : Multiset I)) + ([j] : Multiset I)) [l] γ
      (by rw [add_assoc, add_assoc]; exact h)

def contentETripleComparison (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) :
    contentETripleTo D Sc cutoff N β i j l γ h ≅ contentInductionTo D Sc cutoff N β [i,j,l] γ h :=
  Functor.isoWhiskerRight (contentEPairComparison D Sc cutoff N β i j)
    (contentInductionTo D Sc cutoff N ((β + ([i] : Multiset I)) + ([j] : Multiset I)) [l] γ
      (by rw [add_assoc, add_assoc]; exact h)) ≪≫
  contentInductionCompTo D Sc cutoff N β [i,j]
    ((β + ([i] : Multiset I)) + ([j] : Multiset I)) (by rw [add_assoc]; rfl)
    [l] γ _ h

theorem contentETripleComparison_mem (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β) :
    EvenComparisonAt (k := k) (contentETripleComparison D Sc cutoff N β i j l γ h) M :=
  evenComparison_trans _ _ M
    (evenComparison_whisker (contentEPairComparison D Sc cutoff N β i j)
      (contentInductionTo D Sc cutoff N ((β + ([i] : Multiset I)) + ([j] : Multiset I)) [l] γ
        (by rw [add_assoc, add_assoc]; exact h)) M
      (contentInductionComp_mem D Sc cutoff N β [i] [j] _ rfl _ M))
    (contentInductionCompTo_mem D Sc cutoff N β [i,j]
      ((β + ([i] : Multiset I)) + ([j] : Multiset I)) (by rw [add_assoc]; rfl) [l] γ _ h M)

abbrev ContentETripleSpace (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) :=
  BalancedInduction.Obj
    (contentAppendTo D Sc cutoff N ((β + ([i] : Multiset I)) + ([j] : Multiset I)) [l] γ
      (by rw [add_assoc, add_assoc]; exact h))
    (BalancedInduction.induced
      (contentAppend D Sc cutoff N (β + ([i] : Multiset I)) [j])
      (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M)).toFunctor w

def contentETripleEquiv (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) :
    ContentETripleSpace D Sc cutoff N β i j l γ h M w ≃ₗ[k]
      BalancedInduction.Obj (contentAppendTo D Sc cutoff N β [i,j,l] γ h) M.toFunctor w :=
  moduleIsoLinearEquiv ((contentETripleComparison D Sc cutoff N β i j l γ h).app M) w

/-- The source-positioned map on three successive E functors. -/
def contentETripleMap {β γ : Multiset I} {i j l a b c : I}
    (hσ : β + ([i,j,l] : Multiset I) = γ)
    (hτ : β + ([a,b,c] : Multiset I) = γ) {p : ZMod 2}
    {f : (pres D Sc).obj (ob D [i,j,l]) ⟶ (pres D Sc).obj (ob D [a,b,c])}
    (hf : f ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ) :
    ContentETripleSpace D Sc cutoff N β a b c γ hτ M w →ₗ[k]
      ContentETripleSpace D Sc cutoff N β i j l γ hσ M w :=
  (contentETripleEquiv D Sc cutoff N β i j l γ hσ M w).symm.toLinearMap.comp
    ((BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N hσ hτ hf) M w).comp
      (contentETripleEquiv D Sc cutoff N β a b c γ hτ M w).toLinearMap)

/-- A single comparison per word makes every transported arrow commute with it. -/
theorem contentETripleMap_comparison {β γ : Multiset I} {i j l a b c : I}
    (hσ : β + ([i,j,l] : Multiset I) = γ)
    (hτ : β + ([a,b,c] : Multiset I) = γ) {p : ZMod 2}
    {f : (pres D Sc).obj (ob D [i,j,l]) ⟶ (pres D Sc).obj (ob D [a,b,c])}
    (hf : f ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ) :
    (contentETripleEquiv D Sc cutoff N β i j l γ hσ M w).toLinearMap.comp
      (contentETripleMap D Sc cutoff N hσ hτ hf M w) =
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N hσ hτ hf) M w).comp
        (contentETripleEquiv D Sc cutoff N β a b c γ hτ M w).toLinearMap := by
  apply LinearMap.ext
  intro x
  exact (contentETripleEquiv D Sc cutoff N β i j l γ hσ M w).apply_symm_apply _

def contentETripleTransform {β γ : Multiset I} {i j l a b c : I}
    (hσ : β + ([i,j,l] : Multiset I) = γ)
    (hτ : β + ([a,b,c] : Multiset I) = γ) {p : ZMod 2}
    {f : (pres D Sc).obj (ob D [i,j,l]) ⟶ (pres D Sc).obj (ob D [a,b,c])}
    (hf : f ∈ parity (R := k) _ _ p) :
    SuperNatTrans k (contentETripleTo D Sc cutoff N β a b c γ hτ)
      (contentETripleTo D Sc cutoff N β i j l γ hσ) :=
  (evenComparison_supernatural
    (contentETripleComparison D Sc cutoff N β a b c γ hτ)
    (contentETripleComparison D Sc cutoff N β i j l γ hσ)
    (contentETripleComparison_mem D Sc cutoff N β a b c γ hτ)
    (contentETripleComparison_mem D Sc cutoff N β i j l γ hσ)
    ((contentInductionTransform D Sc cutoff N hσ hτ hf).isSupernatural p)).toSuperNatTrans

theorem contentETripleTransform_component {β γ : Multiset I} {i j l a b c : I}
    (hσ : β + ([i,j,l] : Multiset I) = γ)
    (hτ : β + ([a,b,c] : Multiset I) = γ) {p : ZMod 2}
    {f : (pres D Sc).obj (ob D [i,j,l]) ⟶ (pres D Sc).obj (ob D [a,b,c])}
    (hf : f ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) :
    (contentETripleTransform D Sc cutoff N hσ hτ hf).app p M =
      ((contentETripleComparison D Sc cutoff N β a b c γ hτ).hom.app M ≫
        (contentInductionTransform D Sc cutoff N hσ hτ hf).app p M) ≫
        (contentETripleComparison D Sc cutoff N β i j l γ hσ).inv.app M :=
  tripleComparison_app
    (contentETripleComparison D Sc cutoff N β a b c γ hτ)
    (contentETripleComparison D Sc cutoff N β i j l γ hσ)
    (contentETripleComparison_mem D Sc cutoff N β a b c γ hτ)
    (contentETripleComparison_mem D Sc cutoff N β i j l γ hσ)
    ((contentInductionTransform D Sc cutoff N hσ hτ hf).isSupernatural p) M

private theorem tripleBlock_total {β γ : Multiset I} {i j l a b c : I}
    (hσ : β + ([i,j,l] : Multiset I) = γ)
    (hτ : β + ([a,b,c] : Multiset I) = γ) {p : ZMod 2}
    {f : (pres D Sc).obj (ob D [i,j,l]) ⟶ (pres D Sc).obj (ob D [a,b,c])}
    (hf : f ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ) :
    ((contentInductionTransform D Sc cutoff N hσ hτ hf).app p M).total w =
      BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hσ hτ hf) M w := by
  have h := congrFun (IsSupernatural.toSuperNatTrans_app
    (BalancedInduction.transformComponent_supernatural
      (contentAppendTo_supernatural D Sc cutoff N hσ hτ hf))) M
  exact (congrArg (fun a => a.total w) h).trans
    (tripleHomogeneous_total
      (BalancedInduction.transformLinear_supernatural
        (contentAppendTo_supernatural D Sc cutoff N hσ hτ hf) M) w)

/-- The linear maps in the mixed braid are the genuine supernatural components. -/
theorem contentETripleTransform_total {β γ : Multiset I} {i j l a b c : I}
    (hσ : β + ([i,j,l] : Multiset I) = γ)
    (hτ : β + ([a,b,c] : Multiset I) = γ) {p : ZMod 2}
    {f : (pres D Sc).obj (ob D [i,j,l]) ⟶ (pres D Sc).obj (ob D [a,b,c])}
    (hf : f ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ) :
    ((contentETripleTransform D Sc cutoff N hσ hτ hf).app p M).total w =
      contentETripleMap D Sc cutoff N hσ hτ hf M w := by
  rw [contentETripleTransform_component]
  exact tripleIso_transport
    ((contentETripleComparison D Sc cutoff N β a b c γ hτ).app M)
    ((contentETripleComparison D Sc cutoff N β i j l γ hσ).app M)
    _ w _ (tripleBlock_total D Sc cutoff N hσ hτ hf M w)

def contentETriplePathIij (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M w) :=
  let A := contentETripleMap D Sc cutoff N rfl (content_triple_iij β i j)
    (contentTripleRight_parity D Sc i j i) M w
  let B := contentETripleMap D Sc cutoff N (content_triple_iij β i j) (content_triple_iij β i j)
    (contentTripleLeft_parity D Sc i i j) M w
  let C := contentETripleMap D Sc cutoff N (content_triple_iij β i j) rfl
    (contentTripleRight_parity D Sc i i j) M w
  A.comp ((-B).comp C)

def contentETriplePathJii (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M w) :=
  let E := contentETripleMap D Sc cutoff N rfl (content_triple_jii β i j)
    (contentTripleLeft_parity D Sc i j i) M w
  let F := contentETripleMap D Sc cutoff N (content_triple_jii β i j) (content_triple_jii β i j)
    (contentTripleRight_parity D Sc j i i) M w
  let G := contentETripleMap D Sc cutoff N (content_triple_jii β i j) rfl
    (contentTripleLeft_parity D Sc j i i) M w
  E.comp ((-F).comp G)

def contentETripleMixedBraid (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M w) :=
  contentETriplePathIij D Sc cutoff N β i j M w - contentETriplePathJii D Sc cutoff N β i j M w

private theorem transport_three
    {A B C E : Type*} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    [AddCommGroup E] [Module k E]
    (e : A ≃ₗ[k] B) (f : C ≃ₗ[k] E)
    (a : E →ₗ[k] B) (b : E →ₗ[k] E) (c : B →ₗ[k] E) :
    (e.symm.toLinearMap.comp (a.comp f.toLinearMap)).comp
      ((-(f.symm.toLinearMap.comp (b.comp f.toLinearMap))).comp
        (f.symm.toLinearMap.comp (c.comp e.toLinearMap))) =
      e.symm.conjAlgEquiv k (a.comp ((-b).comp c)) := by
  apply LinearMap.ext
  intro x
  change e.symm (a (f (-(f.symm (b (f (f.symm (c (e x))))))))) = e.symm (a (-(b (c (e x)))))
  rw [f.apply_symm_apply, map_neg, f.apply_symm_apply]

def contentBlockPathIij (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (BalancedInduction.Obj
      (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl) M.toFunctor w) :=
  let A := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N rfl (content_triple_iij β i j)
      (contentTripleRight_parity D Sc i j i)) M w
  let B := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_iij β i j) (content_triple_iij β i j)
      (contentTripleLeft_parity D Sc i i j)) M w
  let C := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_iij β i j) rfl
      (contentTripleRight_parity D Sc i i j)) M w
  A.comp ((-B).comp C)

theorem contentETriplePathIij_comparison (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    contentETriplePathIij D Sc cutoff N β i j M w =
      (contentETripleEquiv D Sc cutoff N β i j i _ rfl M w).symm.conjAlgEquiv k
        (contentBlockPathIij D Sc cutoff N β i j M w) :=
  transport_three
    (contentETripleEquiv D Sc cutoff N β i j i _ rfl M w)
    (contentETripleEquiv D Sc cutoff N β i i j _ (content_triple_iij β i j) M w)
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N rfl (content_triple_iij β i j)
        (contentTripleRight_parity D Sc i j i)) M w)
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N (content_triple_iij β i j) (content_triple_iij β i j)
        (contentTripleLeft_parity D Sc i i j)) M w)
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N (content_triple_iij β i j) rfl
        (contentTripleRight_parity D Sc i i j)) M w)

def contentBlockPathJii (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (BalancedInduction.Obj
      (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl) M.toFunctor w) :=
  let A := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N rfl (content_triple_jii β i j)
      (contentTripleLeft_parity D Sc i j i)) M w
  let B := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_jii β i j) (content_triple_jii β i j)
      (contentTripleRight_parity D Sc j i i)) M w
  let C := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_jii β i j) rfl
      (contentTripleLeft_parity D Sc j i i)) M w
  A.comp ((-B).comp C)

theorem contentETriplePathJii_comparison (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    contentETriplePathJii D Sc cutoff N β i j M w =
      (contentETripleEquiv D Sc cutoff N β i j i _ rfl M w).symm.conjAlgEquiv k
        (contentBlockPathJii D Sc cutoff N β i j M w) :=
  transport_three
    (contentETripleEquiv D Sc cutoff N β i j i _ rfl M w)
    (contentETripleEquiv D Sc cutoff N β j i i _ (content_triple_jii β i j) M w)
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N rfl (content_triple_jii β i j)
        (contentTripleLeft_parity D Sc i j i)) M w)
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N (content_triple_jii β i j) (content_triple_jii β i j)
        (contentTripleRight_parity D Sc j i i)) M w)
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N (content_triple_jii β i j) rfl
        (contentTripleLeft_parity D Sc j i i)) M w)

theorem contentETripleMixedBraid_comparison (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    contentETripleMixedBraid D Sc cutoff N β i j M w =
      (contentETripleEquiv D Sc cutoff N β i j i _ rfl M w).symm.conjAlgEquiv k
        (contentMixedBraid D Sc cutoff N β i j M w) := by
  rw [contentETripleMixedBraid, contentETriplePathIij_comparison,
    contentETriplePathJii_comparison, ← map_sub]
  rfl

/-- All three positioned dots use the same canonical even comparison. -/
def contentETripleDot (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) (a : Fin 3) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M w) :=
  (contentETripleEquiv D Sc cutoff N β i j i _ rfl M w).symm.conjAlgEquiv k
    (if a = 0 then contentInductionEndLinear D Sc cutoff N (firstDot_parity D Sc i [j,i]) M w
     else if a = 1 then contentInductionEndLinear D Sc cutoff N (contentTripleDot_one_parity D Sc i j) M w
     else contentInductionEndLinear D Sc cutoff N (contentTripleDot_two_parity D Sc i j) M w)

def contentETripleDotSum (β : Multiset I) (i j : I) (r s : ℕ) (d : k)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M w) :=
  let A := contentETripleDot D Sc cutoff N β i j M w 0
  let B := contentETripleDot D Sc cutoff N β i j M w 1
  let C := contentETripleDot D Sc cutoff N β i j M w 2
  ∑ l ∈ Finset.range r, (SKM.zsign k (D.parity i*(D.parity j+l))*d) • (C^(r-1-l)*B^s*A^l)

theorem contentETripleDotSum_comparison (β : Multiset I) (i j : I) (r s : ℕ) (d : k)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    (contentETripleEquiv D Sc cutoff N β i j i _ rfl M w).symm.conjAlgEquiv k
      (contentMixedDotSum D Sc cutoff N β i j r s d M w) =
      contentETripleDotSum D Sc cutoff N β i j r s d M w := by
  classical
  simp only [contentMixedDotSum, contentETripleDotSum, contentETripleDot,
    show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte, map_sum, map_smul, map_mul, map_pow]

/-- Ordered three-dot correction with the original Sc, including the leading t term. -/
def contentETriplePolynomial (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D (parameterTwist D Sc) cutoff N β i j i _ rfl M w) :=
  contentETripleDotSum D (parameterTwist D Sc) cutoff N β i j (D.dn i j) 0 (Sc.t i j : k) M w +
    ∑ r ∈ Finset.Ioo 0 (D.dn i j), ∑ s ∈ Finset.Ioo 0 (D.dn j i),
      contentETripleDotSum D (parameterTwist D Sc) cutoff N β i j r s (Sc.s i j r s) M w

theorem contentETriplePolynomial_comparison (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    (contentETripleEquiv D (parameterTwist D Sc) cutoff N β i j i _ rfl M w).symm.conjAlgEquiv k
      (contentMixedBraidPolynomial D Sc cutoff N β i j M w) =
      contentETriplePolynomial D Sc cutoff N β i j M w := by
  classical
  simp only [contentMixedBraidPolynomial, contentETriplePolynomial,
    map_add, map_sum, contentETripleDotSum_comparison]

/-- The transported normalized paths on three actual E functors satisfy the corrected mixed braid. -/
theorem contentETriple_mixedBraid (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    contentETripleMixedBraid D (parameterTwist D Sc) cutoff N β i j M w =
      contentETriplePolynomial D Sc cutoff N β i j M w := by
  rw [contentETripleMixedBraid_comparison,
    contentMixedBraid_polynomial_linear D Sc cutoff N β hij M w,
    contentETriplePolynomial_comparison]

/-- On transported generators the full outside-colour twist remains visible. -/
theorem contentETriple_mixedBraid_tensor (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl).obj v ⟶ w) (m : M.obj v) :
    (contentETripleEquiv D Sc cutoff N β i j i _ rfl M w)
      (contentETripleMixedBraid D Sc cutoff N β i j M w
        ((contentETripleEquiv D Sc cutoff N β i j i _ rfl M w).symm
          (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl)
            M.toFunctor v h m))) =
      sign k (D.parity i * D.parity j) •
        contentTensorEval D Sc cutoff N M w v (twist k (D.parity i) h) m
          (contentBraidCorrection D Sc i j) := by
  rw [contentETripleMixedBraid_comparison]
  change (contentETripleEquiv D Sc cutoff N β i j i _ rfl M w)
    ((contentETripleEquiv D Sc cutoff N β i j i _ rfl M w).symm
      (contentMixedBraid D Sc cutoff N β i j M w
        ((contentETripleEquiv D Sc cutoff N β i j i _ rfl M w)
          ((contentETripleEquiv D Sc cutoff N β i j i _ rfl M w).symm _)))) = _
  simp only [LinearEquiv.apply_symm_apply]
  exact contentMixedBraid_tensor D Sc cutoff N β hij M w v h m

end OddMath.QuiverHecke.ELVOld
