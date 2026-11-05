import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContent
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppendTensor
import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVContentComparisonCoherence
import OddMath.QuiverHecke.CyclotomicAction.ELVOldModuleAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionCrossTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform
import Mathlib.CategoryTheory.EqToHom
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations

/-! # The chosen content dot on scheduled regular-power words

SwappedVacuumCoordinates §§4–6: transport the independently chosen dot
through the established word descent and selected content append comparison.
The full old-arrow parity twist and all exterior coefficients are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordContentDot
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem total_of_mem {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (w : C) : f.total w = f.app p w := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]

private theorem transform_total {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ w, J.obj w ⟶ J.obj w} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (w : B) :
    (BalancedInduction.transformComponent hα M).total w =
      BalancedInduction.transformLinear hα M w := by
  rw [total_of_mem (BalancedInduction.transformComponent_mem hα M),
    BalancedInduction.transformComponent_app, ite_eq_left rfl]

private theorem square_of_total {C : Type*} [Category* C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M N : Superfunctor k C (SVec k)} (e : M ⟶ N) (x : M ⟶ M) (y : N ⟶ N)
    (h : ∀ w, e.total w ∘ₗ x.total w = y.total w ∘ₗ e.total w) : x ≫ e = e ≫ y := by
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  exact h w

omit [Fintype I] in
/-- The previously checked whole linear-map dot square, as a module-map
identity needed by weighted descent. -/
theorem append_dot (ν : List I) (i : I) :
    BalancedInduction.transformComponent (oldAppendDot_supernatural D Sc cutoff i)
      (powerWordModule D Sc cutoff L ν) ≫ (powerWordAppendIso D Sc cutoff L ν i).hom =
    (powerWordAppendIso D Sc cutoff L ν i).hom ≫ PowerWordAppend.nativeDot D Sc cutoff L ν i := by
  apply square_of_total
  intro w
  rw [transform_total]
  have hn : PowerWordAppend.nativeDot D Sc cutoff L ν i ∈ parity (R := k) _ _ (D.parity i) :=
    PowerWordMorphisms.fromArrow_mem D Sc cutoff L (ν ++ [i]) (ν ++ [i]) _
      ((oldAppendDot_supernatural D Sc cutoff i).mem (OldCategory.mk ν))
  rw [total_of_mem hn]
  exact PowerWordAppend.appendLinear_dot D Sc cutoff L ν i w

private theorem comparison_even {C B E : Type u}
    [Category.{u} C] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (P : C ⥤ E)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [P.Additive] [P.Linear k] [IsSuperfunctor k P] (e : J ⋙ K = P)
    (R : Superfunctor k C (SVec k)) :
    ((inductionCompOfEq J K P e).app R).hom ∈ parity (R := k) _ _ 0 := by
  subst P
  simpa only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl, Iso.app_hom] using
    BalancedInduction.inductionComp_hom_mem J K R

private theorem iso_trans_even {C : Type*} [Category* C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A B E : C} (e : A ≅ B) (f : B ≅ E)
    (he : e.hom ∈ parity (R := k) _ _ 0) (hf : f.hom ∈ parity (R := k) _ _ 0) :
    (e ≪≫ f).hom ∈ parity (R := k) _ _ 0 := by
  simpa only [Iso.trans_hom, zero_add] using comp_mem he hf

omit [Fintype I] in
theorem wordAppend_even (ν : List I) (i : I) :
    (powerWordAppendIso D Sc cutoff L ν i).hom ∈ parity (R := k) _ _ 0 := by
  rw [PowerWordPair.selectedAppend_eq]
  exact comparison_even _ _ _ _ _

/-- The selected weighted comparison is even before transporting operators. -/
theorem weightedAppend_even (ν : List I) (i : I) :
    (PowerWordContent.weightedAppendIso D Sc cutoff L ν i).hom ∈ parity (R := k) _ _ 0 := by
  unfold PowerWordContent.weightedAppendIso
  apply iso_trans_even
  · exact appendWeightedModuleIso_inv_mem D Sc cutoff _ i _
  · apply weightedModuleHom_mem
    apply iso_trans_even
    · exact IsSuperfunctor.map_mem (F := BalancedInduction.induction (append D Sc cutoff i))
        (weightedRestrictionModuleIso_hom_mem D Sc cutoff _ _ _)
    · exact wordAppend_even D Sc cutoff L ν i

/-- The content extension counit is even on the scheduled word model. -/
theorem contentExtension_even (ν : List I) :
    (PowerWordContent.contentExtensionIso D Sc cutoff L ν).hom ∈ parity (R := k) _ _ 0 := by
  unfold PowerWordContent.contentExtensionIso contentSupportedCounitIso
  exact moduleIsoOfEvenNatIso_hom_mem _ _ _ _ _

omit [Fintype I] in
private theorem weightedHom_total (N : ℕ)
    (M P : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (hP : KillsWeightedCoefficients D Sc cutoff N P)
    (f : M ⟶ P) (w : TruncatedCategory D Sc cutoff N) :
    (weightedModuleHom D Sc cutoff N M P hM hP f).total w = f.total (OldCategory.mk w.word) := rfl

omit [Fintype I] in
private def weightedOldDot (N : ℕ) (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    End (weightedInducedModule D Sc cutoff N i (weightedRestriction D Sc cutoff N M)
      (weightedRestriction_kills D Sc cutoff N M)) :=
  let R := weightedRestriction D Sc cutoff N M
  let F := BalancedInduction.induced (append D Sc cutoff i) R
  let hF := induced_killsWeightedCoefficients D Sc cutoff N i R (weightedRestriction_kills D Sc cutoff N M)
  weightedModuleHom D Sc cutoff N F F hF hF
    (BalancedInduction.transformComponent (oldAppendDot_supernatural D Sc cutoff i) R)

omit [Fintype I] in
private def truncatedDot (N : ℕ) (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    End (BalancedInduction.induced (truncatedAppend D Sc cutoff N [i]) M) :=
  BalancedInduction.transformComponent
    (truncatedAppendComponent_supernatural D Sc cutoff N (by
      simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M

omit [Fintype I] in
private theorem weightedDot_square (N : ℕ) (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    weightedOldDot D Sc cutoff N i M ≫ (appendWeightedModuleIso D Sc cutoff N i M).hom =
      (appendWeightedModuleIso D Sc cutoff N i M).hom ≫ truncatedDot D Sc cutoff N i M := by
  unfold weightedOldDot truncatedDot
  apply square_of_total
  intro w
  rw [weightedHom_total, transform_total, transform_total]
  exact appendWeightedModuleIso_hom_dot D Sc cutoff N i M (OldCategory.mk w.word)

private theorem natural_even {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p : ZMod 2} {α : ∀ X, F.obj X ⟶ G.obj X} (hα : IsSupernatural k p α)
    {X Y : C} (f : X ⟶ Y) (hf : f ∈ parity (R := k) _ _ 0) :
    α X ≫ G.map f = F.map f ≫ α Y := by
  simpa only [mul_zero, Supercategory.sign_zero, one_smul] using (hα.naturality hf).symm

private theorem compose_squares {C : Type*} [Category* C] {A B E : C}
    (e : A ≅ B) (f : B ≅ E) (x : A ⟶ A) (y : B ⟶ B) (z : E ⟶ E)
    (he : x ≫ e.hom = e.hom ≫ y) (hf : y ≫ f.hom = f.hom ≫ z) :
    x ≫ (e ≪≫ f).hom = (e ≪≫ f).hom ≫ z := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, he, Category.assoc, hf]

private def oldWordComparison (ν : List I) (i : I) :
    BalancedInduction.induced (append D Sc cutoff i)
      (weightedRestriction D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν)) ≅ powerWordModule D Sc cutoff L (ν ++ [i]) :=
  (BalancedInduction.induction (append D Sc cutoff i)).mapIso
    (weightedRestrictionModuleIso D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      (powerWordModule D Sc cutoff L ν) (PowerWordContent.word_killsWeighted D Sc cutoff L ν)) ≪≫
    powerWordAppendIso D Sc cutoff L ν i

private theorem oldWord_dot (ν : List I) (i : I) :
    BalancedInduction.transformComponent (oldAppendDot_supernatural D Sc cutoff i)
      (weightedRestriction D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν)) ≫ (oldWordComparison D Sc cutoff L ν i).hom =
      (oldWordComparison D Sc cutoff L ν i).hom ≫ PowerWordAppend.nativeDot D Sc cutoff L ν i := by
  unfold oldWordComparison
  apply compose_squares
  · exact natural_even
      (BalancedInduction.transformComponent_supernatural (oldAppendDot_supernatural D Sc cutoff i)) _
      (weightedRestrictionModuleIso_hom_mem D Sc cutoff _ _ _)
  · exact append_dot D Sc cutoff L ν i

/-- The literal descended old-Hom dot on the next word module. -/
def weightedWordDot (ν : List I) (i : I) : End (PowerWordContent.weightedWord D Sc cutoff L (ν ++ [i])) :=
  weightedModuleHom D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    (powerWordModule D Sc cutoff L (ν ++ [i])) (powerWordModule D Sc cutoff L (ν ++ [i]))
    (PowerWordContent.word_killsWeighted D Sc cutoff L (ν ++ [i]))
    (PowerWordContent.word_killsWeighted D Sc cutoff L (ν ++ [i]))
    (PowerWordAppend.nativeDot D Sc cutoff L ν i)

omit [Fintype I] in
private theorem descend_square (N : ℕ)
    (M P : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (hP : KillsWeightedCoefficients D Sc cutoff N P)
    (e : M ⟶ P) (x : M ⟶ M) (y : P ⟶ P) (h : x ≫ e = e ≫ y) :
    weightedModuleHom D Sc cutoff N M M hM hM x ≫ weightedModuleHom D Sc cutoff N M P hM hP e =
      weightedModuleHom D Sc cutoff N M P hM hP e ≫ weightedModuleHom D Sc cutoff N P P hP hP y := by
  have he := congrArg (fun f => weightedModuleHom D Sc cutoff N M P hM hP f) h
  rw [weightedModuleHom_comp, weightedModuleHom_comp] at he
  exact he

private theorem conjugate_square {C : Type*} [Category* C] {A B E : C}
    (e : A ≅ B) (f : A ≅ E) (x : A ⟶ A) (y : B ⟶ B) (z : E ⟶ E)
    (he : x ≫ e.hom = e.hom ≫ y) (hf : x ≫ f.hom = f.hom ≫ z) :
    y ≫ (e.symm ≪≫ f).hom = (e.symm ≪≫ f).hom ≫ z := by
  have hi : y ≫ e.inv = e.inv ≫ x := by
    calc
      _ = (e.inv ≫ (e.hom ≫ y)) ≫ e.inv := by simp only [Iso.inv_hom_id_assoc]
      _ = (e.inv ≫ (x ≫ e.hom)) ≫ e.inv := by rw [← he]
      _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  rw [hi, Category.assoc, hf, Category.assoc]

private def oldWordWeightedComparison (ν : List I) (i : I) :
    weightedInducedModule D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (weightedRestriction D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν))
      (weightedRestriction_kills D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν)) ≅
      PowerWordContent.weightedWord D Sc cutoff L (ν ++ [i]) :=
  let N := PowerWordContent.powerBound D cutoff L
  let M := PowerWordContent.weightedWord D Sc cutoff L ν
  let R := weightedRestriction D Sc cutoff N M
  let F := BalancedInduction.induced (append D Sc cutoff i) R
  let hF := induced_killsWeightedCoefficients D Sc cutoff N i R (weightedRestriction_kills D Sc cutoff N M)
  weightedModuleIso D Sc cutoff N F (powerWordModule D Sc cutoff L (ν ++ [i])) hF
    (PowerWordContent.word_killsWeighted D Sc cutoff L (ν ++ [i])) (oldWordComparison D Sc cutoff L ν i)

private theorem oldWordWeightedDot_square (ν : List I) (i : I) :
    weightedOldDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (PowerWordContent.weightedWord D Sc cutoff L ν) ≫ (oldWordWeightedComparison D Sc cutoff L ν i).hom =
    (oldWordWeightedComparison D Sc cutoff L ν i).hom ≫ weightedWordDot D Sc cutoff L ν i :=
  descend_square D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    _ _ _ _ (oldWordComparison D Sc cutoff L ν i).hom
    (BalancedInduction.transformComponent (oldAppendDot_supernatural D Sc cutoff i)
      (weightedRestriction D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        (PowerWordContent.weightedWord D Sc cutoff L ν)))
    (PowerWordAppend.nativeDot D Sc cutoff L ν i) (oldWord_dot D Sc cutoff L ν i)

/-- The independently chosen truncated induction dot intertwines with the
literal descended old-Hom word dot through the prescribed weighted comparison. -/
theorem weighted_append_dot (ν : List I) (i : I) :
    truncatedDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (PowerWordContent.weightedWord D Sc cutoff L ν) ≫
        (PowerWordContent.weightedAppendIso D Sc cutoff L ν i).hom =
    (PowerWordContent.weightedAppendIso D Sc cutoff L ν i).hom ≫ weightedWordDot D Sc cutoff L ν i :=
  conjugate_square
    (appendWeightedModuleIso D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (PowerWordContent.weightedWord D Sc cutoff L ν))
    (oldWordWeightedComparison D Sc cutoff L ν i)
    (weightedOldDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (PowerWordContent.weightedWord D Sc cutoff L ν))
    (truncatedDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (PowerWordContent.weightedWord D Sc cutoff L ν))
    (weightedWordDot D Sc cutoff L ν i)
    (weightedDot_square D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (PowerWordContent.weightedWord D Sc cutoff L ν))
    (oldWordWeightedDot_square D Sc cutoff L ν i)

private theorem restriction_total {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M P : Superfunctor k B (SVec k)} (f : M ⟶ P) (v : C) :
    ((BalancedInduction.restriction Q).map f).total v = f.total (Q.obj v) := rfl

omit [Fintype I] in
private def contentDot (N : ℕ) (β : Multiset I) (i : I) (γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β) :
    End (BalancedInduction.induced (contentAppendTo D Sc cutoff N β [i] γ hγ) M) :=
  BalancedInduction.transformComponent
    (contentAppendTo_supernatural D Sc cutoff N hγ hγ (by
      simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M

omit [Fintype I] in
private theorem contentRestrictionLinear_dot (N : ℕ) (β : Multiset I) (i : I) (γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (t : ContentCategory D Sc cutoff N γ) :
    contentAppendToRestrictionLinear D Sc cutoff N β [i] γ hγ M t ∘ₗ
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N hγ hγ (by
          simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M t =
    BalancedInduction.transformLinear
      (truncatedAppendComponent_supernatural D Sc cutoff N (by
        simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1))
      (BalancedInduction.induced (contentInclusion D Sc cutoff N β) M) t.obj ∘ₗ
        contentAppendToRestrictionLinear D Sc cutoff N β [i] γ hγ M t := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, BalancedInduction.transformLinear_tensor,
    contentAppendToRestrictionLinear_tensor]
  rfl

omit [Fintype I] in
private theorem contentRestriction_dot (N : ℕ) (β : Multiset I) (i : I) (γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β) :
    contentDot D Sc cutoff N β i γ hγ M ≫ (contentAppendToRestrictionIso D Sc cutoff N β [i] γ hγ M).hom =
      (contentAppendToRestrictionIso D Sc cutoff N β [i] γ hγ M).hom ≫
        (BalancedInduction.restriction (contentInclusion D Sc cutoff N γ)).map
          (truncatedDot D Sc cutoff N i (BalancedInduction.induced (contentInclusion D Sc cutoff N β) M)) := by
  unfold contentDot truncatedDot
  apply square_of_total
  intro t
  rw [restriction_total, transform_total, transform_total]
  exact contentRestrictionLinear_dot D Sc cutoff N β i γ hγ M t

private theorem map_square {C B : Type*} [Category* C] [Category* B]
    (F : C ⥤ B) {M P : C} (e : M ≅ P) (x : M ⟶ M) (y : P ⟶ P)
    (h : x ≫ e.hom = e.hom ≫ y) :
    F.map x ≫ (F.mapIso e).hom = (F.mapIso e).hom ≫ F.map y := by
  simp only [Functor.mapIso_hom]
  rw [← F.map_comp, h, F.map_comp]

private def extendedWordComparison (ν : List I) (i : I) :
    BalancedInduction.induced (truncatedAppend D Sc cutoff (PowerWordContent.powerBound D cutoff L) [i])
      (BalancedInduction.induced
        (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
        (PowerWordContent.contentWord D Sc cutoff L ν)) ≅
    PowerWordContent.weightedWord D Sc cutoff L (ν ++ [i]) :=
  (BalancedInduction.induction (truncatedAppend D Sc cutoff (PowerWordContent.powerBound D cutoff L) [i])).mapIso
    (PowerWordContent.contentExtensionIso D Sc cutoff L ν) ≪≫ PowerWordContent.weightedAppendIso D Sc cutoff L ν i

private theorem extendedWord_dot (ν : List I) (i : I) :
    truncatedDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
      (BalancedInduction.induced
        (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
        (PowerWordContent.contentWord D Sc cutoff L ν)) ≫ (extendedWordComparison D Sc cutoff L ν i).hom =
      (extendedWordComparison D Sc cutoff L ν i).hom ≫ weightedWordDot D Sc cutoff L ν i := by
  unfold extendedWordComparison
  apply compose_squares
  · exact natural_even
      (BalancedInduction.transformComponent_supernatural
        (truncatedAppendComponent_supernatural D Sc cutoff (PowerWordContent.powerBound D cutoff L) (by
          simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1))) _
      (contentExtension_even D Sc cutoff L ν)
  · exact weighted_append_dot D Sc cutoff L ν i

/-- The literal old-Hom word dot after weighted descent and exact-content restriction. -/
def contentWordDot (ν : List I) (i : I) : End (PowerWordContent.contentWord D Sc cutoff L (ν ++ [i])) :=
  (BalancedInduction.restriction
    (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) ((ν ++ [i] : List I) : Multiset I))).map
      (weightedWordDot D Sc cutoff L ν i)

/-- The independently chosen content induction dot with its exact output content. -/
def chosenContentDot (ν : List I) (i : I) :
    End (BalancedInduction.induced
      (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I) [i]
        ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i]))
      (PowerWordContent.contentWord D Sc cutoff L ν)) :=
  contentDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I) i
    ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i]) (PowerWordContent.contentWord D Sc cutoff L ν)

private theorem transform_component_eq {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ w, J.obj w ⟶ J.obj w} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) :
    BalancedInduction.transformComponent hα M = (BalancedInduction.transform hα).app p M :=
  (congrFun (IsSupernatural.toSuperNatTrans_app (BalancedInduction.transformComponent_supernatural hα)) M).symm

/-- This is the existing normalized content generator, not a new conjugate. -/
theorem chosenContentDot_eq (ν : List I) (i : I) : chosenContentDot D Sc cutoff L ν i =
    (contentInductionTransform D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      (Multiset.coe_add ν [i]) (Multiset.coe_add ν [i]) (by
        simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)).app (D.parity i)
      (PowerWordContent.contentWord D Sc cutoff L ν) := by
  unfold chosenContentDot contentDot contentInductionTransform
  exact transform_component_eq _ _ _

/-- The chosen content E dot is the full old-Hom dot under the prescribed
scheduled word comparison, on every coefficient vector. -/
theorem content_append_dot (ν : List I) (i : I) :
    chosenContentDot D Sc cutoff L ν i ≫ (PowerWordContent.contentAppendIso D Sc cutoff L ν i).hom =
      (PowerWordContent.contentAppendIso D Sc cutoff L ν i).hom ≫ contentWordDot D Sc cutoff L ν i :=
  compose_squares
    (contentAppendToRestrictionIso D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I) [i]
      ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i]) (PowerWordContent.contentWord D Sc cutoff L ν))
    ((BalancedInduction.restriction
      (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        ((ν ++ [i] : List I) : Multiset I))).mapIso (extendedWordComparison D Sc cutoff L ν i))
    (chosenContentDot D Sc cutoff L ν i)
    ((BalancedInduction.restriction
      (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        ((ν ++ [i] : List I) : Multiset I))).map
      (truncatedDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) i
        (BalancedInduction.induced
          (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I))
          (PowerWordContent.contentWord D Sc cutoff L ν))))
    (contentWordDot D Sc cutoff L ν i)
    (contentRestriction_dot D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν : Multiset I) i
      ((ν ++ [i] : List I) : Multiset I) (Multiset.coe_add ν [i]) (PowerWordContent.contentWord D Sc cutoff L ν))
    (map_square (BalancedInduction.restriction
      (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        ((ν ++ [i] : List I) : Multiset I))) (extendedWordComparison D Sc cutoff L ν i) _ _
      (extendedWord_dot D Sc cutoff L ν i))

end OddMath.QuiverHecke.ELVOld.PowerWordContentDot
