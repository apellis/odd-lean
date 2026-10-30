/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCompositeComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentOperatorQuadratic

/-! # Single-letter content induction relations

Advances `DeformedActionAssembly.md` §5 by transporting the checked normalized
source crossing and positioned dots through the canonical even comparison.
`contentEPair_quadratic` is the original-Sc ordered polynomial relation on
successive single-letter induction, for every module. The second target content
is explicitly recast, not silently identified. `contentEPairCrossTransform`
is supernatural against odd module maps and `contentEPairCross_total` identifies
its evaluated map. No triple coherence, mixed braid, weight assembly or
nondegeneracy is asserted in this module.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Evaluation of a module isomorphism on the entire superspace. -/
def moduleIsoLinearEquiv {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M L : Superfunctor k C (SVec k)} (e : M ≅ L) (w : C) : M.obj w ≃ₗ[k] L.obj w where
  toLinearMap := e.hom.total w
  invFun := e.inv.total w
  left_inv x := by
    have h := congrArg (fun f : M ⟶ M => f.total w) e.hom_inv_id
    rw [Superfunctor.comp_total] at h
    simp only [SuperNatTrans.total, Superfunctor.id_app_zero,
      Superfunctor.id_app_one, add_zero] at h
    exact congrArg (fun f : M.obj w →ₗ[k] M.obj w => f x) h
  right_inv x := by
    have h := congrArg (fun f : L ⟶ L => f.total w) e.inv_hom_id
    rw [Superfunctor.comp_total] at h
    simp only [SuperNatTrans.total, Superfunctor.id_app_zero,
      Superfunctor.id_app_one, add_zero] at h
    exact congrArg (fun f : L.obj w →ₗ[k] L.obj w => f x) h

private theorem moduleIsoLinearEquiv_transport
    {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {A B E F : Superfunctor k C (SVec k)} (e : A ≅ B) (f : E ≅ F)
    (a : B ⟶ F) (w : C) (b : B.obj w →ₗ[k] F.obj w) (h : a.total w = b) :
    ((e.hom ≫ a) ≫ f.inv).total w =
      (moduleIsoLinearEquiv f w).symm.toLinearMap.comp
        (b.comp (moduleIsoLinearEquiv e w).toLinearMap) := by
  rw [Superfunctor.comp_total, Superfunctor.comp_total, h]
  rfl

/-- The second single-letter induction has its target content explicitly transported. -/
abbrev contentEPairTo (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) :=
  contentE D Sc cutoff N β i ⋙
    contentInductionTo D Sc cutoff N (β + ([i] : Multiset I)) [j] γ
      (by rw [add_assoc]; exact h)

def contentEPairToComparison (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) :
    contentEPairTo D Sc cutoff N β i j γ h ≅ contentInductionTo D Sc cutoff N β [i,j] γ h :=
  contentInductionComp D Sc cutoff N β [i] [j] γ _ h

abbrev ContentEPairSpace (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) :=
  BalancedInduction.Obj
    (contentAppendTo D Sc cutoff N (β + ([i] : Multiset I)) [j] γ
      (by rw [add_assoc]; exact h))
    (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M).toFunctor w

def contentEPairEquiv (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) :
    ContentEPairSpace D Sc cutoff N β i j γ h M w ≃ₗ[k]
      BalancedInduction.Obj (contentAppendTo D Sc cutoff N β [i,j] γ h) M.toFunctor w :=
  moduleIsoLinearEquiv ((contentEPairToComparison D Sc cutoff N β i j γ h).app M) w

/-- Transport of a homogeneous transformation through even natural comparisons. -/
theorem evenComparison_supernatural
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G F' G' : C ⥤ B}
    [F.Additive] [F.Linear k] [G.Additive] [G.Linear k]
    [F'.Additive] [F'.Linear k] [G'.Additive] [G'.Linear k]
    (e : F' ≅ F) (f : G' ≅ G)
    (he : ∀ M, EvenComparisonAt (k := k) e M)
    (hf : ∀ M, EvenComparisonAt (k := k) f M)
    {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M} (hx : IsSupernatural k p x) :
    IsSupernatural k p (fun M => (e.hom.app M ≫ x M) ≫ f.inv.app M) := by
  simpa only [zero_add, add_zero] using
    ((isSupernatural_of_natTrans e.hom (fun M => (he M).1)).comp hx).comp
      (isSupernatural_of_natTrans f.inv (fun M => (hf M).2))

private theorem evenComparison_app
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

/-- The normalized pair crossing is genuinely supernatural on all modules. -/
def contentEPairCrossTransform (β : Multiset I) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ) :
    SuperNatTrans k (contentEPairTo D Sc cutoff N β j i γ hji)
      (contentEPairTo D Sc cutoff N β i j γ hij) :=
  (evenComparison_supernatural
    (contentEPairToComparison D Sc cutoff N β j i γ hji)
    (contentEPairToComparison D Sc cutoff N β i j γ hij)
    (contentInductionComp_mem D Sc cutoff N β [j] [i] γ _ hji)
    (contentInductionComp_mem D Sc cutoff N β [i] [j] γ _ hij)
    ((contentInductionTransform D Sc cutoff N hij hji
      (contentCrossAffine_mem D Sc i j)).isSupernatural (D.parity i * D.parity j))).toSuperNatTrans

private theorem comparison_cross_comp
    {A B C E : Type*} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    [AddCommGroup E] [Module k E]
    (e : A ≃ₗ[k] B) (f : C ≃ₗ[k] E) (a : E →ₗ[k] B) (b : B →ₗ[k] E) :
    (e.symm.toLinearMap.comp (a.comp f.toLinearMap)).comp
      (f.symm.toLinearMap.comp (b.comp e.toLinearMap)) =
      e.symm.conjAlgEquiv k (a.comp b) := by
  apply LinearMap.ext
  intro x
  change e.symm (a (f (f.symm (b (e x))))) = e.symm (a (b (e x)))
  rw [f.apply_symm_apply]

/-- Canonical transport of the normalized source crossing; no scalar choices. -/
def contentEPairCross (β : Multiset I) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ) :
    ContentEPairSpace D Sc cutoff N β j i γ hji M w →ₗ[k]
      ContentEPairSpace D Sc cutoff N β i j γ hij M w :=
  (contentEPairEquiv D Sc cutoff N β i j γ hij M w).symm.toLinearMap.comp
    ((BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j)) M w).comp
      (contentEPairEquiv D Sc cutoff N β j i γ hji M w).toLinearMap)

theorem contentEPairCross_component (β : Multiset I) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) :
    (contentEPairCrossTransform D Sc cutoff N β i j γ hij hji).app
      (D.parity i * D.parity j) M =
    ((contentEPairToComparison D Sc cutoff N β j i γ hji).hom.app M ≫
      (contentInductionTransform D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j)).app
        (D.parity i * D.parity j) M) ≫
      (contentEPairToComparison D Sc cutoff N β i j γ hij).inv.app M :=
  evenComparison_app
    (contentEPairToComparison D Sc cutoff N β j i γ hji)
    (contentEPairToComparison D Sc cutoff N β i j γ hij)
    (contentInductionComp_mem D Sc cutoff N β [j] [i] γ _ hji)
    (contentInductionComp_mem D Sc cutoff N β [i] [j] γ _ hij)
    ((contentInductionTransform D Sc cutoff N hij hji
      (contentCrossAffine_mem D Sc i j)).isSupernatural (D.parity i * D.parity j)) M

private theorem homogeneous_total
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M}
    (hx : IsSupernatural k p x) (M : C) : hx.toSuperNatTrans.total M = x M := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

private theorem contentCross_block_total (β : Multiset I) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ) :
    ((contentInductionTransform D Sc cutoff N hij hji
      (contentCrossAffine_mem D Sc i j)).app (D.parity i * D.parity j) M).total w =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j)) M w := by
  have h := congrFun (IsSupernatural.toSuperNatTrans_app
    (BalancedInduction.transformComponent_supernatural
      (contentAppendTo_supernatural D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j)))) M
  exact (congrArg (fun a => a.total w) h).trans
    (homogeneous_total
      (BalancedInduction.transformLinear_supernatural
        (contentAppendTo_supernatural D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j)) M) w)

/-- The linear crossing evaluates the prescribed supernatural crossing component. -/
theorem contentEPairCross_total (β : Multiset I) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ) :
    ((contentEPairCrossTransform D Sc cutoff N β i j γ hij hji).app
      (D.parity i * D.parity j) M).total w = contentEPairCross D Sc cutoff N β i j γ hij hji M w := by
  rw [contentEPairCross_component]
  exact moduleIsoLinearEquiv_transport
    ((contentEPairToComparison D Sc cutoff N β j i γ hji).app M)
    ((contentEPairToComparison D Sc cutoff N β i j γ hij).app M)
    _ w _ (contentCross_block_total D Sc cutoff N β i j γ hij hji M w)

/-- Each positioned dot is transported by the same canonical even comparison. -/
def contentEPairDot (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I))) (a : Fin 2) :
    Module.End k (ContentEPairSpace D Sc cutoff N β i j _ rfl M w) :=
  (contentEPairEquiv D Sc cutoff N β i j _ rfl M w).symm.conjAlgEquiv k
    (if a = 0 then contentInductionEndLinear D Sc cutoff N (firstDot_parity D Sc i [j]) M w
      else contentInductionEndLinear D Sc cutoff N (contentPairDot_one_parity D Sc i j) M w)

/-- The polynomial retains the prescribed ordered dot powers and the specified Sc. -/
def contentEPairPolynomial (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I))) :
    Module.End k (ContentEPairSpace D (parameterTwist D Sc) cutoff N β i j _ rfl M w) :=
  let A := contentEPairDot D (parameterTwist D Sc) cutoff N β i j M w 0
  let B := contentEPairDot D (parameterTwist D Sc) cutoff N β i j M w 1
  if D.d i j = 0 then (Sc.t i j : k) • (1 : Module.End k _) else
    ∑ r ∈ Finset.Ioo 0 (D.dn i j), ∑ s ∈ Finset.Ioo 0 (D.dn j i),
      Sc.s i j r s • (B ^ s * A ^ r) +
    ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i)

theorem contentEPairPolynomial_comparison (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I))) :
    (contentEPairEquiv D (parameterTwist D Sc) cutoff N β i j _ rfl M w).symm.conjAlgEquiv k
        (contentInductionPairPolynomial D Sc cutoff N β i j M w) =
      contentEPairPolynomial D Sc cutoff N β i j M w := by
  classical
  simp only [contentInductionPairPolynomial, contentEPairPolynomial, contentEPairDot,
    show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
  split_ifs <;> simp only [map_smul, map_one, map_add, map_sum, map_mul, map_pow]

/-- The actual pair composite obeys the original-Sc quadratic, on every module. -/
theorem contentEPair_quadratic (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I))) :
    (contentEPairCross D (parameterTwist D Sc) cutoff N β i j _ rfl
        (content_pair_swap β i j) M w).comp
      (contentEPairCross D (parameterTwist D Sc) cutoff N β j i _
        (content_pair_swap β i j) rfl M w) =
      contentEPairPolynomial D Sc cutoff N β i j M w := by
  unfold contentEPairCross
  rw [comparison_cross_comp, contentInduction_quadratic_linear D Sc cutoff N β hij M w]
  exact contentEPairPolynomial_comparison D Sc cutoff N β i j M w

end OddMath.QuiverHecke.ELVOld
