/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleAction
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform

/-! # Exact-content induction transformations

The dot and normalized crossing of `DeformedActionAssembly.md` §5 act on
balanced induction between exact-content module categories. A common target
content avoids casts between the two orders of a pair of colours. Induction
reverses the direction of the affine transformation. Equal-colour crossings
have the negative normalization; distinct-colour crossings retain the raw
normalization. No presentation relations or comparison with composites of
single-colour induction functors are asserted here.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
namespace BalancedInduction
variable {k : Type u} [CommRing k]
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
variable {J K : C ⥤ B} [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]

/-- The two homogeneous components of induction's mate on a balanced generator. -/
theorem transform_app_tensor {p : ZMod 2} {α : ∀ v, J.obj v ⟶ K.obj v}
    (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k))
    (w : B) (v : C) (h : K.obj v ⟶ w) (m : M.obj v) :
    ((transform hα).app p M).app p w (tensor K M.toFunctor v h m) =
      tensor J M.toFunctor v (α v ≫ twist k p h) m := by
  simp only [transform, IsSupernatural.toSuperNatTrans, ↓reduceIte]
  change (transformComponent hα M).app p w (tensor K M.toFunctor v h m) = _
  rw [transformComponent_apply]
  simp only [↓reduceIte, transformLinear_tensor]
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Append with an explicit common target content. -/
def contentAppendTo (β : Multiset I) (σ : List I) (γ : Multiset I)
    (hσ : β + (σ : Multiset I) = γ) :
    ContentCategory D Sc cutoff N β ⥤ ContentCategory D Sc cutoff N γ where
  obj v := ⟨(truncatedAppend D Sc cutoff N σ).obj v.obj, by
    change ((v.obj.word ++ σ : List I) : Multiset I) = γ
    rw [← Multiset.coe_add, v.content, hσ]⟩
  map f := (truncatedAppend D Sc cutoff N σ).map f
  map_id v := (truncatedAppend D Sc cutoff N σ).map_id v.obj
  map_comp f g := (truncatedAppend D Sc cutoff N σ).map_comp f g

instance contentAppendTo_additive (β : Multiset I) (σ : List I) (γ : Multiset I)
    (hσ : β + (σ : Multiset I) = γ) :
    (contentAppendTo D Sc cutoff N β σ γ hσ).Additive where
  map_add := (truncatedAppend D Sc cutoff N σ).map_add
instance contentAppendTo_linear (β : Multiset I) (σ : List I) (γ : Multiset I)
    (hσ : β + (σ : Multiset I) = γ) :
    (contentAppendTo D Sc cutoff N β σ γ hσ).Linear k where
  map_smul f r := (truncatedAppend D Sc cutoff N σ).map_smul r f
instance contentAppendTo_super (β : Multiset I) (σ : List I) (γ : Multiset I)
    (hσ : β + (σ : Multiset I) = γ) :
    IsSuperfunctor k (contentAppendTo D Sc cutoff N β σ γ hσ) where
  map_mem := Supercategory.map_mem (truncatedAppend D Sc cutoff N σ)

abbrev contentInductionTo (β : Multiset I) (σ : List I) (γ : Multiset I)
    (hσ : β + (σ : Multiset I) = γ) :
    ContentModules D Sc cutoff N β ⥤ ContentModules D Sc cutoff N γ :=
  BalancedInduction.induction (contentAppendTo D Sc cutoff N β σ γ hσ)

/-- The exact-content component is the same quotient morphism. -/
def contentAppendToComponent {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ))
    (v : ContentCategory D Sc cutoff N β) :
    (contentAppendTo D Sc cutoff N β σ γ hσ).obj v ⟶
      (contentAppendTo D Sc cutoff N β τ γ hτ).obj v :=
  truncatedAppendComponent D Sc cutoff N a v.obj

@[simp] theorem contentAppendToComponent_neg {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ))
    (v : ContentCategory D Sc cutoff N β) :
    contentAppendToComponent D Sc cutoff N hσ hτ (-a) v =
      -contentAppendToComponent D Sc cutoff N hσ hτ a v := by
  simp [contentAppendToComponent, truncatedAppendComponent, appendComponent,
    MonoidalSupercategory.whiskerLeft_neg k, TensorProduct.tmul_neg]

/-- Restrict the appended affine transformation to exact-content objects. -/
theorem contentAppendTo_supernatural {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (ha : a ∈ parity (R := k) _ _ p) :
    IsSupernatural k p (F := contentAppendTo D Sc cutoff N β σ γ hσ)
      (G := contentAppendTo D Sc cutoff N β τ γ hτ)
      (contentAppendToComponent D Sc cutoff N hσ hτ a) where
  mem v := (truncatedAppendComponent_supernatural D Sc cutoff N ha).mem v.obj
  naturality hf := (truncatedAppendComponent_supernatural D Sc cutoff N ha).naturality hf

/-- Balanced induction reverses the affine map, keeping exact endpoints. -/
def contentInductionTransform {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (ha : a ∈ parity (R := k) _ _ p) :
    SuperNatTrans k (contentInductionTo D Sc cutoff N β τ γ hτ)
      (contentInductionTo D Sc cutoff N β σ γ hσ) :=
  BalancedInduction.transform (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha)

@[simp] theorem contentInductionTransform_tensor {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (ha : a ∈ parity (R := k) _ _ p) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β τ γ hτ).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionTransform D Sc cutoff N hσ hτ ha).app p M).app p w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β τ γ hτ) M.toFunctor v h m) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ γ hσ) M.toFunctor v
      (contentAppendToComponent D Sc cutoff N hσ hτ a v ≫ twist k p h) m :=
  BalancedInduction.transform_app_tensor
    (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M w v h m

/-- The dot acts on the raising functor `E`. -/
def contentInductionDot (β : Multiset I) (i : I) :
    SuperNatTrans k (contentE D Sc cutoff N β i) (contentE D Sc cutoff N β i) :=
  contentInductionTransform D Sc cutoff N rfl rfl (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

/-- The two colour orders have the same exact target content. -/
theorem content_pair_swap (β : Multiset I) (i j : I) :
    β + ([j, i] : Multiset I) = β + ([i, j] : Multiset I) := by
  congr 1
  exact Multiset.coe_eq_coe.mpr (List.Perm.swap i j [])

/-- Raw crossing with a common exact target, contravariant in append. -/
def contentInductionCrossRaw (β : Multiset I) (i j : I) :
    SuperNatTrans k
      (contentInductionTo D Sc cutoff N β [j, i] (β + ([i, j] : Multiset I))
        (content_pair_swap β i j))
      (contentInductionTo D Sc cutoff N β [i, j] (β + ([i, j] : Multiset I)) rfl) :=
  contentInductionTransform D Sc cutoff N rfl (content_pair_swap β i j) (crossTwo_mem D Sc i j)

/-- The normalized affine representative used by the induction crossing. -/
def contentCrossAffine (i j : I) :
    (pres D Sc).obj (ob D [i, j]) ⟶ (pres D Sc).obj (ob D [j, i]) := by
  classical
  exact if i = j then -crossTwo D Sc i j else crossTwo D Sc i j

theorem contentCrossAffine_mem (i j : I) :
    contentCrossAffine D Sc i j ∈ parity (R := k) _ _ (D.parity i * D.parity j) := by
  classical
  unfold contentCrossAffine
  split_ifs
  · exact Submodule.neg_mem _ (crossTwo_mem D Sc i j)
  · exact crossTwo_mem D Sc i j

@[simp] theorem contentCrossAffine_equal (i : I) :
    contentCrossAffine D Sc i i = -crossTwo D Sc i i := by
  simp [contentCrossAffine]

@[simp] theorem contentCrossAffine_distinct (i j : I) (h : i ≠ j) :
    contentCrossAffine D Sc i j = crossTwo D Sc i j := by
  simp [contentCrossAffine, h]

/-- Source normalization: minus the raw affine crossing for equal colours. -/
def contentInductionCross (β : Multiset I) (i j : I) :
    SuperNatTrans k
      (contentInductionTo D Sc cutoff N β [j, i] (β + ([i, j] : Multiset I))
        (content_pair_swap β i j))
      (contentInductionTo D Sc cutoff N β [i, j] (β + ([i, j] : Multiset I)) rfl) :=
  contentInductionTransform D Sc cutoff N rfl (content_pair_swap β i j)
    (contentCrossAffine_mem D Sc i j)

@[simp] theorem contentInductionDot_tensor (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppend D Sc cutoff N β [i]).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionDot D Sc cutoff N β i).app (D.parity i) M).app (D.parity i) w
      (BalancedInduction.tensor (contentAppend D Sc cutoff N β [i]) M.toFunctor v h m) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i] _ rfl) M.toFunctor v
      (contentAppendToComponent D Sc cutoff N rfl rfl (dotE D Sc [i] 0) v ≫
        twist k (D.parity i) h) m :=
  contentInductionTransform_tensor D Sc cutoff N rfl rfl _ M w v h m

@[simp] theorem contentInductionCross_tensor (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i, j] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j)).obj v ⟶ w)
    (m : M.obj v) :
    ((contentInductionCross D Sc cutoff N β i j).app (D.parity i * D.parity j) M).app
      (D.parity i * D.parity j) w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [j, i] _
        (content_pair_swap β i j)) M.toFunctor v h m) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i, j] _ rfl) M.toFunctor v
      (contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j)
        (contentCrossAffine D Sc i j) v ≫ twist k (D.parity i * D.parity j) h) m :=
  contentInductionTransform_tensor D Sc cutoff N rfl (content_pair_swap β i j) _ M w v h m

/-- In equal colour the induced action is minus the raw action on every generator. -/
theorem contentInductionCross_equal_tensor (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i, i] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β [i, i] _ (content_pair_swap β i i)).obj v ⟶ w)
    (m : M.obj v) :
    ((contentInductionCross D Sc cutoff N β i i).app (D.parity i * D.parity i) M).app
      (D.parity i * D.parity i) w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i, i] _
        (content_pair_swap β i i)) M.toFunctor v h m) =
    -BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i, i] _ rfl) M.toFunctor v
      (contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i i)
        (crossTwo D Sc i i) v ≫ twist k (D.parity i * D.parity i) h) m := by
  rw [contentInductionCross_tensor, contentCrossAffine_equal, contentAppendToComponent_neg,
    Preadditive.neg_comp]
  simp only [BalancedInduction.tensor, TensorProduct.neg_tmul, map_neg]

/-- In distinct colours the affine crossing has no extra normalization sign. -/
theorem contentInductionCross_distinct_tensor (β : Multiset I) (i j : I) (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i, j] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j)).obj v ⟶ w)
    (m : M.obj v) :
    ((contentInductionCross D Sc cutoff N β i j).app (D.parity i * D.parity j) M).app
      (D.parity i * D.parity j) w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [j, i] _
        (content_pair_swap β i j)) M.toFunctor v h m) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i, j] _ rfl) M.toFunctor v
      (contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j)
        (crossTwo D Sc i j) v ≫ twist k (D.parity i * D.parity j) h) m := by
  rw [contentInductionCross_tensor, contentCrossAffine_distinct D Sc i j hij]

end OddMath.QuiverHecke.ELVOld
