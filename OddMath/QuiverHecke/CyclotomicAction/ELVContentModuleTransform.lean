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

end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

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

/-- The concrete quotient component as a linear map in its affine input. -/
def contentAppendToLinear {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (v : ContentCategory D Sc cutoff N β) :
    ((pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)) →ₗ[k]
      ((contentAppendTo D Sc cutoff N β σ γ hσ).obj v ⟶
       (contentAppendTo D Sc cutoff N β τ γ hτ).obj v) := by
  let L : ((pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)) →ₗ[k]
      ((pres D Sc).obj (ob D (v.obj.word ++ σ)) ⟶
       (pres D Sc).obj (ob D (v.obj.word ++ τ))) :=
    { toFun := fun a => MonoidalCategoryStruct.whiskerLeft ((pres D Sc).obj (ob D v.obj.word)) a
      map_add' := fun a b => MonoidalSupercategory.whiskerLeft_add k _ a b
      map_smul' := fun r a => MonoidalSupercategory.whiskerLeft_smul (R := k) _ r a }
  exact (truncatedIdeal D Sc cutoff N _ _).mkQ.comp
    ((TensorProduct.mk k (End (obj D Sc cutoff v.obj.word).fst) _ (𝟙 _)).comp L)

@[simp] theorem contentAppendToLinear_apply {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (v : ContentCategory D Sc cutoff N β)
    (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)) :
    contentAppendToLinear D Sc cutoff N hσ hτ v a =
      contentAppendToComponent D Sc cutoff N hσ hτ a v := rfl

@[simp] theorem contentAppendToComponent_neg {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ))
    (v : ContentCategory D Sc cutoff N β) :
    contentAppendToComponent D Sc cutoff N hσ hτ (-a) v =
      -contentAppendToComponent D Sc cutoff N hσ hτ a v := by
  exact (contentAppendToLinear D Sc cutoff N hσ hτ v).map_neg a

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

end OddMath.QuiverHecke.ELVOld
