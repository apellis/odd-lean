/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalSupport
import OddMath.QuiverHecke.CyclotomicAction.CrossingTransformation

/-!
# The signed crossing on cyclotomic content blocks

Ports the blockwise crossing of
`Categorification/KLR/CyclotomicAction/GlobalCross.lean`. The target content
is explicitly supplied, allowing the two strand orders to land in the same
full supercategory. The crossing is exactly the restriction of
`cyclotomicSuperInductionCrossing`, which uses the signed `SuperCrossing`
corner map transported along `inductionFunctorComparison`. Thus there is
no competing crossing and no unsigned odd naturality. The product over all
weight blocks and its height-zero boundary are separate constructions.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)
  (i j : I) (n : ℕ) (β δ : Multiset I)

/-- Both inductions land in the sum content, with the displayed strand order. -/
theorem contentSupported_induction₂ (h : {i} + ({j} + β) = δ)
    (M : CyclotomicSupermodules D Sc a ha n) (hM : ContentSupported D Sc a ha n β M) :
    ContentSupported D Sc a ha ((n + 1) + 1) δ
      ((cyclotomicSuperInduction D Sc i a ha (n + 1)).obj
        ((cyclotomicSuperInduction D Sc j a ha n).obj M)) := by
  have h₁ := contentSupported_induction D Sc a ha j n β M hM
  have h₂ := contentSupported_induction D Sc a ha i (n + 1) ({j} + β)
    ((cyclotomicSuperInduction D Sc j a ha n).obj M) h₁
  rw [← h]
  exact h₂

/-- Two successive induction functors with an explicitly chosen common content. -/
def globalBlockInduction₂ (h : {i} + ({j} + β) = δ) :
    Superfunctor k (CyclotomicContentModules D Sc a ha n β)
      (CyclotomicContentModules D Sc a ha ((n + 1) + 1) δ) := by
  let P : ObjectProperty (CyclotomicSupermodules D Sc a ha n) := ContentSupported D Sc a ha n β
  let Q : ObjectProperty (CyclotomicSupermodules D Sc a ha ((n + 1) + 1)) := ContentSupported D Sc a ha ((n + 1) + 1) δ
  change Superfunctor k P.FullSubcategory Q.FullSubcategory
  apply fullLiftSuperfunctor P Q
    ⟨cyclotomicSuperInduction D Sc j a ha n ⋙ cyclotomicSuperInduction D Sc i a ha (n + 1)⟩
  intro M hM
  exact contentSupported_induction₂ D Sc a ha i j n β δ h M hM

omit [Fintype I] in
/-- The two orders have the same target content. -/
theorem swapped_content (h : {i} + ({j} + β) = δ) : {j} + ({i} + β) = δ :=
  (add_left_comm _ _ _).trans h

/-- The already constructed homogeneous signed crossing, restricted to content. -/
def globalBlockCross (h : {i} + ({j} + β) = δ) :
    globalBlockInduction₂ D Sc a ha i j n β δ h ⟶
      globalBlockInduction₂ D Sc a ha j i n β δ (swapped_content i j β δ h) where
  app p M := ⟨(cyclotomicSuperInductionCrossing D Sc i j a ha n).app p M.obj⟩
  app_mem p M := (cyclotomicSuperInductionCrossing D Sc i j a ha n).app_mem p M.obj
  naturality p _ _ _ f hf := InducedCategory.hom_ext
    ((cyclotomicSuperInductionCrossing D Sc i j a ha n).naturality p f.hom hf)

/-- Forgetting content gives the existing crossing component, with no extra sign. -/
@[simp] theorem globalBlockCross_app (h : {i} + ({j} + β) = δ) (p : ZMod 2)
    (M : CyclotomicContentModules D Sc a ha n β) :
    ((globalBlockCross D Sc a ha i j n β δ h).app p M).hom =
      (cyclotomicSuperInductionCrossing D Sc i j a ha n).app p M.obj := rfl

/-- In particular, odd/odd crossing has odd parity on the content blocks. -/
theorem globalBlockCross_homogeneous (h : {i} + ({j} + β) = δ) :
    (globalBlockCross D Sc a ha i j n β δ h).IsHomogeneous (D.parity i * D.parity j) := by
  intro p hp
  funext M
  apply InducedCategory.hom_ext
  exact congrFun (cyclotomicSuperInductionCrossing_homogeneous D Sc i j a ha n p hp) M.obj

end OddMath.QuiverHecke.CyclotomicAction
