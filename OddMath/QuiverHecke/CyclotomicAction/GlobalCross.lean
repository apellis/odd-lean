/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalSupport
import OddMath.QuiverHecke.CyclotomicAction.CrossingTransformation
import OddMath.QuiverHecke.CyclotomicAction.Square

/-!
# The crossing on cyclotomic content blocks

Ports the blockwise crossing of
`Categorification/KLR/CyclotomicAction/GlobalCross.lean`. The target content
is supplied explicitly, so the two strand orders land in the same full
supercategory. The underlying crossing is the restriction of
`cyclotomicSuperInductionCrossing`, which is the signed `SuperCrossing`
corner map transported along `inductionFunctorComparison`; no second
crossing is constructed. As in the even file, the Rouquier crossing is
`-ψ` for equal colours and `ψ` otherwise (`globalBlockSignedCross`).
The product over weight blocks and its height-zero boundary are separate.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)
  (i j : I) (n : ℕ) (β δ : Multiset I)

/-- Two inductions land in the sum content, with the displayed strand order. -/
theorem contentSupported_induction₂ (h : {i} + ({j} + β) = δ)
    (M : CyclotomicSupermodules D Sc a ha n) (hM : ContentSupported D Sc a ha n β M) :
    ContentSupported D Sc a ha (n + 1 + 1) δ
      ((cyclotomicSuperInduction D Sc i a ha (n + 1)).obj
        ((cyclotomicSuperInduction D Sc j a ha n).obj M)) := by
  subst h
  exact contentSupported_induction D Sc a ha i (n + 1) _ _
    (contentSupported_induction D Sc a ha j n β M hM)

/-- Two successive inductions with an explicitly chosen common target content. -/
def globalBlockInduction₂ (h : {i} + ({j} + β) = δ) :
    Superfunctor k (CyclotomicContentModules D Sc a ha n β)
      (CyclotomicContentModules D Sc a ha (n + 1 + 1) δ) :=
  fullLiftSuperfunctor _ _
    ⟨cyclotomicSuperInduction D Sc j a ha n ⋙ cyclotomicSuperInduction D Sc i a ha (n + 1)⟩
    (contentSupported_induction₂ D Sc a ha i j n β δ h)

omit [Fintype I] in
/-- The two orders have the same target content. -/
theorem swapped_content (h : {i} + ({j} + β) = δ) : {j} + ({i} + β) = δ :=
  (add_left_comm _ _ _).trans h

/-- The constructed homogeneous crossing `ψ`, restricted to content blocks. -/
def globalBlockCross (h : {i} + ({j} + β) = δ) :
    globalBlockInduction₂ D Sc a ha i j n β δ h ⟶
      globalBlockInduction₂ D Sc a ha j i n β δ (swapped_content i j β δ h) :=
  fullLiftTrans _ _
    (contentSupported_induction₂ D Sc a ha i j n β δ h)
    (contentSupported_induction₂ D Sc a ha j i n β δ (swapped_content i j β δ h))
    (cyclotomicSuperInductionCrossing D Sc i j a ha n)

/-- Forgetting content gives the existing crossing component, with no extra sign. -/
@[simp] theorem globalBlockCross_app (h : {i} + ({j} + β) = δ) (p : ZMod 2)
    (M : CyclotomicContentModules D Sc a ha n β) :
    ((globalBlockCross D Sc a ha i j n β δ h).app p M).hom =
      (cyclotomicSuperInductionCrossing D Sc i j a ha n).app p M.obj := rfl

/-- The crossing on content blocks has the parity of its two colours. -/
theorem globalBlockCross_homogeneous (h : {i} + ({j} + β) = δ) :
    (globalBlockCross D Sc a ha i j n β δ h).IsHomogeneous (D.parity i * D.parity j) :=
  fullLiftTrans_homogeneous _ _ _ _ _
    (cyclotomicSuperInductionCrossing_homogeneous D Sc i j a ha n)

/-- The Rouquier crossing of the even file: `-ψ` for equal colours, `ψ` otherwise. -/
def globalBlockSignedCross [DecidableEq I] (h : {i} + ({j} + β) = δ) :
    globalBlockInduction₂ D Sc a ha i j n β δ h ⟶
      globalBlockInduction₂ D Sc a ha j i n β δ (swapped_content i j β δ h) :=
  if i = j then -globalBlockCross D Sc a ha i j n β δ h
  else globalBlockCross D Sc a ha i j n β δ h

theorem globalBlockSignedCross_of_ne [DecidableEq I] {i j : I} (hij : i ≠ j)
    (h : {i} + ({j} + β) = δ) :
    globalBlockSignedCross D Sc a ha i j n β δ h = globalBlockCross D Sc a ha i j n β δ h :=
  by simp [globalBlockSignedCross, hij]

theorem globalBlockSignedCross_self [DecidableEq I] (h : {i} + ({i} + β) = δ) :
    globalBlockSignedCross D Sc a ha i i n β δ h = -globalBlockCross D Sc a ha i i n β δ h :=
  by simp [globalBlockSignedCross]

/-- Two homogeneous transformations of the same parity whose components of that parity
compose to zero have zero composite. -/
theorem superTrans_comp_eq_zero {C₁ C₂ : Type*} [Category C₁] [Preadditive C₁] [Linear k C₁]
    [Supercategory k C₁] [Category C₂] [Preadditive C₂] [Linear k C₂] [Supercategory k C₂]
    {F G H : Superfunctor k C₁ C₂} {x : F ⟶ G} {y : G ⟶ H} {d : ZMod 2}
    (hx : SuperNatTrans.IsHomogeneous x d) (hy : SuperNatTrans.IsHomogeneous y d)
    (h : ∀ M, x.app d M ≫ y.app d M = 0) : x ≫ y = 0 := by
  have hx' : ∀ q, q ≠ d → ∀ M, x.app q M = 0 := fun q hq M => congrFun (hx q hq) M
  have hy' : ∀ q, q ≠ d → ∀ M, y.app q M = 0 := fun q hq M => congrFun (hy q hq) M
  rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) d with rfl | rfl
  · apply Superfunctor.hom_ext_parity
    · intro M
      rw [Superfunctor.comp_app_zero, hx' 1 (by decide) M, h M, Superfunctor.zero_app]
      simp
    · intro M
      rw [Superfunctor.comp_app_one, hx' 1 (by decide) M, hy' 1 (by decide) M,
        Superfunctor.zero_app]
      simp
  · apply Superfunctor.hom_ext_parity
    · intro M
      rw [Superfunctor.comp_app_zero, hx' 0 (by decide) M, h M, Superfunctor.zero_app]
      simp
    · intro M
      rw [Superfunctor.comp_app_one, hx' 0 (by decide) M, hy' 0 (by decide) M,
        Superfunctor.zero_app]
      simp

/-- The same-colour crossing on composed superinduction squares to zero. -/
theorem cyclotomicSuperInductionCrossing_square (M : CyclotomicSupermodules D Sc a ha n) :
    (cyclotomicSuperInductionCrossing D Sc i i a ha n).app (D.parity i * D.parity i) M ≫
      (cyclotomicSuperInductionCrossing D Sc i i a ha n).app (D.parity i * D.parity i) M = 0 := by
  have hw : SuperBimodule.whiskerRight (compositionSuperCrossing D Sc i i a ha n) M ≫
      SuperBimodule.whiskerRight (compositionSuperCrossing D Sc i i a ha n) M = 0 := by
    rw [← SuperBimodule.comp_whiskerRight, compositionSuperCrossing_square]
    have h0 := SuperBimodule.smul_whiskerRight (0 : compositionCorner D Sc i i a ha n ⟶
      compositionCorner D Sc i i a ha n) M (0 : k)
    rwa [zero_smul, zero_smul] at h0
  rw [cyclotomicSuperInductionCrossing_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hw]
  simp

/-- The same-colour crossing on content blocks squares to zero (even `globalCross_sq`). -/
theorem globalBlockCross_square (h : {i} + ({i} + β) = δ) :
    globalBlockCross D Sc a ha i i n β δ h ≫ globalBlockCross D Sc a ha i i n β δ h = 0 :=
  superTrans_comp_eq_zero (globalBlockCross_homogeneous D Sc a ha i i n β δ h)
    (globalBlockCross_homogeneous D Sc a ha i i n β δ h) fun M =>
      InducedCategory.hom_ext (cyclotomicSuperInductionCrossing_square D Sc a ha i n M.obj)

/-- The signed same-colour crossing also squares to zero. -/
theorem globalBlockSignedCross_square [DecidableEq I] (h : {i} + ({i} + β) = δ) :
    globalBlockSignedCross D Sc a ha i i n β δ h ≫
      globalBlockSignedCross D Sc a ha i i n β δ h = 0 := by
  rw [globalBlockSignedCross_self, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg,
    globalBlockCross_square]

end OddMath.QuiverHecke.CyclotomicAction
