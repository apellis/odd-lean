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

omit [Fintype I] in
/-- The two orders have the same target content. -/
theorem swapped_content (h : {i} + ({j} + β) = δ) : {j} + ({i} + β) = δ :=
  (add_left_comm _ _ _).trans h

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

end OddMath.QuiverHecke.CyclotomicAction
