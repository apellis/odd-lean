/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightCrossing
import OddMath.QuiverHecke.CyclotomicAction.GlobalCross

/-!
# The crossing on content blocks at every height

Ports the block crossing of `Categorification/KLR/CyclotomicAction/GlobalCross.lean`
(`globalCross`, `globalCross_sq`) to every height of the extended tower,
including two inductions from the empty word. The square-zero relation of
`Square` holds for `heightLastCrossing` (at two strands it is the image of
`affineLastCrossing_square`), hence for the corner crossing and for
`heightSuperInductionCrossing`. On content blocks with an explicit common
target content, the restricted crossing `heightBlockCross` has parity
`|i||j|` and the same-colour crossing squares to zero.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)
  (i j : I) (n : ℕ)

/-- The same-colour last crossing squares to zero at every height. -/
theorem heightLastCrossing_square :
    heightLastCrossing D Sc a i i n * heightLastCrossing D Sc a i i n = 0 := by
  cases n with
  | zero =>
    change cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i i 0) *
      cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i i 0) = 0
    rw [← map_mul, affineLastCrossing_square, map_zero]
  | succ n => exact cyclotomicLastCrossing_square D Sc i a n

/-- The signed corner crossing squares to zero on homogeneous elements. -/
theorem heightCompositionSuperCrossing_square_apply {p : ZMod 2}
    (x : (heightCompositionCorner D Sc i i a ha n).toSVec)
    (hx : x ∈ (heightCompositionCorner D Sc i i a ha n).toSVec.part p) :
    ((heightCompositionSuperCrossing D Sc i i a ha n).1
      ((heightCompositionSuperCrossing D Sc i i a ha n).1 x)).val = 0 := by
  have hf : (heightCompositionSuperCrossing D Sc i i a ha n).1 x ∈
      (heightCompositionCorner D Sc i i a ha n).toSVec.part (p + D.parity i * D.parity i) :=
    SVec.apply_mem_part (heightCompositionCrossingLinear_parity D Sc i i a ha n) hx
  erw [heightCompositionSuperCrossing_apply D Sc i i a ha n _ hf,
    heightCompositionSuperCrossing_apply D Sc i i a ha n x hx]
  rw [smul_mul_assoc, mul_assoc, heightLastCrossing_square, mul_zero, smul_zero, smul_zero]

/-- The homogeneous corner crossing has square zero at every height. -/
theorem heightCompositionSuperCrossing_square :
    heightCompositionSuperCrossing D Sc i i a ha n ≫
      heightCompositionSuperCrossing D Sc i i a ha n = 0 := by
  apply Subtype.ext
  apply SVec.hom_ext
  intro x
  have h (p : ZMod 2) : (heightCompositionSuperCrossing D Sc i i a ha n).1
      ((heightCompositionSuperCrossing D Sc i i a ha n).1
        ((heightCompositionCorner D Sc i i a ha n).toSVec.proj p x)) = 0 := by
    apply Subtype.ext
    exact heightCompositionSuperCrossing_square_apply D Sc a ha i n _
      ((heightCompositionCorner D Sc i i a ha n).toSVec.proj_mem_part p x)
  change (heightCompositionSuperCrossing D Sc i i a ha n).1
    ((heightCompositionSuperCrossing D Sc i i a ha n).1 x) = 0
  rw [← (heightCompositionCorner D Sc i i a ha n).toSVec.proj_apply_add x, map_add, map_add,
    h 0, h 1, add_zero]

/-- The same-colour crossing on two inductions squares to zero at every height. -/
theorem heightSuperInductionCrossing_square (M : HeightModules D Sc a ha n) :
    (heightSuperInductionCrossing D Sc i i a ha n).app (D.parity i * D.parity i) M ≫
      (heightSuperInductionCrossing D Sc i i a ha n).app (D.parity i * D.parity i) M = 0 := by
  have hw : SuperBimodule.whiskerRight (heightCompositionSuperCrossing D Sc i i a ha n) M ≫
      SuperBimodule.whiskerRight (heightCompositionSuperCrossing D Sc i i a ha n) M = 0 := by
    rw [← SuperBimodule.comp_whiskerRight, heightCompositionSuperCrossing_square]
    have h0 := SuperBimodule.smul_whiskerRight (0 : heightCompositionCorner D Sc i i a ha n ⟶
      heightCompositionCorner D Sc i i a ha n) M (0 : k)
    rwa [zero_smul, zero_smul] at h0
  rw [heightSuperInductionCrossing_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hw]
  simp

variable (β δ : Multiset I)

/-- Two inductions land in the sum content at every height. -/
theorem heightContentSupported_induction₂ (h : {i} + ({j} + β) = δ)
    (M : HeightModules D Sc a ha n) (hM : heightContentSupported D Sc a ha n β M) :
    heightContentSupported D Sc a ha (n + 1 + 1) δ
      ((heightSuperInduction D Sc i a ha (n + 1)).obj
        ((heightSuperInduction D Sc j a ha n).obj M)) := by
  subst h
  exact heightContentSupported_induction D Sc i a ha (n + 1) _ _
    (heightContentSupported_induction D Sc j a ha n β M hM)

/-- Two successive inductions with an explicit common target content, at every height. -/
def heightBlockInduction₂ (h : {i} + ({j} + β) = δ) :
    Superfunctor k (ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β))
      (ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha (n + 1 + 1) δ)) :=
  fullLiftSuperfunctor _ _
    ⟨heightSuperInduction D Sc j a ha n ⋙ heightSuperInduction D Sc i a ha (n + 1)⟩
    (heightContentSupported_induction₂ D Sc a ha i j n β δ h)

/-- The homogeneous crossing restricted to content blocks, at every height. -/
def heightBlockCross (h : {i} + ({j} + β) = δ) :
    heightBlockInduction₂ D Sc a ha i j n β δ h ⟶
      heightBlockInduction₂ D Sc a ha j i n β δ (swapped_content i j β δ h) :=
  fullLiftTrans _ _
    (heightContentSupported_induction₂ D Sc a ha i j n β δ h)
    (heightContentSupported_induction₂ D Sc a ha j i n β δ (swapped_content i j β δ h))
    (heightSuperInductionCrossing D Sc i j a ha n)

@[simp] theorem heightBlockCross_app (h : {i} + ({j} + β) = δ) (p : ZMod 2)
    (M : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β)) :
    ((heightBlockCross D Sc a ha i j n β δ h).app p M).hom =
      (heightSuperInductionCrossing D Sc i j a ha n).app p M.obj := rfl

theorem heightBlockCross_homogeneous (h : {i} + ({j} + β) = δ) :
    (heightBlockCross D Sc a ha i j n β δ h).IsHomogeneous (D.parity i * D.parity j) :=
  fullLiftTrans_homogeneous _ _ _ _ _
    (heightSuperInductionCrossing_homogeneous D Sc i j a ha n)

/-- The same-colour block crossing squares to zero at every height. -/
theorem heightBlockCross_square (h : {i} + ({i} + β) = δ) :
    heightBlockCross D Sc a ha i i n β δ h ≫ heightBlockCross D Sc a ha i i n β δ h = 0 :=
  superTrans_comp_eq_zero (heightBlockCross_homogeneous D Sc a ha i i n β δ h)
    (heightBlockCross_homogeneous D Sc a ha i i n β δ h) fun M =>
      InducedCategory.hom_ext (heightSuperInductionCrossing_square D Sc a ha i n M.obj)

end OddMath.QuiverHecke.CyclotomicAction
