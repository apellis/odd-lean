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

end OddMath.QuiverHecke.CyclotomicAction
