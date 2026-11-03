/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightQuadraticRelation

/-! # Signed nilHecke slides in the original-weight action

Brundan--Ellis (1.8), DeformedActionAssembly §6: retain the independently
given dots and crossing, both selected pair coordinates and every absent
weight sector.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
section Coordinates
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]

/-- The signed slide, expressed at whole module maps before specializing
coend carriers. -/
def ModuleNilHeckeSlide {A : Superfunctor k C (SVec k)}
    (a b c d : A ⟶ A) (w : C) (s : k) : Prop :=
  (a.total w).comp (b.total w) - s • (c.total w).comp (d.total w) = LinearMap.id

private theorem coordinateSquare_of_total {A E : Superfunctor k C (SVec k)}
    (e : A ≅ E) (c : A ⟶ A) (w : C) (c' : Module.End k (E.obj w))
    (h : c.total w = (moduleIsoLinearEquiv e w).symm.toLinearMap.comp
      (c'.comp (moduleIsoLinearEquiv e w).toLinearMap)) : ModuleCoordinateSquare e c w c' := by
  apply LinearMap.ext
  intro v
  change (moduleIsoLinearEquiv e w) (c.total w v) = c' ((moduleIsoLinearEquiv e w) v)
  rw [h]
  exact (moduleIsoLinearEquiv e w).apply_symm_apply _

private theorem moduleSlide_of_squares {A E : Superfunctor k C (SVec k)}
    (e : A ≅ E) (a b c d : A ⟶ A) (w : C) (s : k)
    (a' b' c' d' : Module.End k (E.obj w))
    (ha : ModuleCoordinateSquare e a w a') (hb : ModuleCoordinateSquare e b w b')
    (hc : ModuleCoordinateSquare e c w c') (hd : ModuleCoordinateSquare e d w d')
    (h : a'.comp b' - s • c'.comp d' = LinearMap.id) : ModuleNilHeckeSlide a b c d w s := by
  apply LinearMap.ext
  intro v
  apply (moduleIsoLinearEquiv e w).injective
  have ha' (z : A.obj w) := ModuleCoordinateSquare_apply ha z
  have hb' (z : A.obj w) := ModuleCoordinateSquare_apply hb z
  have hc' (z : A.obj w) := ModuleCoordinateSquare_apply hc z
  have hd' (z : A.obj w) := ModuleCoordinateSquare_apply hd z
  change (e.hom.total w) (a.total w (b.total w v) - s • c.total w (d.total w v)) =
    (e.hom.total w) v
  rw [map_sub, map_smul, ha', hb', hc', hd']
  exact LinearMap.congr_fun h ((e.hom.total w) v)
private theorem moduleSlide_of_isZero {A : Superfunctor k C (SVec k)}
    (hA : Limits.IsZero A) (a b c d : A ⟶ A) (w : C) (s : k) :
    ModuleNilHeckeSlide a b c d w s := by
  let := moduleValue_subsingleton_of_isZero hA w
  apply LinearMap.ext
  intro v
  exact Subsingleton.elim _ _
end Coordinates

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

private theorem content_slide_to (β : Multiset I) (i : I) (γ : Multiset I)
    (hγ : β + ([i,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (contentCrossAffine_mem D Sc i i)) M w).comp
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (pairDot_one_parity D Sc i)) M w) -
      sign k (D.parity i * D.parity i) •
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (pairDot_zero_parity D Sc i)) M w).comp
          (BalancedInduction.transformLinear
            (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (contentCrossAffine_mem D Sc i i)) M w) =
      LinearMap.id := by
  subst γ
  exact contentInduction_normalized_slide_linear D Sc cutoff bound β i M w

private theorem content_slide_right_to (β : Multiset I) (i : I) (γ : Multiset I)
    (hγ : β + ([i,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    let A := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (pairDot_zero_parity D Sc i)) M w
    let B := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (pairDot_one_parity D Sc i)) M w
    let C := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (contentCrossAffine_mem D Sc i i)) M w
    B.comp C - sign k (D.parity i * D.parity i) • C.comp A = LinearMap.id := by
  subst γ
  exact contentInduction_normalized_slide_right_linear D Sc cutoff bound β i M w

variable (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

theorem elvWeightCrossVia_slideLeft
    (β : WeightBlocks D Λ x₀)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound (blockSucc₂ D i i Λ h₁ h₂ β).1) :
    let ε := blockSucc₂ D i i Λ h₁ h₂ β
    ModuleNilHeckeSlide
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      ((elvE D Sc cutoff bound i Λ h₁ ◁
        elvActionDot D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      ((elvActionDot D Sc cutoff bound i Λ h₁ ▷
        elvE D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      w (sign k (D.parity i * D.parity i)) := by
  dsimp only
  let ε := blockSucc₂ D i i Λ h₁ h₂ β
  let hs := elvWeightPair_content_eq D i i Λ h₁ h₂ β ε rfl
  let e := moduleIsoLinearEquiv
    ((elvWeightPairComparison D Sc cutoff bound i i Λ h₁ h₂ β ε rfl).app M) w
  let A := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound hs hs (pairDot_zero_parity D Sc i)) (M β) w
  let B := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound hs hs (pairDot_one_parity D Sc i)) (M β) w
  let C := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound hs hs (contentCrossAffine_mem D Sc i i)) (M β) w
  have hi := elvWeightPairComparison_inner_total D Sc cutoff bound i i Λ h₁ h₂ β M w
  rw [contentInduction_inner_positioned] at hi
  have ho := elvWeightPairComparison_outer_total D Sc cutoff bound i i Λ h₁ h₂ β M w
  rw [contentInduction_outer_positioned] at ho
  have hc : ModuleCoordinateSquare
      ((elvWeightPairComparison D Sc cutoff bound i i Λ h₁ h₂ β ε rfl).app M)
      (elvWeightCrossComponent D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
        (D.parity i * D.parity i) M ε) w C := by
    apply coordinateSquare_of_total
    rw [elvWeightCrossComponent_total D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ β ε rfl M w,
      contentInductionTransform_total]
  apply moduleSlide_of_squares
    ((elvWeightPairComparison D Sc cutoff bound i i Λ h₁ h₂ β ε rfl).app M)
    _ _ _ _ w _ C B A C
  · exact hc
  · exact ho
  · exact hi
  · exact hc
  · exact content_slide_to D Sc cutoff bound β.1 i ε.1 hs (M β) w
theorem elvWeightCrossVia_slideRight
    (β : WeightBlocks D Λ x₀)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound (blockSucc₂ D i i Λ h₁ h₂ β).1) :
    let ε := blockSucc₂ D i i Λ h₁ h₂ β
    ModuleNilHeckeSlide
      ((elvE D Sc cutoff bound i Λ h₁ ◁
        elvActionDot D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      ((elvActionDot D Sc cutoff bound i Λ h₁ ▷
        elvE D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      w (sign k (D.parity i * D.parity i)) := by
  dsimp only
  let ε := blockSucc₂ D i i Λ h₁ h₂ β
  let hs := elvWeightPair_content_eq D i i Λ h₁ h₂ β ε rfl
  let e := moduleIsoLinearEquiv
    ((elvWeightPairComparison D Sc cutoff bound i i Λ h₁ h₂ β ε rfl).app M) w
  let A := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound hs hs (pairDot_zero_parity D Sc i)) (M β) w
  let B := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound hs hs (pairDot_one_parity D Sc i)) (M β) w
  let C := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound hs hs (contentCrossAffine_mem D Sc i i)) (M β) w
  have hi := elvWeightPairComparison_inner_total D Sc cutoff bound i i Λ h₁ h₂ β M w
  rw [contentInduction_inner_positioned] at hi
  have ho := elvWeightPairComparison_outer_total D Sc cutoff bound i i Λ h₁ h₂ β M w
  rw [contentInduction_outer_positioned] at ho
  have hc : ModuleCoordinateSquare
      ((elvWeightPairComparison D Sc cutoff bound i i Λ h₁ h₂ β ε rfl).app M)
      (elvWeightCrossComponent D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
        (D.parity i * D.parity i) M ε) w C := by
    apply coordinateSquare_of_total
    rw [elvWeightCrossComponent_total D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ β ε rfl M w,
      contentInductionTransform_total]
  apply moduleSlide_of_squares
    ((elvWeightPairComparison D Sc cutoff bound i i Λ h₁ h₂ β ε rfl).app M)
    _ _ _ _ w _ B C C A
  · exact ho
  · exact hc
  · exact hc
  · exact hi
  · exact content_slide_right_to D Sc cutoff bound β.1 i ε.1 hs (M β) w
theorem elvWeightCrossComponent_slideLeft
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (ε : WeightBlocks D Λ x₂)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    ModuleNilHeckeSlide
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      ((elvE D Sc cutoff bound i Λ h₁ ◁
        elvActionDot D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      ((elvActionDot D Sc cutoff bound i Λ h₁ ▷
        elvE D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      w (sign k (D.parity i * D.parity i)) := by
  by_cases hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    exact elvWeightCrossVia_slideLeft D Sc cutoff bound i Λ h₁ h₂ β M w
  · exact moduleSlide_of_isZero
      (elvEFunctor_comp₂_isZero D Sc cutoff bound i i Λ h₁ h₂ ε hε M) _ _ _ _ w _

theorem elvWeightCrossComponent_slideRight
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (ε : WeightBlocks D Λ x₂)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    ModuleNilHeckeSlide
      ((elvE D Sc cutoff bound i Λ h₁ ◁
        elvActionDot D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      ((elvActionDot D Sc cutoff bound i Λ h₁ ▷
        elvE D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      w (sign k (D.parity i * D.parity i)) := by
  by_cases hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    exact elvWeightCrossVia_slideRight D Sc cutoff bound i Λ h₁ h₂ β M w
  · exact moduleSlide_of_isZero
      (elvEFunctor_comp₂_isZero D Sc cutoff bound i i Λ h₁ h₂ ε hε M) _ _ _ _ w _

end OddMath.QuiverHecke.ELVOld
