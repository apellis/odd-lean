/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairQuadratic

/-! # The independent weight dots in selected pair coordinates

DeformedActionAssembly §6 (9) requires identifying the two given weight-dot
operators under exactly the pair comparison used for the crossing square.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u

/-- The literal component square, kept as a named proposition while
specializing deep module objects. Unfolding gives equality of whole maps. -/
def ModuleCoordinateSquare
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A E : Superfunctor k C (SVec k)} (e : A ≅ E)
    (x : A ⟶ A) (w : C) (z : E.obj w →ₗ[k] E.obj w) : Prop :=
  (e.hom.total w).comp (x.total w) = z.comp (e.hom.total w)

/-- Evaluation of the whole component square on any input vector. -/
theorem ModuleCoordinateSquare_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A E : Superfunctor k C (SVec k)} {e : A ≅ E}
    {x : A ⟶ A} {w : C} {z : E.obj w →ₗ[k] E.obj w}
    (h : ModuleCoordinateSquare e x w z) (v : A.obj w) :
    e.hom.total w (x.total w v) = z (e.hom.total w v) :=
  congrArg (fun a : A.obj w →ₗ[k] E.obj w => a v) h

private theorem module_coordinate_square_eq
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {P : Type*} [Category* P]
    {F G H : P ⥤ Superfunctor k C (SVec k)}
    (h : F = G) (f : G ≅ H) (M : P)
    (x : F.obj M ⟶ F.obj M) (y : G.obj M ⟶ G.obj M) (w : C)
    (z : (H.obj M).obj w →ₗ[k] (H.obj M).obj w)
    (hx : x = eqToHom (Functor.congr_obj h M) ≫ y ≫
      eqToHom (Functor.congr_obj h M).symm)
    (hy : ((f.hom.app M).total w).comp (y.total w) =
      z.comp ((f.hom.app M).total w)) :
    ModuleCoordinateSquare ((eqToIso h ≪≫ f).app M) x w z := by
  subst G
  have hxy : x = y := by simpa using hx
  rw [hxy]
  simpa only [ModuleCoordinateSquare, eqToIso_refl, Iso.refl_trans, Iso.app_hom] using hy

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- The selected pair comparison intertwines induction on the given first
single-letter dot with its right-whiskered source operator. -/
theorem contentEPairComparison_inner_square (β : Multiset I) (i j : I)
    (γ : Multiset I) (hγ : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    let e := moduleIsoLinearEquiv ((contentEPairToComparison D Sc cutoff bound β i j γ hγ).app M) w
    e.toLinearMap.comp
      (((contentInductionTo D Sc cutoff bound (β + ([i] : Multiset I)) [j] γ
        ((contentPair_sum β i j).symm.trans hγ)).map
        ((contentInductionDot D Sc cutoff bound β i).app (D.parity i) M)).total w) =
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound hγ hγ
        (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [j]))
          (firstDot_parity D Sc i []))) M w).comp e.toLinearMap := by
  dsimp only
  rw [contentInductionDot_component,
    contentInductionMap_total_of_mem _ (BalancedInduction.transformComponent_mem _ M)]
  exact contentInductionComp_inner D Sc cutoff bound β [i] [j] γ _ hγ
    (firstDot_parity D Sc i []) M w

/-- The preceding square with the actual intermediate content retained. -/
theorem contentInductionCompTo_inner_square (β : Multiset I) (i j : I)
    (δ γ : Multiset I) (hδ : β + ([i] : Multiset I) = δ)
    (hγ : δ + ([j] : Multiset I) = γ) (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    let e := moduleIsoLinearEquiv
      ((contentInductionCompTo D Sc cutoff bound β [i] δ hδ [j] γ hγ h).app M) w
    e.toLinearMap.comp
      (((contentInductionTo D Sc cutoff bound δ [j] γ hγ).map
        ((elvContentDotTo D Sc cutoff bound i β δ hδ).app (D.parity i) M)).total w) =
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h
        (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [j]))
          (firstDot_parity D Sc i []))) M w).comp e.toLinearMap := by
  subst δ
  exact contentEPairComparison_inner_square D Sc cutoff bound β i j γ h M w

/-- The selected comparison retains the actual second single-letter dot at
the specified intermediate and output contents. -/
theorem contentInductionCompTo_outer_square (β : Multiset I) (i j : I)
    (δ γ : Multiset I) (hδ : β + ([i] : Multiset I) = δ)
    (hγ : δ + ([j] : Multiset I) = γ) (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    let e := moduleIsoLinearEquiv
      ((contentInductionCompTo D Sc cutoff bound β [i] δ hδ [j] γ hγ h).app M) w
    e.toLinearMap.comp
      (((elvContentDotTo D Sc cutoff bound j δ γ hγ).app (D.parity j)
        ((contentInductionTo D Sc cutoff bound β [i] δ hδ).obj M)).total w) =
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h
        (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
          (firstDot_parity D Sc j []))) M w).comp e.toLinearMap := by
  subst δ
  dsimp only
  rw [contentInductionTransform_total]
  exact contentInductionComp_outer D Sc cutoff bound β [i] [j] γ _ h
    (firstDot_parity D Sc j []) M w

variable (i j : I) (Λ : X) {x₀ x₁ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)

/-- The independently assembled inner weight dot commutes with the same
selected pair comparison used for the weight crossing square. -/
theorem elvWeightPairComparison_inner_total
    (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound (blockSucc₂ D i j Λ h₁ h₂ β).1) :
    ModuleCoordinateSquare
      ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β _ rfl).app M)
      ((elvInductionComponent D Sc cutoff bound i Λ h₂ (blockSucc₂ D i j Λ h₁ h₂ β)).map
        ((elvWeightDot D Sc cutoff bound j Λ h₁).app (D.parity j) M)) w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β _ rfl)
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β _ rfl)
          (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [i]))
            (firstDot_parity D Sc j []))) (M β) w) := by
  change ModuleCoordinateSquare
    ((eqToIso (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) ≪≫
      Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
        (elvBlockPairComparison D Sc cutoff bound i j Λ h₁ h₂ β)).app M) _ w _
  exact module_coordinate_square_eq
    (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β)
    (Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
      (elvBlockPairComparison D Sc cutoff bound i j Λ h₁ h₂ β)) M _ _ w _
    (elvWeightInnerDot_blockSucc D Sc cutoff bound i j Λ h₁ h₂ (D.parity j) β M)
    (contentInductionCompTo_inner_square D Sc cutoff bound β.1 j i
      (blockSucc D Λ j h₁ β).1 (blockSucc₂ D i j Λ h₁ h₂ β).1
      (elvBlockSucc_content_eq D j Λ h₁ β)
      (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ j h₁ β))
      (elvBlockPair_content_eq D i j Λ h₁ h₂ β) (M β) w)

/-- The outer weight dot uses the identical selected pair comparison. -/
theorem elvWeightPairComparison_outer_total
    (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound (blockSucc₂ D i j Λ h₁ h₂ β).1) :
    ModuleCoordinateSquare
      ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β _ rfl).app M)
      (elvWeightDotComponent D Sc cutoff bound i Λ h₂ (D.parity i)
        ((elvEFunctor D Sc cutoff bound j Λ h₁).obj M)
        (blockSucc₂ D i j Λ h₁ h₂ β)) w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β _ rfl)
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β _ rfl)
          (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [j]))
            (firstDot_parity D Sc i []))) (M β) w) := by
  change ModuleCoordinateSquare
    ((eqToIso (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) ≪≫
      Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
        (elvBlockPairComparison D Sc cutoff bound i j Λ h₁ h₂ β)).app M) _ w _
  exact module_coordinate_square_eq
    (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β)
    (Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
      (elvBlockPairComparison D Sc cutoff bound i j Λ h₁ h₂ β)) M _ _ w _
    (elvWeightOuterDot_blockSucc D Sc cutoff bound i j Λ h₁ h₂ (D.parity i) β M)
    (contentInductionCompTo_outer_square D Sc cutoff bound β.1 j i
      (blockSucc D Λ j h₁ β).1 (blockSucc₂ D i j Λ h₁ h₂ β).1
      (elvBlockSucc_content_eq D j Λ h₁ β)
      (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ j h₁ β))
      (elvBlockPair_content_eq D i j Λ h₁ h₂ β) (M β) w)

end OddMath.QuiverHecke.ELVOld
