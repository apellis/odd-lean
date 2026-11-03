/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightNilHeckeRelation

/-! # Distinct-colour signed slides in the original-weight action

Brundan--Ellis (1.8), DeformedActionAssembly §6. The two selected pair
charts retain the given crossing and the independently defined dots.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
section Coordinates
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]

def ModuleCrossSlide {A B : Superfunctor k C (SVec k)}
    (c : A ⟶ B) (x : A ⟶ A) (y : B ⟶ B) (w : C) (s : k) : Prop :=
  (c.total w).comp (x.total w) = s • (y.total w).comp (c.total w)

def ModuleCrossCoordinateSquare {A B E F : Superfunctor k C (SVec k)}
    (e : A ≅ E) (f : B ≅ F) (c : A ⟶ B) (w : C)
    (c' : E.obj w →ₗ[k] F.obj w) : Prop :=
  (f.hom.total w).comp (c.total w) = c'.comp (e.hom.total w)

private theorem crossSquare_of_total {A B E F : Superfunctor k C (SVec k)}
    (e : A ≅ E) (f : B ≅ F) (c : A ⟶ B) (w : C)
    (c' : E.obj w →ₗ[k] F.obj w)
    (h : c.total w = (moduleIsoLinearEquiv f w).symm.toLinearMap.comp
      (c'.comp (moduleIsoLinearEquiv e w).toLinearMap)) :
    ModuleCrossCoordinateSquare e f c w c' := by
  apply LinearMap.ext
  intro v
  change (moduleIsoLinearEquiv f w) (c.total w v) = c' ((moduleIsoLinearEquiv e w) v)
  rw [h]
  exact (moduleIsoLinearEquiv f w).apply_symm_apply _

private theorem crossSlide_of_squares {A B E F : Superfunctor k C (SVec k)}
    (e : A ≅ E) (f : B ≅ F) (c : A ⟶ B) (x : A ⟶ A) (y : B ⟶ B)
    (w : C) (s : k) (c' : E.obj w →ₗ[k] F.obj w)
    (x' : Module.End k (E.obj w)) (y' : Module.End k (F.obj w))
    (hc : ModuleCrossCoordinateSquare e f c w c')
    (hx : ModuleCoordinateSquare e x w x') (hy : ModuleCoordinateSquare f y w y')
    (h : c'.comp x' = s • y'.comp c') : ModuleCrossSlide c x y w s := by
  apply LinearMap.ext
  intro v
  apply (moduleIsoLinearEquiv f w).injective
  have hc' (z : A.obj w) : (f.hom.total w) (c.total w z) = c' ((e.hom.total w) z) :=
    LinearMap.congr_fun hc z
  have hx' (z : A.obj w) := ModuleCoordinateSquare_apply hx z
  have hy' (z : B.obj w) := ModuleCoordinateSquare_apply hy z
  change (f.hom.total w) (c.total w (x.total w v)) =
    (f.hom.total w) (s • y.total w (c.total w v))
  rw [map_smul, hc', hx', hy', hc']
  exact LinearMap.congr_fun h ((e.hom.total w) v)
end Coordinates

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)

private theorem pair_inner_square_to (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (w : ContentCategory D Sc cutoff bound ε.1) :
    ModuleCoordinateSquare
      ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).app M)
      ((elvActionDot D Sc cutoff bound j Λ h₁ ▷ elvE D Sc cutoff bound i Λ h₂).app
        (D.parity j) M ε) w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
          (firstDot_parity D Sc j [i])) (M β) w) := by
  cases hε
  have h := elvWeightPairComparison_inner_total D Sc cutoff bound i j Λ h₁ h₂ β M w
  rw [contentInduction_inner_positioned] at h
  exact h

private theorem pair_outer_square_to (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (w : ContentCategory D Sc cutoff bound ε.1) :
    ModuleCoordinateSquare
      ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).app M)
      ((elvE D Sc cutoff bound j Λ h₁ ◁ elvActionDot D Sc cutoff bound i Λ h₂).app
        (D.parity i) M ε) w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
          (contentPairDot_one_parity D Sc j i)) (M β) w) := by
  cases hε
  have h := elvWeightPairComparison_outer_total D Sc cutoff bound i j Λ h₁ h₂ β M w
  rw [contentInduction_outer_positioned] at h
  exact h
end OddMath.QuiverHecke.ELVOld
