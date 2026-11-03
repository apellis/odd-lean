import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTripleDotCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVTripleCorrectionPolynomial

/-! # The original-Sc correction in the selected weight triple coordinates

Brundan--Ellis (1.9), repeated outer colour. The ordered polynomial in the
three literal weight-dot positions is conjugated by the selected C3 chart
to the same polynomial in the three indexed affine generators. The actual
output content is retained; no canonical-content replacement is made.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem coordinate_conjugation
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A B : Superfunctor k C (SVec k)} (e : A ≅ B) (x : End A) (w : C)
    (z : Module.End k (B.obj w)) (h : ModuleCoordinateSquare e x w z) :
    ((moduleIsoLinearEquiv e w).conjAlgEquiv k).toAlgHom (x.total w) = z := by
  apply LinearMap.ext
  intro v
  change (moduleIsoLinearEquiv e w) (x.total w ((moduleIsoLinearEquiv e w).symm v)) = z v
  have hv := ModuleCoordinateSquare_apply h ((moduleIsoLinearEquiv e w).symm v)
  change (moduleIsoLinearEquiv e w) (x.total w ((moduleIsoLinearEquiv e w).symm v)) =
    z ((moduleIsoLinearEquiv e w) ((moduleIsoLinearEquiv e w).symm v)) at hv
  simpa only [LinearEquiv.apply_symm_apply] using hv

private theorem polynomial_of_coordinates
    {k C I X : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C] [AddCommGroup X]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (i j : I)
    {A B : Superfunctor k C (SVec k)} (e : A ≅ B) (x₀ x₁ x₂ : End A) (w : C)
    (z₀ z₁ z₂ : Module.End k (B.obj w))
    (h₀ : ModuleCoordinateSquare e x₀ w z₀)
    (h₁ : ModuleCoordinateSquare e x₁ w z₁)
    (h₂ : ModuleCoordinateSquare e x₂ w z₂) :
    ((moduleIsoLinearEquiv e w).conjAlgEquiv k).toAlgHom
        (tripleDotCorrectionPolynomial D Sc i j (x₀.total w) (x₁.total w) (x₂.total w)) =
      tripleDotCorrectionPolynomial D Sc i j z₀ z₁ z₂ := by
  have hp := tripleDotCorrectionPolynomial_map D Sc
    ((moduleIsoLinearEquiv e w).conjAlgEquiv k).toAlgHom i j (x₀.total w) (x₁.total w) (x₂.total w)
  rw [coordinate_conjugation e x₀ w z₀ h₀, coordinate_conjugation e x₁ w z₁ h₁,
    coordinate_conjugation e x₂ w z₂ h₂] at hp
  exact hp

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {a b c d : X}
  (h₁ : a + D.α i = b) (h₂ : b + D.α j = c) (h₃ : c + D.α i = d)
  (β : WeightBlocks D Λ a)
local notation "Sc'" => parameterTwist D Sc
local notation "β₃" => elvBlockSucc₃ D i j i Λ h₁ h₂ h₃ β
local notation "hT" => elvBlockTriple_content_eq D i j i Λ h₁ h₂ h₃ β
local notation "C₃" => elvWeightTripleComparison D Sc' cutoff bound i j i Λ h₁ h₂ h₃ β β₃ rfl

/-- The ordered correction in the THREE GIVEN native dots uses ORIGINAL
Sc under the selected C3 chart, at the actual output block. This is the
polynomial transport square, before the native braid-path assembly. -/
theorem elvWeightTriplePolynomial_coordinate
    (M : ELVWeightProduct D Sc' cutoff bound Λ a)
    (w : ContentCategory D Sc' cutoff bound β₃.1) :
    let A := ((elvEFunctor D Sc' cutoff bound i Λ h₁ ⋙ elvEFunctor D Sc' cutoff bound j Λ h₂) ⋙
      (elvInductionComponent D Sc' cutoff bound i Λ h₃ β₃).toFunctor).obj M
    let x₀ : End A := (elvWeightTripleFirstDot D Sc' cutoff bound i j i Λ h₁ h₂ h₃).total M β₃
    let x₁ : End A := (elvWeightTripleMiddleDot D Sc' cutoff bound i j i Λ h₁ h₂ h₃).total M β₃
    let x₂ : End A := (elvWeightTripleLastDot D Sc' cutoff bound i j i Λ h₁ h₂ h₃).total M β₃
    ((moduleIsoLinearEquiv ((C₃).app M) w).conjAlgEquiv k).toAlgHom
      (tripleDotCorrectionPolynomial D Sc i j (x₀.total w) (x₁.total w) (x₂.total w)) =
    tripleDotCorrectionPolynomial D Sc i j
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc' cutoff bound hT hT (firstDot_parity D Sc' i [j,i])) (M β) w)
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc' cutoff bound hT hT (contentTripleDot_one_parity D Sc' i j)) (M β) w)
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc' cutoff bound hT hT (contentTripleDot_two_parity D Sc' i j)) (M β) w) := by
  dsimp only
  apply polynomial_of_coordinates D Sc i j ((C₃).app M)
    ((elvWeightTripleFirstDot D Sc' cutoff bound i j i Λ h₁ h₂ h₃).total M β₃)
    ((elvWeightTripleMiddleDot D Sc' cutoff bound i j i Λ h₁ h₂ h₃).total M β₃)
    ((elvWeightTripleLastDot D Sc' cutoff bound i j i Λ h₁ h₂ h₃).total M β₃) w
  · exact elvWeightTripleDot_first_coordinate D Sc' cutoff bound i j i Λ h₁ h₂ h₃ β M w
  · exact elvWeightTripleDot_middle_coordinate D Sc' cutoff bound i j i Λ h₁ h₂ h₃ β M w
  · exact elvWeightTripleDot_last_coordinate D Sc' cutoff bound i j i Λ h₁ h₂ h₃ β M w

end OddMath.QuiverHecke.ELVOld
