import OddMath.QuiverHecke.CyclotomicAction.WeightTripleComparison.WeightDistinctSlideRelations

/-!
# Weight triple comparison

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The original-Sc correction in the selected weight triple coordinates

Brundan--Ellis (1.9), repeated outer colour. The ordered polynomial in the
three literal weight-dot positions is conjugated by the selected C3 chart
to the same polynomial in the three indexed affine generators. The actual
output content is retained; no canonical-content replacement is made.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The mixed braid polynomial on the prescribed weight crossings

Brundan--Ellis (1.9), repeated outer colour: transport both given crossing
paths and the ordered original-parameter dot polynomial through the same
selected triple chart.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem polynomial_from_comparison
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A B : Superfunctor k C (SVec k)} (e : A ≅ B) (x : End A) (y : End B)
    (w : C) (p : Module.End k (A.obj w)) (q : Module.End k (B.obj w))
    (h : x ≫ e.hom = e.hom ≫ y) (hy : y.total w = q)
    (hp : ((moduleIsoLinearEquiv e w).conjAlgEquiv k).toAlgHom p = q) :
    x.total w = p := by
  have ht := congrArg (fun z => z.total w) h
  rw [Superfunctor.comp_total, Superfunctor.comp_total] at ht
  have hc : ((moduleIsoLinearEquiv e w).conjAlgEquiv k).toAlgHom (x.total w) = y.total w := by
    apply LinearMap.ext
    intro v
    change (moduleIsoLinearEquiv e w) (x.total w ((moduleIsoLinearEquiv e w).symm v)) = y.total w v
    have hv := LinearMap.congr_fun ht ((moduleIsoLinearEquiv e w).symm v)
    change (moduleIsoLinearEquiv e w) (x.total w ((moduleIsoLinearEquiv e w).symm v)) =
      y.total w ((moduleIsoLinearEquiv e w) ((moduleIsoLinearEquiv e w).symm v)) at hv
    simpa only [LinearEquiv.apply_symm_apply] using hv
  exact ((moduleIsoLinearEquiv e w).conjAlgEquiv k).injective (hc.trans (hy.trans hp.symm))

private theorem module_total_sub
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (A : Superfunctor k C (SVec k)) (x y : End A) (w : C) :
    (x - y).total w = x.total w - y.total w :=
  (supernaturalTotalLinearMap A A w).map_sub x y

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
local notation "Sc'" => parameterTwist D Sc

section Direct
variable (β : Multiset I) (i j : I) (hij : i ≠ j) (γ : Multiset I)
    (h₀ : β + ([i,j,i] : Multiset I) = γ)
    (h₁ : β + ([i,i,j] : Multiset I) = γ)
    (h₂ : β + ([j,i,i] : Multiset I) = γ)
local notation "c₀" => SuperNatTrans.app (contentInductionTransform D Sc' cutoff bound h₁ h₀
  (contentNormalizedRight_mem D Sc' i i j)) (D.parity i * D.parity j)
local notation "c₁" => SuperNatTrans.app (contentInductionTransform D Sc' cutoff bound h₁ h₁
  (contentNormalizedLeft_mem D Sc' i i j)) (D.parity i * D.parity i)
local notation "c₂" => SuperNatTrans.app (contentInductionTransform D Sc' cutoff bound h₀ h₁
  (contentNormalizedRight_mem D Sc' i j i)) (D.parity j * D.parity i)
local notation "d₀" => SuperNatTrans.app (contentInductionTransform D Sc' cutoff bound h₂ h₀
  (contentNormalizedLeft_mem D Sc' j i i)) (D.parity j * D.parity i)
local notation "d₁" => SuperNatTrans.app (contentInductionTransform D Sc' cutoff bound h₂ h₂
  (contentNormalizedRight_mem D Sc' j i i)) (D.parity i * D.parity i)
local notation "d₂" => SuperNatTrans.app (contentInductionTransform D Sc' cutoff bound h₀ h₂
  (contentNormalizedLeft_mem D Sc' i j i)) (D.parity i * D.parity j)
include hij in
private theorem direct_paths_polynomial
    (M : ContentModules D Sc' cutoff bound β) (w : ContentCategory D Sc' cutoff bound γ) :
    (c₀ M ≫ c₁ M ≫ c₂ M - d₀ M ≫ d₁ M ≫ d₂ M).total w =
      tripleDotCorrectionPolynomial D Sc i j
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (firstDot_parity D Sc' i [j,i])) M w)
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (contentTripleDot_one_parity D Sc' i j)) M w)
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (contentTripleDot_two_parity D Sc' i j)) M w) := by
  rw [module_total_sub, Superfunctor.comp_total, Superfunctor.comp_total,
    Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [contentInductionTransform_total]
  change (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₁ (contentNormalizedRight_mem D Sc' i j i)) M w).comp ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc' cutoff bound h₁ h₁ (contentNormalizedLeft_mem D Sc' i i j)) M w).comp (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc' cutoff bound h₁ h₀ (contentNormalizedRight_mem D Sc' i i j)) M w)) -
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₂ (contentNormalizedLeft_mem D Sc' i j i)) M w).comp ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc' cutoff bound h₂ h₂ (contentNormalizedRight_mem D Sc' j i i)) M w).comp (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc' cutoff bound h₂ h₀ (contentNormalizedLeft_mem D Sc' j i i)) M w)) = _
  exact contentNormalizedMixedBraid_at_polynomial D Sc cutoff bound β i j hij γ h₀ h₁ h₂ M w
end Direct

variable (i j : I) (Λ : X) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d) (β : WeightBlocks D Λ a)
local notation "β₁" => blockSucc D Λ i hab β
local notation "δ" => blockSucc₂ D j i Λ hab hbc β
local notation "ε" => elvBlockSucc₃ D i j i Λ hab hbc hcd β
local notation "hA" => blockSucc₂_swap D i j Λ hbc hcd hbe hed (β := β₁) rfl
local notation "hB" => elvBlockSucc₃_eq_of_pair D i i j Λ haf hfc hcd β δ ε
  (blockSucc₂_swap D j i Λ hab hbc haf hfc rfl) rfl
local notation "h₀" => elvBlockTriple_content_eq D i j i Λ hab hbc hcd β
local notation "h₁" => elvWeightTriple_content_eq D j i i Λ hab hbe hed β ε hA
local notation "h₂" => elvWeightTriple_content_eq D i i j Λ haf hfc hcd β ε hB
local notation "C₀" => elvWeightTripleComparison D Sc' cutoff bound i j i Λ hab hbc hcd β ε rfl
local notation "a₀" => elvWeightSuffixCross D Sc' cutoff bound i j i Λ hab hbc hcd hbe hed
local notation "a₁" => elvWeightPrefixCross D Sc' cutoff bound j i i Λ hab hbe hab hbe hed
local notation "a₂" => elvWeightSuffixCross D Sc' cutoff bound j i i Λ hab hbe hed hbc hcd
local notation "b₀" => elvWeightPrefixCross D Sc' cutoff bound i j i Λ hab hbc haf hfc hcd
local notation "b₁" => elvWeightSuffixCross D Sc' cutoff bound i i j Λ haf hfc hcd hfc hcd
local notation "b₂" => elvWeightPrefixCross D Sc' cutoff bound i i j Λ haf hfc hab hbc hcd
local notation "c₀" => SuperNatTrans.app (contentInductionTransform D Sc' cutoff bound h₁ h₀
  (contentNormalizedRight_mem D Sc' i i j)) (D.parity i * D.parity j)
local notation "c₁" => SuperNatTrans.app (contentInductionTransform D Sc' cutoff bound h₁ h₁
  (contentNormalizedLeft_mem D Sc' i i j)) (D.parity i * D.parity i)
local notation "c₂" => SuperNatTrans.app (contentInductionTransform D Sc' cutoff bound h₀ h₁
  (contentNormalizedRight_mem D Sc' i j i)) (D.parity j * D.parity i)
local notation "d₀" => SuperNatTrans.app (contentInductionTransform D Sc' cutoff bound h₂ h₀
  (contentNormalizedLeft_mem D Sc' j i i)) (D.parity j * D.parity i)
local notation "d₁" => SuperNatTrans.app (contentInductionTransform D Sc' cutoff bound h₂ h₂
  (contentNormalizedRight_mem D Sc' j i i)) (D.parity i * D.parity i)
local notation "d₂" => SuperNatTrans.app (contentInductionTransform D Sc' cutoff bound h₀ h₂
  (contentNormalizedLeft_mem D Sc' i j i)) (D.parity i * D.parity j)

/-- The prescribed six weight crossings have the original-Sc correction
on every vector at each supported output block. -/
theorem elvWeightMixedBraid_polynomial_coordinate (hij : i ≠ j)
    (M : ELVWeightProduct D Sc' cutoff bound Λ a)
    (w : ContentCategory D Sc' cutoff bound ε.1) :
    let A := ((elvEFunctor D Sc' cutoff bound i Λ hab ⋙ elvEFunctor D Sc' cutoff bound j Λ hbc) ⋙
      (elvInductionComponent D Sc' cutoff bound i Λ hcd ε).toFunctor).obj M
    let x₀ : End A := (elvWeightTripleFirstDot D Sc' cutoff bound i j i Λ hab hbc hcd).total M ε
    let x₁ : End A := (elvWeightTripleMiddleDot D Sc' cutoff bound i j i Λ hab hbc hcd).total M ε
    let x₂ : End A := (elvWeightTripleLastDot D Sc' cutoff bound i j i Λ hab hbc hcd).total M ε
    ((a₀).total M ε ≫ (a₁).total M ε ≫ (a₂).total M ε -
      (b₀).total M ε ≫ (b₁).total M ε ≫ (b₂).total M ε).total w =
      tripleDotCorrectionPolynomial (R := Module.End k (A.obj w)) D Sc i j (x₀.total w) (x₁.total w) (x₂.total w) := by
  dsimp only
  apply polynomial_from_comparison ((C₀).app M)
    ((a₀).total M ε ≫ (a₁).total M ε ≫ (a₂).total M ε -
      (b₀).total M ε ≫ (b₁).total M ε ≫ (b₂).total M ε)
    (c₀ (M β) ≫ c₁ (M β) ≫ c₂ (M β) - d₀ (M β) ≫ d₁ (M β) ≫ d₂ (M β)) w _ _
  · simpa only [Iso.app_hom] using
      elvWeightMixedPaths_comparison D Sc' cutoff bound i j Λ hab haf hbc hbe hfc hcd hed β M
  · exact direct_paths_polynomial D Sc cutoff bound β.1 i j hij ε.1 h₀ h₁ h₂ (M β) w
  · exact elvWeightTriplePolynomial_coordinate D Sc cutoff bound i j Λ hab hbc hcd β M w

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The corrected braid on the chosen output modules

Brundan--Ellis (1.9). Recover equality of whole output-module maps from
the checked prescribed crossing and dot operators, before family evaluation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem module_polynomial_of_operators
    {k C I X : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C] [AddCommGroup X]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (i j : I)
    (A : Superfunctor k C (SVec k)) (l x₀ x₁ x₂ : End A)
    (h : ∀ w, l.total w = tripleDotCorrectionPolynomial (R := Module.End k (A.obj w))
      D Sc i j (x₀.total w) (x₁.total w) (x₂.total w)) :
    l = tripleDotCorrectionPolynomial (R := End A) D Sc i j x₀ x₁ x₂ := by
  apply FiniteSupermodule.hom_ext_total
  intro w
  let ev := (svecEndEvaluation (A.obj w)).comp (supernaturalEndEvaluation A w)
  have hp := tripleDotCorrectionPolynomial_map D Sc ev i j x₀ x₁ x₂
  exact (h w).trans hp.symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d) (β : WeightBlocks D Λ a)
local notation "Sc'" => parameterTwist D Sc
local notation "ε" => elvBlockSucc₃ D i j i Λ hab hbc hcd β
local notation "a₀" => elvWeightSuffixCross D Sc' cutoff bound i j i Λ hab hbc hcd hbe hed
local notation "a₁" => elvWeightPrefixCross D Sc' cutoff bound j i i Λ hab hbe hab hbe hed
local notation "a₂" => elvWeightSuffixCross D Sc' cutoff bound j i i Λ hab hbe hed hbc hcd
local notation "b₀" => elvWeightPrefixCross D Sc' cutoff bound i j i Λ hab hbc haf hfc hcd
local notation "b₁" => elvWeightSuffixCross D Sc' cutoff bound i i j Λ haf hfc hcd hfc hcd
local notation "b₂" => elvWeightPrefixCross D Sc' cutoff bound i i j Λ haf hfc hab hbc hcd

/-- Equality of the prescribed module maps at a supported output block,
retaining the canonical ordinary triple-coordinate object. -/
theorem elvWeightMixedBraid_module_polynomial (hij : i ≠ j)
    (M : ELVWeightProduct D Sc' cutoff bound Λ a) :
    let A := ((elvEFunctor D Sc' cutoff bound i Λ hab ⋙ elvEFunctor D Sc' cutoff bound j Λ hbc) ⋙
      (elvInductionComponent D Sc' cutoff bound i Λ hcd ε).toFunctor).obj M
    let x₀ : End A := (elvWeightTripleFirstDot D Sc' cutoff bound i j i Λ hab hbc hcd).total M ε
    let x₁ : End A := (elvWeightTripleMiddleDot D Sc' cutoff bound i j i Λ hab hbc hcd).total M ε
    let x₂ : End A := (elvWeightTripleLastDot D Sc' cutoff bound i j i Λ hab hbc hcd).total M ε
    (a₀).total M ε ≫ (a₁).total M ε ≫ (a₂).total M ε -
      (b₀).total M ε ≫ (b₁).total M ε ≫ (b₂).total M ε =
      tripleDotCorrectionPolynomial (R := End A) D Sc i j x₀ x₁ x₂ := by
  dsimp only
  apply module_polynomial_of_operators D Sc i j _ _ _ _ _
  intro w
  exact elvWeightMixedBraid_polynomial_coordinate D Sc cutoff bound i j Λ
    hab haf hbc hbe hfc hcd hed β hij M w

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The corrected braid on the prescribed weight action

Brundan--Ellis (1.9), repeated outer colour. The given six crossings and
three positioned dots satisfy the ordered original-parameter correction
as supernatural maps, including every absent predecessor sector.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
section Evaluation
variable {k : Type u} [CommRing k]
    {C : Type*} [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    {J : Type u} {A : J → Type u}
    [∀ j, Category.{u} (A j)] [∀ j, Preadditive (A j)]
    [∀ j, Linear k (A j)] [∀ j, Supercategory k (A j)]
    {F G H : Superfunctor k C (∀ j, Superfunctor k (A j) (SVec k))}
private theorem family_correction_of_module_components
    {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (i j : I) (a₀ : F ⟶ G) (a₁ : End G) (a₂ : G ⟶ F)
    (b₀ : F ⟶ H) (b₁ : End H) (b₂ : H ⟶ F) (x₀ x₁ x₂ : End F)
    (h : ∀ M t,
      a₀.total M t ≫ a₁.total M t ≫ a₂.total M t -
        b₀.total M t ≫ b₁.total M t ≫ b₂.total M t =
      tripleDotCorrectionPolynomial (R := End (F.obj M t)) D Sc i j
        (x₀.total M t) (x₁.total M t) (x₂.total M t)) :
    a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
      tripleDotCorrectionPolynomial (R := End F) D Sc i j x₀ x₁ x₂ := by
  apply supernatural_hom_ext_total
  intro M
  funext t
  let ev := (piEndEvaluation (F.obj M) t).comp (supernaturalEndEvaluation F M)
  have hp := tripleDotCorrectionPolynomial_map D Sc ev i j x₀ x₁ x₂
  have he : (a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂).total M t =
      a₀.total M t ≫ a₁.total M t ≫ a₂.total M t -
        b₀.total M t ≫ b₁.total M t ≫ b₂.total M t := by
    have hs := (supernaturalTotalLinearMap F F M).map_sub
      (a₀ ≫ a₁ ≫ a₂) (b₀ ≫ b₁ ≫ b₂)
    change (a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂).total M =
      (a₀ ≫ a₁ ≫ a₂).total M - (b₀ ≫ b₁ ≫ b₂).total M at hs
    rw [Superfunctor.comp_total, Superfunctor.comp_total,
      Superfunctor.comp_total, Superfunctor.comp_total] at hs
    exact congrFun hs t
  exact he.trans ((h M t).trans hp.symm)
end Evaluation

private theorem pi_component_polynomial
    {k I X : Type u} {C₀ C₁ C₂ : Type*} [CommRing k] [AddCommGroup X]
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Preadditive C₂] [Linear k C₂] [Supercategory k C₂]
    {J : Type u} {A : J → Type u}
    [∀ j, Category.{u} (A j)] [∀ j, Preadditive (A j)]
    [∀ j, Linear k (A j)] [∀ j, Supercategory k (A j)]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (i j : I)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (K : ∀ t, Superfunctor k C₂ (Superfunctor k (A t) (SVec k)))
    (M : C₀) (t : J)
    (l x₀ x₁ x₂ : End (((F ⋙ G ⋙ Functor.pi' (fun t => (K t).toFunctor)).obj M) t))
    (h : @Eq (End (((F ⋙ G ⋙ Functor.pi' (fun t => (K t).toFunctor)).obj M) t))
      l (tripleDotCorrectionPolynomial (R := End (((F ⋙ G) ⋙ (K t).toFunctor).obj M))
        D Sc i j x₀ x₁ x₂)) :
    @Eq (End (((F ⋙ G ⋙ Functor.pi' (fun t => (K t).toFunctor)).obj M) t))
      l (tripleDotCorrectionPolynomial
        (R := End (((F ⋙ G ⋙ Functor.pi' (fun t => (K t).toFunctor)).obj M) t))
        D Sc i j x₀ x₁ x₂) := by
  exact h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)
local notation "Sc'" => parameterTwist D Sc
local notation "F₀" => elvE D Sc' cutoff bound i Λ hab ≫ elvE D Sc' cutoff bound j Λ hbc ≫ elvE D Sc' cutoff bound i Λ hcd
local notation "a₀" => elvWeightSuffixCross D Sc' cutoff bound i j i Λ hab hbc hcd hbe hed
local notation "a₁" => elvWeightPrefixCross D Sc' cutoff bound j i i Λ hab hbe hab hbe hed
local notation "a₂" => elvWeightSuffixCross D Sc' cutoff bound j i i Λ hab hbe hed hbc hcd
local notation "b₀" => elvWeightPrefixCross D Sc' cutoff bound i j i Λ hab hbc haf hfc hcd
local notation "b₁" => elvWeightSuffixCross D Sc' cutoff bound i i j Λ haf hfc hcd hfc hcd
local notation "b₂" => elvWeightPrefixCross D Sc' cutoff bound i i j Λ haf hfc hab hbc hcd
local notation "x₀" => elvWeightTripleFirstDot D Sc' cutoff bound i j i Λ hab hbc hcd
local notation "x₁" => elvWeightTripleMiddleDot D Sc' cutoff bound i j i Λ hab hbc hcd
local notation "x₂" => elvWeightTripleLastDot D Sc' cutoff bound i j i Λ hab hbc hcd

/-- The corrected braid for the literal given weight crossings and dots.
The coefficients are Sc while the acting scalar family is parameterTwist Sc. -/
theorem elvActionCross_mixedBraid (hij : i ≠ j) :
    a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
      tripleDotCorrectionPolynomial (R := End F₀) D Sc i j x₀ x₁ x₂ := by
  apply family_correction_of_module_components D Sc i j a₀ a₁ a₂ b₀ b₁ b₂ x₀ x₁ x₂
  intro M ε
  by_cases hs : ∃ β, elvBlockSucc₃ D i j i Λ hab hbc hcd β = ε
  · obtain ⟨β, rfl⟩ := hs
    apply pi_component_polynomial D Sc i j
      (elvEFunctor D Sc' cutoff bound i Λ hab)
      (elvEFunctor D Sc' cutoff bound j Λ hbc)
      (elvInductionComponent D Sc' cutoff bound i Λ hcd) M _ _ _ _ _
    have h := elvWeightMixedBraid_module_polynomial D Sc cutoff bound i j Λ
      hab haf hbc hbe hfc hcd hed β hij M
    set_option backward.dsimp.instances true in
      dsimp only at h ⊢
    convert h using 1
  · have hz := elvEFunctor_comp₃_isZero D Sc' cutoff bound i j i Λ hab hbc hcd ε hs M
    exact hz.eq_of_src _ _

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The dotted mixed braid field of the selected weight data

Brundan--Ellis (1.9), repeated outer colour. This is exactly the
RouquierMulticolour.braidEq field for the independently selected maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)
local notation "Sc'" => parameterTwist D Sc
local notation "E₁" => elvE D Sc' cutoff bound i Λ hab
local notation "E₂" => elvE D Sc' cutoff bound j Λ hbc
local notation "E₃" => elvE D Sc' cutoff bound i Λ hcd

/-- The exact repeated-outer dotted braid field, with original Sc and
all prescribed crossings, associators and rouquierPower terms. -/
theorem elvRouquierData_braidEq (hij : i ≠ j) :
    rouquierMixedBraidEquation D Sc (elvRouquierData D Sc' cutoff bound Λ)
      i j hab haf hbc hbe hfc hcd hed := by
  apply rouquierMixedBraidEquation_of_polynomial
  have h := elvActionCross_mixedBraid D Sc cutoff bound i j Λ
    hab haf hbc hbe hfc hcd hed hij
  simp only [elvRouquierData, elvWeightPrefixCross, elvWeightSuffixCross] at h ⊢
  convert h using 1

end OddMath.QuiverHecke.ELV
end

end
