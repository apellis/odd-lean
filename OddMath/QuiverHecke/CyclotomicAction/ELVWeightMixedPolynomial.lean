import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedPaths
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTriplePolynomialComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentNormalizedCorrection
import OddMath.QuiverHecke.CyclotomicAction.ELVEndEvaluation

/-! # The mixed braid polynomial on the prescribed weight crossings

Brundan--Ellis (1.9), repeated outer colour: transport both given crossing
paths and the ordered original-parameter dot polynomial through the same
selected triple chart.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
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

end OddMath.QuiverHecke.ELVOld
