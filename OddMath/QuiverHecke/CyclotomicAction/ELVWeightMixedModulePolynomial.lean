import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedPolynomial

/-! # The corrected braid on the chosen output modules

Brundan--Ellis (1.9). Recover equality of whole output-module maps from
the checked prescribed crossing and dot operators, before family evaluation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
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

end OddMath.QuiverHecke.ELVOld
