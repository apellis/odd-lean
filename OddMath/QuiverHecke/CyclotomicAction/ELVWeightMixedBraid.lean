import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedModulePolynomial

/-! # The corrected braid on the prescribed weight action

Brundan--Ellis (1.9), repeated outer colour. The given six crossings and
three positioned dots satisfy the ordered original-parameter correction
as supernatural maps, including every absent predecessor sector.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
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

end OddMath.QuiverHecke.ELVOld
