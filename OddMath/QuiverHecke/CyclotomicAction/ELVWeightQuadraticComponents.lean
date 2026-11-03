/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightQuadratic

/-! # Quadratic components on every original weight block

DeformedActionAssembly §6 (9): the independently assembled global
crossings have the original-parameter quadratic in the actual weight dots,
including the absent-double-predecessor branch.
-/

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u

/-- A zero supermodule has zero value at every object, before specializing
any induction coends. -/
theorem moduleValue_subsingleton_of_isZero
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Superfunctor k C (SVec k)} (hA : Limits.IsZero A) (w : C) :
    Subsingleton (A.obj w) := by
  have hh := congrArg (fun f : A ⟶ A => f.total w)
    (hA.eq_of_src (𝟙 A) 0)
  change (LinearMap.id : A.obj w →ₗ[k] A.obj w) + 0 = 0 + 0 at hh
  have hv (v : A.obj w) : v = 0 := by
    have h := congrArg (fun f : A.obj w →ₗ[k] A.obj w => f v) hh
    simpa only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.zero_apply, add_zero] using h
  exact ⟨fun v z => (hv v).trans (hv z).symm⟩

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

/-- The global crossing components obey the original-Sc quadratic in the
independently given inner and outer weight dots at every output block.
No support or predecessor hypothesis is added. -/
theorem elvWeightCrossComponent_quadratic_total (hij : i ≠ j)
    (M : ELVWeightProduct D (parameterTwist D Sc) cutoff bound Λ x₀)
    (ε : WeightBlocks D Λ x₃)
    (w : ContentCategory D (parameterTwist D Sc) cutoff bound ε.1) :
    let x := (elvInductionComponent D (parameterTwist D Sc) cutoff bound i Λ h₂ ε).map
      ((elvWeightDot D (parameterTwist D Sc) cutoff bound j Λ h₁).app (D.parity j) M)
    let y := elvWeightDotComponent D (parameterTwist D Sc) cutoff bound i Λ h₂ (D.parity i)
      ((elvEFunctor D (parameterTwist D Sc) cutoff bound j Λ h₁).obj M) ε
    ((elvWeightCrossComponent D (parameterTwist D Sc) cutoff bound j i Λ h₃ h₄ h₁ h₂
        (D.parity j * D.parity i) M ε).total w).comp
      ((elvWeightCrossComponent D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ h₃ h₄
        (D.parity i * D.parity j) M ε).total w) =
      orderedPairOperatorPolynomial (R := Module.End k _) D Sc j i (x.total w) (y.total w) := by
  dsimp only
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    rw [elvWeightCrossComponent_of D (parameterTwist D Sc) cutoff bound j i Λ h₃ h₄ h₁ h₂
      (D.parity j * D.parity i) M β _ (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ rfl)]
    rw [elvWeightCrossComponent_of D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ h₃ h₄
      (D.parity i * D.parity j) M β _ rfl]
    exact elvWeightCrossVia_quadratic_independent D Sc cutoff bound i j Λ
      h₁ h₂ h₃ h₄ hij β M w
  · let := moduleValue_subsingleton_of_isZero
      (elvEFunctor_comp₂_isZero D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ ε hε M) w
    apply LinearMap.ext
    intro v
    exact Subsingleton.elim _ _

end OddMath.QuiverHecke.ELVOld
