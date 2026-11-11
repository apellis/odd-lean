/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairDotCoordinates

/-! # The supported quadratic in independent weight dots

DeformedActionAssembly §6 (9): normalize the two source whiskerings and
transport the original-parameter ordered polynomial through the selected
pair comparison, retaining the independently assembled weight operators.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- The original parameter polynomial in operator order; the first-position
power acts before the second-position power. No operators are commuted. -/
def orderedPairOperatorPolynomial {R : Type*} [Ring R] [Algebra k R]
    (i j : I) (A B : R) : R :=
  if D.d i j = 0 then (Sc.t i j : k) • 1 else
    ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
      Sc.s i j r s • (B ^ s * A ^ r) +
    ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i)

theorem orderedPairOperatorPolynomial_map
    {R S : Type*} [Ring R] [Algebra k R] [Ring S] [Algebra k S]
    (e : R ≃ₐ[k] S) (i j : I) (A B : R) :
    e (orderedPairOperatorPolynomial D Sc i j A B) =
      orderedPairOperatorPolynomial D Sc i j (e A) (e B) := by
  unfold orderedPairOperatorPolynomial
  split_ifs <;> simp only [map_smul, map_one, map_add, map_sum, map_mul, map_pow]

theorem ModuleCoordinateSquare_conj
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A E : Superfunctor k C (SVec k)} {e : A ≅ E}
    {x : A ⟶ A} {w : C} {z : E.obj w →ₗ[k] E.obj w}
    (h : ModuleCoordinateSquare e x w z) :
    (moduleIsoLinearEquiv e w).symm.conjAlgEquiv k z = x.total w := by
  apply LinearMap.ext
  intro v
  apply (moduleIsoLinearEquiv e w).injective
  change (moduleIsoLinearEquiv e w)
      ((moduleIsoLinearEquiv e w).symm (z ((moduleIsoLinearEquiv e w) v))) =
    (moduleIsoLinearEquiv e w) (x.total w v)
  rw [LinearEquiv.apply_symm_apply]
  exact (ModuleCoordinateSquare_apply h v).symm

variable (cutoff : I → ℕ) (bound : ℕ)

private theorem induction_transform_source_congr
    {β γ : Multiset I} {σ : List I} (h : β + (σ : Multiset I) = γ)
    {p : ZMod 2} {a b : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ p)
    (hab : a = b) (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h ha) M w =
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h hb) M w := by
  cases hab
  rfl

theorem contentInduction_inner_positioned (β : Multiset I) (i j : I)
    (γ : Multiset I) (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h
        (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [j]))
          (firstDot_parity D Sc i []))) M w =
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h
        (firstDot_parity D Sc i [j])) M w :=
  induction_transform_source_congr D Sc cutoff bound h
    (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [j]))
      (firstDot_parity D Sc i [])) (firstDot_parity D Sc i [j])
    (dotE_whiskerRight D Sc [i] [j] 0 (by simp)) M w

theorem contentInduction_outer_positioned (β : Multiset I) (i j : I)
    (γ : Multiset I) (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h
        (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
          (firstDot_parity D Sc j []))) M w =
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound h h
        (contentPairDot_one_parity D Sc i j)) M w :=
  induction_transform_source_congr D Sc cutoff bound h
    (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
      (firstDot_parity D Sc j [])) (contentPairDot_one_parity D Sc i j)
    (whiskerLeft_letter_dotE D Sc i [j] 0) M w

theorem contentInductionPairPolynomialTo_eq_ordered (β : Multiset I) (i j : I)
    (γ : Multiset I) (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D (parameterTwist D Sc) cutoff bound β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff bound γ) :
    contentInductionPairPolynomialTo D Sc cutoff bound β i j γ h M w =
    orderedPairOperatorPolynomial D Sc i j
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff bound h h
          (firstDot_parity D (parameterTwist D Sc) i [j])) M w)
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff bound h h
          (contentPairDot_one_parity D (parameterTwist D Sc) i j)) M w) := rfl

variable (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

/-- The prescribed supported weight crossing square is the original
parameter polynomial in the independently defined inner and outer dots.
The source word is `[j,i]`, so the polynomial uses that same order. -/
theorem elvWeightCrossVia_quadratic_independent (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀)
    (M : ELVWeightProduct D (parameterTwist D Sc) cutoff bound Λ x₀)
    (w : ContentCategory D (parameterTwist D Sc) cutoff bound
      (blockSucc₂ D i j Λ h₁ h₂ β).1) :
    let ε := blockSucc₂ D i j Λ h₁ h₂ β
    let hε' := blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ (β := β) (ε := ε) rfl
    let x := (elvInductionComponent D (parameterTwist D Sc) cutoff bound i Λ h₂ ε).map
      ((elvWeightDot D (parameterTwist D Sc) cutoff bound j Λ h₁).app (D.parity j) M)
    let y := elvWeightDotComponent D (parameterTwist D Sc) cutoff bound i Λ h₂ (D.parity i)
      ((elvEFunctor D (parameterTwist D Sc) cutoff bound j Λ h₁).obj M) ε
    (((elvWeightCrossVia D (parameterTwist D Sc) cutoff bound
        j i Λ h₃ h₄ h₁ h₂ β ε hε').app
        (D.parity j * D.parity i) M).total w).comp
      (((elvWeightCrossVia D (parameterTwist D Sc) cutoff bound
        i j Λ h₁ h₂ h₃ h₄ β ε rfl).app
        (D.parity i * D.parity j) M).total w) =
      orderedPairOperatorPolynomial (R := Module.End k _) D Sc j i (x.total w) (y.total w) := by
  dsimp only
  let ε := blockSucc₂ D i j Λ h₁ h₂ β
  let hs := elvWeightPair_content_eq D i j Λ h₁ h₂ β ε rfl
  let e := moduleIsoLinearEquiv
    ((elvWeightPairComparison D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ β ε rfl).app M) w
  let A := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff bound hs hs
      (firstDot_parity D (parameterTwist D Sc) j [i])) (M β) w
  let B := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff bound hs hs
      (contentPairDot_one_parity D (parameterTwist D Sc) j i)) (M β) w
  have hi := elvWeightPairComparison_inner_total D (parameterTwist D Sc) cutoff bound
    i j Λ h₁ h₂ β M w
  rw [contentInduction_inner_positioned] at hi
  have ho := elvWeightPairComparison_outer_total D (parameterTwist D Sc) cutoff bound
    i j Λ h₁ h₂ β M w
  rw [contentInduction_outer_positioned] at ho
  have hx : e.symm.conjAlgEquiv k A =
      (((elvInductionComponent D (parameterTwist D Sc) cutoff bound i Λ h₂ ε).map
        ((elvWeightDot D (parameterTwist D Sc) cutoff bound j Λ h₁).app
          (D.parity j) M)).total w) := ModuleCoordinateSquare_conj hi
  have hy : e.symm.conjAlgEquiv k B =
      (elvWeightDotComponent D (parameterTwist D Sc) cutoff bound i Λ h₂ (D.parity i)
        ((elvEFunctor D (parameterTwist D Sc) cutoff bound j Λ h₁).obj M) ε).total w :=
    ModuleCoordinateSquare_conj ho
  have hq := elvWeightCrossVia_quadratic_total D Sc cutoff bound i j Λ
    h₁ h₂ h₃ h₄ hij β ε rfl M w
  dsimp only at hq
  rw [contentInductionPairPolynomialTo_eq_ordered] at hq
  have hp := orderedPairOperatorPolynomial_map D Sc (e.symm.conjAlgEquiv k) j i A B
  rw [hx, hy] at hp
  exact hq.trans hp

end OddMath.QuiverHecke.ELVOld
