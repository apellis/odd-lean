/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVParameterUntwist

/-! # The original-parameter quadratic on common-content induction tensors

`DeformedActionAssembly.md` §6: the two actual induction crossings, over
`parameterTwist Sc`, compose to the ordered signed evaluation with the
specified `Sc`. The source is the actual two-word affine relation, with no
finite-colour assumption. This does not yet identify powers of the dotted
module operators with that ordered evaluation or assemble weight functors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem crossTwo_comp_pairQuad {i j : I} (hij : i ≠ j) :
    crossTwo D Sc i j ≫ crossTwo D Sc j i =
      pairQuadPoly D Sc i j (dotE D Sc [i,j] 0) (dotE D Sc [i,j] 1) := by
  unfold crossTwo
  rw [cl_comp]
  unfold pairQuadPoly
  split_ifs with hd
  · exact cross_cross_ne_zero D Sc [] [] hij hd _
  · exact cross_cross_ne D Sc [] [] hij hd _

/-- Actual two-word source quadratic, with the parameter involution cancelled. -/
theorem crossTwo_comp_parameterUntwist {i j : I} (hij : i ≠ j) :
    sign k (D.parity i * D.parity j) •
      (crossTwo D (parameterTwist D Sc) i j ≫ crossTwo D (parameterTwist D Sc) j i) =
      elvSignedPairQuadEval D Sc (R := End ((pres D (parameterTwist D Sc)).obj (ob D [i,j]))) i j
        (dotE D (parameterTwist D Sc) [i,j] 0) (dotE D (parameterTwist D Sc) [i,j] 1) := by
  rw [crossTwo_comp_pairQuad D _ hij, sign_eq_zsign]
  exact pairQuadPoly_parameterTwist_eval D Sc
    (R := End ((pres D (parameterTwist D Sc)).obj (ob D [i,j]))) hij _ _

@[simp] theorem contentAppendToComponent_smul {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (r : k) (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ))
    (v : ContentCategory D Sc cutoff N β) :
    contentAppendToComponent D Sc cutoff N hσ hτ (r • a) v =
      r • contentAppendToComponent D Sc cutoff N hσ hτ a v := by
  simp [contentAppendToComponent, truncatedAppendComponent, appendComponent,
    MonoidalSupercategory.whiskerLeft_smul (R := k), TensorProduct.tmul_smul]

/-- Two crossed append maps on the same content endpoint, evaluated on an actual
balanced induction tensor. The resulting ordered polynomial has original Sc. -/
theorem contentInduction_quadratic_tensor (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (v : ContentCategory D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I)))
    (h : (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl).obj v ⟶ w)
    (m : M.obj v) :
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N rfl
        (content_pair_swap β i j) (contentCrossAffine_mem D (parameterTwist D Sc) i j)) M w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N
          (content_pair_swap β i j) rfl (contentCrossAffine_mem D (parameterTwist D Sc) j i)) M w
        (BalancedInduction.tensor
          (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v h m)) =
    BalancedInduction.tensor
      (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v
      (contentAppendToComponent D (parameterTwist D Sc) cutoff N rfl rfl
        (elvSignedPairQuadEval D Sc (R := End ((pres D (parameterTwist D Sc)).obj (ob D [i,j]))) i j
          (dotE D (parameterTwist D Sc) [i,j] 0)
          (dotE D (parameterTwist D Sc) [i,j] 1)) v ≫ h) m := by
  let p := D.parity i * D.parity j
  have hp : D.parity j * D.parity i = p := mul_comm _ _
  have hpp : p + p = 0 := by
    rcases parity_eq_zero_or_one p with h | h <;> simp [h]
  have hsq : p * p = p := by
    rcases parity_eq_zero_or_one p with h | h <;> simp [h]
  rw [BalancedInduction.transformLinear_tensor, BalancedInduction.transformLinear_tensor,
    twist_comp]
  rw [twist_of_mem _ ((contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N
    (content_pair_swap β i j) rfl (contentCrossAffine_mem D (parameterTwist D Sc) j i)).mem v)]
  rw [← twist_add, hp, hpp, twist_zero, hsq, Linear.smul_comp, Linear.comp_smul,
    ← Category.assoc,
    contentAppendToComponent_comp D (parameterTwist D Sc) cutoff N rfl
      (content_pair_swap β i j) rfl _ (contentCrossAffine_mem D (parameterTwist D Sc) j i),
    ← Linear.smul_comp, ← contentAppendToComponent_smul,
    contentCrossAffine_distinct D _ i j hij, contentCrossAffine_distinct D _ j i hij.symm,
    crossTwo_comp_parameterUntwist D Sc hij]

end OddMath.QuiverHecke.ELVOld
