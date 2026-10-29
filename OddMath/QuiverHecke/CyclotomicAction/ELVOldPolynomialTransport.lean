/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldBalancedTensor

/-!
# Transported old ELV polynomial vanishing

The old-polynomial transport and vanishing part of `DeformedGlobalQP.md`
§2 (K). The moving intertwiner chain is the existing affine `moveHom`,
with the full source coefficients mapped into the signed ELV category.
The old polynomial at position two transports to position one at the
output. Its class vanishes, including every ambient continuation. This
does not supply the prefix-crossing identity, QP induction or cancellation.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Transport of the first old polynomial along the entire moving chain.
The sign includes both coefficient parity and dot parity. -/
theorem oldPolynomial_move (i : I) (j : {j : I // D.parity j = 1}) (v : List I) :
    (elvQuotientFunctor D Sc cutoff).map
        (elvDotPolynomial D Sc j (i :: j.1 :: v) 1 (cutoff j.1)) ≫
      (elvQuotientFunctor D Sc cutoff).map
        (sourceCoefficientHom D Sc 1 (moveHom D Sc i [] (j.1 :: v))) =
    sign k ((cutoff j.1 : ZMod 2) * (D.parity i * wordSumParity D (j.1 :: v))) •
      ((elvQuotientFunctor D Sc cutoff).map
          (sourceCoefficientHom D Sc 1 (moveHom D Sc i [] (j.1 :: v))) ≫
        (elvQuotientFunctor D Sc cutoff).map
          (elvDotPolynomial D Sc j ((j.1 :: v) ++ [i]) 0 (cutoff j.1))) := by
  have ht := coefficientDotPolynomial_mem_comp_moveHom D Sc i j.1 v [] [] (cutoff j.1)
    (SKM.SYM.elvMonicCoefficient D k j (cutoff j.1)) (cutoff j.1 : ZMod 2)
    (SKM.SYM.elvMonicCoefficient_mem_parity D j (cutoff j.1))
  have h : elvDotPolynomial D Sc j (i :: j.1 :: v) 1 (cutoff j.1) ≫
      sourceCoefficientHom D Sc 1 (moveHom D Sc i [] (j.1 :: v)) =
      sign k ((cutoff j.1 : ZMod 2) * (D.parity i * wordSumParity D (j.1 :: v))) •
        (sourceCoefficientHom D Sc 1 (moveHom D Sc i [] (j.1 :: v)) ≫
          elvDotPolynomial D Sc j ((j.1 :: v) ++ [i]) 0 (cutoff j.1)) := by
    simpa only [elvDotPolynomial, List.nil_append, List.length_nil, zero_add, add_zero] using ht
  rw [← Functor.map_comp, h, Functor.map_smul, Functor.map_comp]

/-- The transported old ELV polynomial vanishes in the old-only target,
not by imposing a relation on the moving strand. -/
theorem projection_move_oldPolynomial (i : I) (j : {j : I // D.parity j = 1})
    (v w : List I) (h : hom D Sc cutoff ((j.1 :: v) ++ [i]) w) :
    projection D Sc cutoff i (j.1 :: v) w
      ((elvQuotientFunctor D Sc cutoff).map
          (sourceCoefficientHom D Sc 1 (moveHom D Sc i [] (j.1 :: v))) ≫
        (elvQuotientFunctor D Sc cutoff).map
          (elvDotPolynomial D Sc j ((j.1 :: v) ++ [i]) 0 (cutoff j.1)) ≫ h) = 0 := by
  have hz := projection_elvPolynomial D Sc cutoff i j v w
    ((elvQuotientFunctor D Sc cutoff).map
      (sourceCoefficientHom D Sc 1 (moveHom D Sc i [] (j.1 :: v))) ≫ h)
  rw [← Category.assoc, oldPolynomial_move, Linear.smul_comp, map_smul,
    Category.assoc] at hz
  have hh := congrArg
    (fun z => sign k ((cutoff j.1 : ZMod 2) * (D.parity i * wordSumParity D (j.1 :: v))) • z) hz
  simpa only [sign_smul_sign_smul, smul_zero] using hh

end OddMath.QuiverHecke.ELVOld
