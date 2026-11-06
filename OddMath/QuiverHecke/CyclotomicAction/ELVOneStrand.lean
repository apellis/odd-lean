/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldGrading
import OddMath.QuiverHecke.CyclotomicAbsentColour

/-!
# Full-coefficient one-strand old ELV spanning

The one-strand affine dot basis and the actual monic old relation give spanning
by dot powers strictly below the cutoff, with coefficients in the full ELV
coefficient algebra. This is not an upper-support assertion for that algebra.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Coefficients of the actual old relation, with its normalized left order. -/
def singleCoefficient (i : I) (j : Fin (cutoff i + 1)) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff
    (if h : D.parity i = 1 then SKM.SYM.elvMonicCoefficient D k ⟨i, h⟩ (cutoff i) j
     else SKM.SYM.evenMonicCoefficient D k i (cutoff i) j)

@[simp] theorem singleCoefficient_top (i : I) :
    singleCoefficient (k := k) D cutoff i (Fin.last (cutoff i)) = 1 := by
  unfold singleCoefficient
  split_ifs <;> simp [Fin.last]

def singleTerm (i : I) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (n : ℕ) : hom D Sc cutoff [i] [i] := a ⊗ₜ[k] (dotE D Sc [i] 0 ^ n : End _)

/-- Actual coefficient times dot-power classes in the old quotient. -/
def singleClass (i : I) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (n : ℕ) : Old D Sc cutoff [i] [i] :=
  (ideal D Sc cutoff [i] [i]).mkQ (a ⊗ₜ[k] (dotE D Sc [i] 0 ^ n : End _))

theorem single_relation (i : I) :
    relation D Sc cutoff i [] = ∑ j : Fin (cutoff i + 1),
      singleTerm D Sc cutoff i (singleCoefficient D cutoff i j) j.val := by
  unfold relation singleCoefficient singleTerm
  dsimp only [elvQuotientFunctor]
  split_ifs with h
  · rw [← elvDotPolynomial_first]
    simp only [elvDotPolynomial, coefficientDotPolynomial, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact elvQuotientMap_source D Sc cutoff _ _
  · unfold evenCyclotomic deformedCyclotomic
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show firstDotPower D Sc [i] j.val = dotE D Sc [i] 0 ^ j.val by
      simp only [dotE_pow, firstDotPower, List.map_replicate]]
    exact elvQuotientMap_source D Sc cutoff _ _

private theorem single_precomp (i : I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m n : ℕ) :
    singleTerm D Sc cutoff i 1 m ≫ singleTerm D Sc cutoff i a n =
      singleTerm D Sc cutoff i a (n + m) := by
  change BoxProd.tmulHom (X := obj D Sc cutoff [i]) (Y := obj D Sc cutoff [i])
    (𝟙 _) (dotE D Sc [i] 0 ^ m) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff [i]) (Y := obj D Sc cutoff [i])
      a (dotE D Sc [i] 0 ^ n) = _
  dsimp only [obj, elvQuotientObj, coefficientObj]
  rw [BoxProd.tmulHom_comp_tmulHom_eq]
  simp only [proj_id, ↓reduceIte, one_ne_zero, Category.id_comp, Limits.zero_comp,
    BoxProd.tmulHom_def, TensorProduct.zero_tmul]
  change a ⊗ₜ[k] ((dotE D Sc [i] 0 ^ n) * (dotE D Sc [i] 0 ^ m)) = _
  rw [← pow_add]
  rfl

private theorem single_postcomp (i : I)
    (a b : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (n : ℕ) :
    singleTerm D Sc cutoff i b n ≫ singleTerm D Sc cutoff i a 0 =
      singleTerm D Sc cutoff i (a * b) n := by
  change BoxProd.tmulHom (X := obj D Sc cutoff [i]) (Y := obj D Sc cutoff [i])
    b (dotE D Sc [i] 0 ^ n) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff [i]) (Y := obj D Sc cutoff [i]) a (𝟙 _) = _
  dsimp only [obj, elvQuotientObj, coefficientObj]
  rw [BoxProd.tmulHom_comp_tmulHom_eq]
  simp only [twist_id, Category.comp_id, ← BoxProd.tmulHom_add_left,
    ← Preadditive.add_comp, proj_add_proj]
  rfl

/-- Multiplying the genuine relation on the two specified sides keeps all
coefficients, in their original order; no parity specialization is used. -/
theorem single_recurrence (i : I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m : ℕ) :
    (∑ j : Fin (cutoff i + 1), singleClass D Sc cutoff i
      (a * singleCoefficient D cutoff i j) (j.val + m)) = 0 := by
  have h := comp_ideal D Sc cutoff (singleTerm D Sc cutoff i 1 m)
    (relation_mem D Sc cutoff i [])
  have h' := ideal_comp D Sc cutoff h (singleTerm D Sc cutoff i a 0)
  rw [single_relation, Preadditive.comp_sum, Preadditive.sum_comp] at h'
  simp only [single_precomp, single_postcomp] at h'
  have hz : (ideal D Sc cutoff [i] [i]).mkQ
      (∑ j : Fin (cutoff i + 1), singleTerm D Sc cutoff i
        (a * singleCoefficient D cutoff i j) (j.val + m)) = 0 :=
    (Submodule.Quotient.mk_eq_zero (ideal D Sc cutoff [i] [i])).mpr h'
  rw [map_sum] at hz
  exact hz

end OddMath.QuiverHecke.ELVOld
