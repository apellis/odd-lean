/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVPrefixKilling
import OddMath.QuiverHecke.CyclotomicAction.ELVOneStrand
/-! # Full ELV polynomial at the append endpoint

`relation_comp_move` transports the finite all-colour cyclotomic polynomial
through G with its total coefficient parity sign. This provides the ordered
coefficient comparison in `DeformedBoundaryDivision.md` §3. It imposes no
cyclotomic relation on the moving endpoint.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def endpointCoefficient (i : I) (j : Fin (cutoff i + 1)) : SKM.SYM D k :=
  if h : D.parity i = 1 then
    SKM.SYM.elvMonicCoefficient D k ⟨i, h⟩ (cutoff i) j
  else SKM.SYM.evenMonicCoefficient D k i (cutoff i) j

private theorem endpointCoefficient_parity (i : I) (j : Fin (cutoff i + 1)) :
    SKM.SYM.polynomialExteriorEquiv D k (endpointCoefficient D cutoff i j) ∈
      SKM.SYM.polynomialExteriorParity D k
        (cutoff i • D.parity i - j.val • D.parity i) := by
  unfold endpointCoefficient
  split_ifs with hi
  · simpa only [hi, nsmul_eq_mul, mul_one] using
      (SKM.SYM.elvMonicCoefficient_mem_parity (k := k) D ⟨i, hi⟩ (cutoff i) j)
  · have he : D.parity i = 0 := (parity_eq_zero_or_one (D.parity i)).resolve_right hi
    simp only [he, nsmul_zero, sub_self, SKM.SYM.evenMonicCoefficient, map_smul]
    apply Submodule.smul_mem
    cases cutoff i - j.val with
    | zero =>
        simpa only [SKM.SYM.evenCyclotomicCoefficient, map_one] using
          (SetLike.GradedOne.one_mem : (1 : SKM.SYM.PolynomialExterior D k) ∈
            SKM.SYM.polynomialExteriorParity D k 0)
    | succ n => exact SKM.SYM.polynomialExterior_e_mem_even D k i n

private theorem relation_as_polynomial (i : I) (v : List I) :
    relation D Sc cutoff i v =
      (elvQuotientFunctor D Sc cutoff).map
        (coefficientDotPolynomial D Sc (i :: v) 0 (cutoff i)
          (endpointCoefficient D cutoff i)) := by
  unfold relation endpointCoefficient
  dsimp only [elvQuotientFunctor]
  split_ifs with hi
  · apply congrArg (elvQuotientMap D Sc cutoff _ _)
    exact (elvDotPolynomial_first D Sc ⟨i, hi⟩ v (cutoff i)).symm
  · apply congrArg (elvQuotientMap D Sc cutoff _ _)
    unfold evenCyclotomic deformedCyclotomic coefficientDotPolynomial
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simp only [dotE_pow, firstDotPower, List.map_replicate]

/-- The full finite ELV polynomial at the last strand, with coefficients on the left. -/
def endpointELV (i : I) (v : List I) : hom D Sc cutoff (v ++ [i]) (v ++ [i]) :=
  ∑ j : Fin (cutoff i + 1), singleCoefficient D cutoff i j ⊗ₜ[k]
    (dotE D Sc (v ++ [i]) v.length ^ j.val : End _)

private theorem endpointELV_as_polynomial (i : I) (v : List I) :
    endpointELV D Sc cutoff i v =
      (elvQuotientFunctor D Sc cutoff).map
        (coefficientDotPolynomial D Sc (v ++ [i]) v.length (cutoff i)
          (endpointCoefficient D cutoff i)) := by
  change _ = elvQuotientMap D Sc cutoff _ _ _
  unfold endpointELV coefficientDotPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (elvQuotientMap_source D Sc cutoff (endpointCoefficient D cutoff i j)
    (dotE D Sc (v ++ [i]) v.length ^ j.val)).symm

private theorem move_as_map (i : I) (v : List I) :
    move D Sc cutoff i v =
      (elvQuotientFunctor D Sc cutoff).map
        (sourceCoefficientHom D Sc 1 (moveHom D Sc i [] v)) := by
  change _ = elvQuotientMap D Sc cutoff _ _ _
  rw [elvQuotientMap_source, map_one]
  rfl

/-- Full-coefficient moving-polynomial transport, at every colour and cutoff. -/
theorem relation_comp_move (i : I) (v : List I) :
    relation D Sc cutoff i v ≫ move D Sc cutoff i v =
      sign k ((cutoff i • D.parity i) * (D.parity i * wordSumParity D v)) •
        (move D Sc cutoff i v ≫ endpointELV D Sc cutoff i v) := by
  have h := coefficientDotPolynomial_comp_moveHom D Sc i [] v (cutoff i)
    (endpointCoefficient D cutoff i) (cutoff i • D.parity i)
    (endpointCoefficient_parity D cutoff i)
  have hq := congrArg (fun f => (elvQuotientFunctor D Sc cutoff).map f) h
  rw [relation_as_polynomial, endpointELV_as_polynomial, move_as_map]
  simp only [List.nil_append, List.length_nil, zero_add,
    Functor.map_comp, Functor.map_smul] at hq
  dsimp only [elvQuotientFunctor] at hq ⊢
  exact hq
end OddMath.QuiverHecke.ELVOld
