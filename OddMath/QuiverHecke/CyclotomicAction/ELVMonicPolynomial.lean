/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.EndpointNormEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendBalance
import OddMath.QuiverHecke.CyclotomicAction.ELVOneStrand

/-! # Full-coefficient monic moving-dot product

The literal ELV coefficient polynomial times the normalized full chain norm is
monic. Its evaluation is the ordered categorical norm followed by the endpoint
ELV relation. All coefficients lie in the original full super coefficient category.
`ELVMonicAnnihilator` applies this polynomial to the full cyclotomic ideal.
-/

noncomputable section
open CategoryTheory Polynomial
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def affineUnitEndHom (w : List I) :
    End ((pres D Sc).obj (ob D w)) →+* End (obj D Sc cutoff w) where
  toFun := affineUnit D Sc cutoff w w
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := affineUnit_id D Sc cutoff w
  map_mul' f g := affineUnit_comp D Sc cutoff g f

@[simp] theorem affineUnitEndHom_apply (w : List I)
    (f : End ((pres D Sc).obj (ob D w))) :
    affineUnitEndHom D Sc cutoff w f = affineUnit D Sc cutoff w w f := rfl

def movingELVPolynomial (i : I) (v : List I) : Polynomial (End (obj D Sc cutoff (v ++ [i]))) :=
  ∑ r : Fin (cutoff i + 1),
    (C (R := End (obj D Sc cutoff (v ++ [i]))))
      (ELVPScalar.scalar D Sc cutoff (v ++ [i]) (singleCoefficient D cutoff i r)) * X ^ r.val

private theorem finiteMonic {B : Type*} [Ring B] (n : ℕ) (a : Fin (n + 1) → B)
    (ha : a (Fin.last n) = 1) : (∑ r, C (a r) * X ^ r.val).Monic := by
  apply monic_of_degree_le n
  · apply (degree_sum_le _ _).trans
    apply Finset.sup_le
    intro r hr
    exact (degree_C_mul_X_pow_le _ _).trans (by exact_mod_cast Nat.le_of_lt_succ r.isLt)
  · rw [finsetSum_coeff, Finset.sum_eq_single (Fin.last n)]
    · simp only [Fin.val_last, coeff_C_mul_X_pow, ite_true, ha]
    · intro r hr hn
      rw [coeff_C_mul_X_pow]
      split_ifs with h
      · exact (hn (Fin.ext h.symm)).elim
      · rfl
    · simp

theorem movingELVPolynomial_monic (i : I) (v : List I) :
    (movingELVPolynomial D Sc cutoff i v).Monic := by
  apply finiteMonic (cutoff i)
  rw [singleCoefficient_top]
  rfl

theorem movingELVPolynomial_eval (i : I) (v : List I) :
    (movingELVPolynomial D Sc cutoff i v).eval₂ (RingHom.id _)
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length)) =
      ∑ r : Fin (cutoff i + 1), singleCoefficient D cutoff i r ⊗ₜ[k]
        (dotE D Sc (v ++ [i]) v.length ^ r.val : End _) := by
  rw [movingELVPolynomial, eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [C_mul_X_pow_eq_monomial, eval₂_monomial]
  simp only [RingHom.id_apply]
  rw [← map_pow, End.mul_def]
  exact affineUnit_comp_scalar D Sc cutoff _ _

def affineNormalizedEndpointNormPolynomial (i : I) (v : List I) :
    Polynomial (End (obj D Sc cutoff (v ++ [i]))) :=
  (normalizedEndpointNormPolynomial D Sc i
    (endpointOldDotEntries D Sc (v ++ [i]) 0 v)).map (affineUnitEndHom D Sc cutoff _)

theorem affineNormalizedEndpointNormPolynomial_monic (i : I) (v : List I) :
    (affineNormalizedEndpointNormPolynomial D Sc cutoff i v).Monic :=
  (normalizedEndpointNormPolynomial_monic D Sc i _).map _

theorem affineNormalizedEndpointNormPolynomial_coeffCommute (i : I) (v : List I) :
    NormCoeffCommute
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length))
      (affineNormalizedEndpointNormPolynomial D Sc cutoff i v) := by
  have h := endpointOldDotEntries_pow_commute D Sc i v []
  simp only [List.nil_append, List.length_nil, zero_add] at h
  have hc := normalizedEndpointNormPolynomial_coeffCommute D Sc i _ _ h
  intro n
  simpa only [affineNormalizedEndpointNormPolynomial, coeff_map] using
    (hc n).map (affineUnitEndHom D Sc cutoff (v ++ [i]))

theorem affineNormalizedEndpointNormPolynomial_eval (i : I) (v : List I) :
    (affineNormalizedEndpointNormPolynomial D Sc cutoff i v).eval₂ (RingHom.id _)
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length)) =
      affineUnitEndHom D Sc cutoff (v ++ [i])
        (algebraMap k (End ((pres D Sc).obj (ob D ([] ++ v ++ [i]))))
          ((((endpointOldDotEntries D Sc (v ++ [i]) 0 v).map fun z =>
            (endpointNormLeadingUnit D Sc z.1 i)⁻¹).prod : kˣ) : k) *
          endpointNorm D Sc i [] v) := by
  have h := eval₂_actual_normalizedEndpointNormPolynomial D Sc i [] v
  simp only [List.nil_append, List.length_nil, zero_add] at h
  change Polynomial.eval₂ (RingHom.id _)
    (affineUnitEndHom D Sc cutoff _ (dotE D Sc (v ++ [i]) v.length))
    (Polynomial.map (affineUnitEndHom D Sc cutoff _)
      (normalizedEndpointNormPolynomial D Sc i _)) = _
  rw [eval₂_map, RingHom.id_comp, eval₂_at_apply]
  exact congrArg (affineUnitEndHom D Sc cutoff _) h

def monicELVEndpointProduct (i : I) (v : List I) :
    Polynomial (End (obj D Sc cutoff (v ++ [i]))) :=
  movingELVPolynomial D Sc cutoff i v * affineNormalizedEndpointNormPolynomial D Sc cutoff i v

theorem monicELVEndpointProduct_monic (i : I) (v : List I) :
    (monicELVEndpointProduct D Sc cutoff i v).Monic :=
  (movingELVPolynomial_monic D Sc cutoff i v).mul
    (affineNormalizedEndpointNormPolynomial_monic D Sc cutoff i v)

theorem monicELVEndpointProduct_eval (i : I) (v : List I) :
    (monicELVEndpointProduct D Sc cutoff i v).eval₂ (RingHom.id _)
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length)) =
      (∑ r : Fin (cutoff i + 1), singleCoefficient D cutoff i r ⊗ₜ[k]
        (dotE D Sc (v ++ [i]) v.length ^ r.val : End _) : End (obj D Sc cutoff (v ++ [i]))) *
      affineUnitEndHom D Sc cutoff (v ++ [i])
        (algebraMap k (End ((pres D Sc).obj (ob D ([] ++ v ++ [i]))))
          ((((endpointOldDotEntries D Sc (v ++ [i]) 0 v).map fun z =>
            (endpointNormLeadingUnit D Sc z.1 i)⁻¹).prod : kˣ) : k) *
          endpointNorm D Sc i [] v) := by
  refine (affineNormalizedEndpointNormPolynomial_coeffCommute D Sc cutoff i v).eval_mul.trans ?_
  exact congrArg₂ (fun a b : End (obj D Sc cutoff (v ++ [i])) => a * b)
    (movingELVPolynomial_eval D Sc cutoff i v)
    (affineNormalizedEndpointNormPolynomial_eval D Sc cutoff i v)

end OddMath.QuiverHecke.ELVOld
