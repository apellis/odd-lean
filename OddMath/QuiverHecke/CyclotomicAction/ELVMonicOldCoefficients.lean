/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMonicPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedAppend

/-! # Old coefficients of the actual monic endpoint product

Every coefficient of the enlarged monic moving-dot polynomial is explicitly
inserted from the old full-coefficient endomorphism ring. This is the coefficient
closure input for bounded moving-exponent reduction from `ELVMonicAnnihilator`;
no centrality of arbitrary full ELV coefficients is assumed.
-/

noncomputable section
open CategoryTheory Polynomial
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def rightContextEndHom (i : I) (v : List I) :
    End (obj D Sc cutoff v) →+* End (obj D Sc cutoff (v ++ [i])) where
  toFun := rightContext D Sc cutoff [i] v v
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := rightContext_id D Sc cutoff [i] v
  map_mul' f g := rightContext_comp D Sc cutoff [i] g f

@[simp] theorem rightContextEndHom_apply (i : I) (v : List I)
    (f : End (obj D Sc cutoff v)) :
    rightContextEndHom D Sc cutoff i v f = rightContext D Sc cutoff [i] v v f := rfl

private theorem normalizedFactor_map {B C' : Type*} [Ring B] [Ring C']
    [Algebra k B] [Algebra k C'] (f : B →ₐ[k] C') (j i : I) (x : B) :
    (normalizedEndpointNormFactor D Sc j i x).map f.toRingHom =
      normalizedEndpointNormFactor D Sc j i (f x) := by
  simp only [normalizedEndpointNormFactor, Polynomial.map_mul, Polynomial.map_C]
  congr 1
  · exact congrArg C (f.commutes _)
  · unfold endpointNormFactor
    split_ifs <;>
      simp [IntertwinerMeet.qLeft, Algebra.smul_def, Polynomial.algebraMap_apply,
        Polynomial.map_sum]

private theorem normalizedEntries_map (i : I) (w σ ν : List I) (p : ℕ)
    (h : p + ν.length ≤ w.length) :
    (normalizedEndpointNormPolynomial D Sc i (endpointOldDotEntries D Sc w p ν)).map
        (whiskerListAlgHom D Sc w σ).toRingHom =
      normalizedEndpointNormPolynomial D Sc i (endpointOldDotEntries D Sc (w ++ σ) p ν) := by
  induction ν generalizing p with
  | nil => simp [endpointOldDotEntries, normalizedEndpointNormPolynomial]
  | cons j ν ih =>
    simp only [endpointOldDotEntries, normalizedEndpointNormPolynomial, Polynomial.map_mul]
    rw [normalizedFactor_map]
    have hd : whiskerListAlgHom D Sc w σ (dotE D Sc w p) = dotE D Sc (w ++ σ) p :=
      dotE_whiskerRight D Sc w σ p (by simp only [List.length_cons] at h; omega)
    rw [hd, ih (p + 1) (by simp only [List.length_cons] at h; omega)]

/-- An explicit old-endomorphism polynomial whose image is the concrete endpoint product. -/
def oldMonicELVEndpointProduct (i : I) (v : List I) : Polynomial (End (obj D Sc cutoff v)) :=
  (∑ r : Fin (cutoff i + 1),
    C (R := End (obj D Sc cutoff v))
      (ELVPScalar.scalar D Sc cutoff v (singleCoefficient D cutoff i r)) * X ^ r.val) *
  (normalizedEndpointNormPolynomial D Sc i (endpointOldDotEntries D Sc v 0 v)).map
    (affineUnitEndHom D Sc cutoff v)

theorem oldMonicELVEndpointProduct_map (i : I) (v : List I) :
    (oldMonicELVEndpointProduct D Sc cutoff i v).map (rightContextEndHom D Sc cutoff i v) =
      monicELVEndpointProduct D Sc cutoff i v := by
  rw [oldMonicELVEndpointProduct, Polynomial.map_mul, monicELVEndpointProduct]
  congr 1
  · simp only [movingELVPolynomial, Polynomial.map_sum, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      rightContextEndHom_apply, ELVPScalar.rightContext_scalar]
  · rw [Polynomial.map_map]
    have hc : (rightContextEndHom D Sc cutoff i v).comp (affineUnitEndHom D Sc cutoff v) =
        (affineUnitEndHom D Sc cutoff (v ++ [i])).comp
          (whiskerListAlgHom D Sc v [i]).toRingHom := by
      ext f
      rfl
    rw [hc, ← Polynomial.map_map, normalizedEntries_map D Sc i v [i] v 0 (by omega)]
    rfl

/-- Every coefficient, including coefficients outside the support, is an inserted old endomorphism. -/
theorem monicELVEndpointProduct_coeff_mem_range (i : I) (v : List I) (n : ℕ) :
    (monicELVEndpointProduct D Sc cutoff i v).coeff n ∈
      (rightContextEndHom D Sc cutoff i v).range := by
  refine ⟨(oldMonicELVEndpointProduct D Sc cutoff i v).coeff n, ?_⟩
  rw [← Polynomial.coeff_map, oldMonicELVEndpointProduct_map]

end OddMath.QuiverHecke.ELVOld
