/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendRowsShift
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendPolynomialIdempotents

/-! # Finite projectivity of the ELV append endpoint

The common-append reconstruction and central exponent shift identify K₀ with
finite polynomial old-idempotent rows in the ELV deformed square resolution.
The section and retraction use the literal right ideals `e(t) B[s]`, without
nonvanishing or flatness hypotheses on old corners.
-/
noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The full content append endpoint with its central append action, as a right polynomial module. -/
abbrev AppendEndpointPolynomial (i : I) (ν : List I) :=
  RightCentralPolynomialModule (appendContentCentral D Sc cutoff i ν)

/-- Reconstruction respects arbitrary old matrix coefficients and the central variable. -/
def appendEndpointPolynomialReconstruct (i : I) (ν : List I) :
    AppendRowsPolynomial D Sc cutoff i ν (centralDegree D i) →ₗ[
      (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ] AppendEndpointPolynomial D Sc cutoff i ν :=
  RightCentralPolynomialModule.map _ _ (appendRowsReconstruct D Sc cutoff i ν)
    (appendRowsReconstruct_shift D Sc cutoff i ν)

/-- Upgrade the actual common-append equivalence, using its proved central compatibility. -/
def appendEndpointPolynomialRowsEquiv (i : I) (ν : List I) :
    AppendRowsPolynomial D Sc cutoff i ν (centralDegree D i) ≃ₗ[
      (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ] AppendEndpointPolynomial D Sc cutoff i ν :=
  LinearEquiv.ofBijective (appendEndpointPolynomialReconstruct D Sc cutoff i ν)
    ⟨(appendRowsEquiv D Sc cutoff i ν).injective,
      (appendRowsEquiv D Sc cutoff i ν).surjective⟩

private theorem appendCentralDegree_positive (i : I) : 0 < centralDegree D i := by
  unfold centralDegree
  split <;> decide

/-- Actual finite polynomial-row coordinates of the full append endpoint, not scalar PBW coordinates. -/
def appendEndpointPolynomialEquiv (i : I) (ν : List I) :
    AppendEndpointPolynomial D Sc cutoff i ν ≃ₗ[
      (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
        AppendPolynomialOldRows D Sc cutoff i ν (centralDegree D i) :=
  (appendEndpointPolynomialRowsEquiv D Sc cutoff i ν).symm.trans
    (appendRowsPolynomialEquiv D Sc cutoff i ν (centralDegree D i) (appendCentralDegree_positive D i))

/-- Reconstruction reassembles the exponent and uses the untwisted append pairing. -/
@[simp] theorem appendEndpointPolynomialEquiv_symm_of (i : I) (ν : List I)
    (z : AppendPolynomialCoefficients D Sc cutoff i ν (centralDegree D i)) :
    (appendEndpointPolynomialEquiv D Sc cutoff i ν).symm
      (RightCentralPolynomialModule.of _ z) =
    RightCentralPolynomialModule.of _ (appendRowsReconstruct D Sc cutoff i ν
      (appendRowsJoin D Sc cutoff i ν (centralDegree D i) z)) := rfl

/-- Extraction uses the actual signed PBW inverse, followed by central block/residue splitting. -/
theorem appendEndpointPolynomialEquiv_of (i : I) (ν : List I)
    (z : AppendContent D Sc cutoff i ν) :
    appendEndpointPolynomialEquiv D Sc cutoff i ν (RightCentralPolynomialModule.of _ z) =
    RightCentralPolynomialModule.of _
      (appendRowsSplit D Sc cutoff i ν (centralDegree D i) (appendCentralDegree_positive D i)
        (appendDecode D Sc cutoff i ν z)) := by
  apply (appendEndpointPolynomialEquiv D Sc cutoff i ν).symm.injective
  rw [LinearEquiv.symm_apply_apply, appendEndpointPolynomialEquiv_symm_of,
    appendRowsJoin_split, appendRowsReconstruct_decode]

/-- Explicit section into the finite free polynomial module. -/
def appendEndpointSection (i : I) (ν : List I) :
    AppendEndpointPolynomial D Sc cutoff i ν →ₗ[
      (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
        AppendPolynomialFree D Sc cutoff i ν (centralDegree D i) :=
  (appendPolynomialRowsSection D Sc cutoff i ν (centralDegree D i)).comp
    (appendEndpointPolynomialEquiv D Sc cutoff i ν).toLinearMap

/-- Explicit retraction from the finite free polynomial module. -/
def appendEndpointRetraction (i : I) (ν : List I) :
    AppendPolynomialFree D Sc cutoff i ν (centralDegree D i) →ₗ[
      (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
        AppendEndpointPolynomial D Sc cutoff i ν :=
  (appendEndpointPolynomialEquiv D Sc cutoff i ν).symm.toLinearMap.comp
    (appendPolynomialRowsRetraction D Sc cutoff i ν (centralDegree D i))

@[simp] theorem appendEndpointRetraction_section (i : I) (ν : List I)
    (z : AppendEndpointPolynomial D Sc cutoff i ν) :
    appendEndpointRetraction D Sc cutoff i ν (appendEndpointSection D Sc cutoff i ν z) = z := by
  simp [appendEndpointRetraction, appendEndpointSection]

theorem appendEndpoint_projective (i : I) (ν : List I) :
    Module.Projective (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ
      (AppendEndpointPolynomial D Sc cutoff i ν) :=
  Module.Projective.of_split (appendEndpointSection D Sc cutoff i ν)
    (appendEndpointRetraction D Sc cutoff i ν) (by
      ext z
      exact appendEndpointRetraction_section D Sc cutoff i ν z)

theorem appendEndpoint_finite (i : I) (ν : List I) :
    Module.Finite (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ
      (AppendEndpointPolynomial D Sc cutoff i ν) :=
  Module.Finite.of_surjective (appendEndpointRetraction D Sc cutoff i ν)
    (Function.LeftInverse.surjective (appendEndpointRetraction_section D Sc cutoff i ν))

/-- Polynomial old-row coordinates for K₀, with the prescribed central action. -/
def K0PolynomialEquiv (i : I) (ν : List I) :
    K0 D Sc cutoff i ν ≃ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      AppendPolynomialOldRows D Sc cutoff i ν (centralDegree D i) :=
  appendEndpointPolynomialEquiv D Sc cutoff i ν

/-- K₀ is the finite family of literal right ideals `e(t) B[s]`. -/
def K0IdempotentEquiv (i : I) (ν : List I) :
    K0 D Sc cutoff i ν ≃ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      AppendPolynomialIdempotentRows D Sc cutoff i ν (centralDegree D i) :=
  (K0PolynomialEquiv D Sc cutoff i ν).trans
    (appendPolynomialRowsIdempotentEquiv D Sc cutoff i ν (centralDegree D i))

instance K0_projective (i : I) (ν : List I) :
    Module.Projective (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K0 D Sc cutoff i ν) :=
  appendEndpoint_projective D Sc cutoff i ν

instance K0_finite (i : I) (ν : List I) :
    Module.Finite (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K0 D Sc cutoff i ν) :=
  appendEndpoint_finite D Sc cutoff i ν

end OddMath.QuiverHecke.ELVOld
