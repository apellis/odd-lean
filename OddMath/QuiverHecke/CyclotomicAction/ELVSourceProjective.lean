/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVSourceRowsEquivalence
import OddMath.QuiverHecke.CyclotomicAction.ELVPolynomialIdempotents

/-!
# Finite-projective full ELV source endpoints

The concrete common-tail reconstruction identifies the prescribed source action,
including its total-parity twist, with finite polynomial old-idempotent rows.
This proves finite projectivity of K₁ and K₁′ for the deformed square resolution;
it does not assert the separate append-endpoint decomposition of K₀.
-/
noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The full content source with its prescribed twist, as a right polynomial module. -/
abbrev SourceEndpointPolynomial (p : ZMod 2) (i : I) (ν : List I) :=
  RightCentralPolynomialModule (sourceContentCentral D Sc cutoff p i ν)

/-- Reconstruction respects arbitrary old matrix coefficients and the central variable. -/
def sourceEndpointPolynomialReconstruct (p : ZMod 2) (i : I) (ν : List I) :
    SourceRowsPolynomial D Sc cutoff ν (centralDegree D i) →ₗ[
      (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ] SourceEndpointPolynomial D Sc cutoff p i ν :=
  RightCentralPolynomialModule.map _ _ (sourceRowsReconstruct D Sc cutoff p i ν)
    (sourceRowsReconstruct_shift D Sc cutoff p i ν)

/-- Upgrade the actual common-source equivalence, using its proved central compatibility. -/
def sourceEndpointPolynomialRowsEquiv (p : ZMod 2) (i : I) (ν : List I) :
    SourceRowsPolynomial D Sc cutoff ν (centralDegree D i) ≃ₗ[
      (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ] SourceEndpointPolynomial D Sc cutoff p i ν :=
  LinearEquiv.ofBijective (sourceEndpointPolynomialReconstruct D Sc cutoff p i ν)
    ⟨(sourceRowsEquiv D Sc cutoff p i ν).injective,
      (sourceRowsEquiv D Sc cutoff p i ν).surjective⟩

private theorem centralDegree_positive (i : I) : 0 < centralDegree D i := by
  unfold centralDegree
  split <;> decide

/-- Actual finite polynomial-row coordinates of the full source, not scalar PBW coordinates. -/
def sourceEndpointPolynomialEquiv (p : ZMod 2) (i : I) (ν : List I) :
    SourceEndpointPolynomial D Sc cutoff p i ν ≃ₗ[
      (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
        PolynomialOldRows D Sc cutoff ν (centralDegree D i) :=
  (sourceEndpointPolynomialRowsEquiv D Sc cutoff p i ν).symm.trans
    (sourceRowsPolynomialEquiv D Sc cutoff ν (centralDegree D i) (centralDegree_positive D i))

/-- Reconstruction reassembles the exponent and uses the prescribed twisted pairing. -/
@[simp] theorem sourceEndpointPolynomialEquiv_symm_of (p : ZMod 2) (i : I) (ν : List I)
    (z : SourcePolynomialCoefficients D Sc cutoff ν (centralDegree D i)) :
    (sourceEndpointPolynomialEquiv D Sc cutoff p i ν).symm
      (RightCentralPolynomialModule.of _ z) =
    RightCentralPolynomialModule.of _ (sourceRowsReconstruct D Sc cutoff p i ν
      (sourceRowsJoin D Sc cutoff ν (centralDegree D i) z)) := rfl

/-- Extraction uses the actual signed PBW inverse, followed by central block/residue splitting. -/
theorem sourceEndpointPolynomialEquiv_of (p : ZMod 2) (i : I) (ν : List I)
    (z : SourceContent D Sc cutoff p i ν) :
    sourceEndpointPolynomialEquiv D Sc cutoff p i ν (RightCentralPolynomialModule.of _ z) =
    RightCentralPolynomialModule.of _
      (sourceRowsSplit D Sc cutoff ν (centralDegree D i) (centralDegree_positive D i)
        (sourceDecode D Sc cutoff p i ν z)) := by
  apply (sourceEndpointPolynomialEquiv D Sc cutoff p i ν).symm.injective
  rw [LinearEquiv.symm_apply_apply, sourceEndpointPolynomialEquiv_symm_of,
    sourceRowsJoin_split, sourceRowsReconstruct_decode]

/-- The two source twists are genuinely equivalent, through their same ordinary old rows. -/
def sourceEndpointTwistEquiv (p q : ZMod 2) (i : I) (ν : List I) :
    SourceEndpointPolynomial D Sc cutoff p i ν ≃ₗ[
      (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ] SourceEndpointPolynomial D Sc cutoff q i ν :=
  (sourceEndpointPolynomialEquiv D Sc cutoff p i ν).trans
    (sourceEndpointPolynomialEquiv D Sc cutoff q i ν).symm

/-- Explicit section into the finite free polynomial module. -/
def sourceEndpointSection (p : ZMod 2) (i : I) (ν : List I) :
    SourceEndpointPolynomial D Sc cutoff p i ν →ₗ[
      (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
        SourcePolynomialFree D Sc cutoff ν (centralDegree D i) :=
  (polynomialRowsSection D Sc cutoff ν (centralDegree D i)).comp
    (sourceEndpointPolynomialEquiv D Sc cutoff p i ν).toLinearMap

/-- Explicit retraction from the finite free polynomial module. -/
def sourceEndpointRetraction (p : ZMod 2) (i : I) (ν : List I) :
    SourcePolynomialFree D Sc cutoff ν (centralDegree D i) →ₗ[
      (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
        SourceEndpointPolynomial D Sc cutoff p i ν :=
  (sourceEndpointPolynomialEquiv D Sc cutoff p i ν).symm.toLinearMap.comp
    (polynomialRowsRetraction D Sc cutoff ν (centralDegree D i))

@[simp] theorem sourceEndpointRetraction_section (p : ZMod 2) (i : I) (ν : List I)
    (z : SourceEndpointPolynomial D Sc cutoff p i ν) :
    sourceEndpointRetraction D Sc cutoff p i ν (sourceEndpointSection D Sc cutoff p i ν z) = z := by
  simp [sourceEndpointRetraction, sourceEndpointSection]

theorem sourceEndpoint_projective (p : ZMod 2) (i : I) (ν : List I) :
    Module.Projective (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ
      (SourceEndpointPolynomial D Sc cutoff p i ν) :=
  Module.Projective.of_split (sourceEndpointSection D Sc cutoff p i ν)
    (sourceEndpointRetraction D Sc cutoff p i ν) (by
      ext z
      exact sourceEndpointRetraction_section D Sc cutoff p i ν z)

theorem sourceEndpoint_finite (p : ZMod 2) (i : I) (ν : List I) :
    Module.Finite (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ
      (SourceEndpointPolynomial D Sc cutoff p i ν) :=
  Module.Finite.of_surjective (sourceEndpointRetraction D Sc cutoff p i ν)
    (Function.LeftInverse.surjective (sourceEndpointRetraction_section D Sc cutoff p i ν))

/-- The epsilon-twisted source has concrete finite polynomial-row coordinates. -/
def K1PolynomialEquiv (i : I) (ν : List I) :
    K1 D Sc cutoff i ν ≃ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      PolynomialOldRows D Sc cutoff ν (centralDegree D i) :=
  sourceEndpointPolynomialEquiv D Sc cutoff (appendQ D cutoff i ν) i ν

/-- The eta-twisted source has the same ordinary row coordinates, through its own pairing. -/
def K1PrimePolynomialEquiv (i : I) (ν : List I) :
    K1Prime D Sc cutoff i ν ≃ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      PolynomialOldRows D Sc cutoff ν (centralDegree D i) :=
  sourceEndpointPolynomialEquiv D Sc cutoff (D.parity i * wordSumParity D ν) i ν

/-- The epsilon source is the finite family of literal right ideals `e(t) B[s]`. -/
def K1IdempotentEquiv (i : I) (ν : List I) :
    K1 D Sc cutoff i ν ≃ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      PolynomialIdempotentRows D Sc cutoff ν (centralDegree D i) :=
  (K1PolynomialEquiv D Sc cutoff i ν).trans
    (polynomialRowsIdempotentEquiv D Sc cutoff ν (centralDegree D i))

/-- The eta source is the same finite family, without identifying the twisted actions. -/
def K1PrimeIdempotentEquiv (i : I) (ν : List I) :
    K1Prime D Sc cutoff i ν ≃ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      PolynomialIdempotentRows D Sc cutoff ν (centralDegree D i) :=
  (K1PrimePolynomialEquiv D Sc cutoff i ν).trans
    (polynomialRowsIdempotentEquiv D Sc cutoff ν (centralDegree D i))

instance K1_projective (i : I) (ν : List I) :
    Module.Projective (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K1 D Sc cutoff i ν) :=
  sourceEndpoint_projective D Sc cutoff (appendQ D cutoff i ν) i ν

instance K1_finite (i : I) (ν : List I) :
    Module.Finite (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K1 D Sc cutoff i ν) :=
  sourceEndpoint_finite D Sc cutoff (appendQ D cutoff i ν) i ν

instance K1Prime_projective (i : I) (ν : List I) :
    Module.Projective (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K1Prime D Sc cutoff i ν) :=
  sourceEndpoint_projective D Sc cutoff (D.parity i * wordSumParity D ν) i ν

instance K1Prime_finite (i : I) (ν : List I) :
    Module.Finite (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K1Prime D Sc cutoff i ν) :=
  sourceEndpoint_finite D Sc cutoff (D.parity i * wordSumParity D ν) i ν

end OddMath.QuiverHecke.ELVOld
