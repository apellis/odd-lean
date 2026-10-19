/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.LowestPolarization
import OddMath.CoveringQuantum.UDot.VermaWeightExamples

/-!
# Highest and lowest quotients on infinite non-bar data

The source-generated quotient of CHWII Remark 2.5 is instantiated at a dominant
weight of the countable orthogonal datum. Singularity, action-generated relation
descent, representative form evaluation, finite weight support and global
Chevalley covariance use the same quotient. The lowest form retains the J sign
and the rho/tau1-prime convention of Clark IV Proposition 5.8 / §5.2.
Unlike the finite bar-consistent source setting, this example has infinitely
many colours and fails bar-consistency. No local-nilpotence, simplicity,
nondegeneracy, tensor or limit assertion is made.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.IntegrableQuotientExamples
open Coefficients PreF GenericVerma VermaWeightExamples

/-- A nonnegative highest weight, distinct from the unrestricted Verma examples. -/
def highestWeight : ℕ →₀ ℤ := Finsupp.single 0 2

/-- Dominance holds at every colour, including those outside the weight support. -/
theorem dominant (i : ℕ) : 0 ≤ datum.h i highestWeight := by
  simp only [datum, RootDatum.h, highestWeight, Finsupp.lapply_apply]
  by_cases h : 0 = i <;> simp [h]

/-- The example uses an infinite colour type and a non-bar-consistent datum. -/
theorem applicability : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent :=
  ⟨inferInstance, not_barConsistent⟩

/-- Each generating power is singular under every original lowering operator. -/
theorem singular (i j : ℕ) :
    lower datum.toSuperCartanDatum j (datum.h j highestWeight)
      (integrabilityGenerator datum highestWeight i) = 0 :=
  lower_integrabilityGenerator datum highestWeight i j (dominant i)

/-- The relation and its entire original action orbit vanish in the quotient. -/
theorem relation_descent (i : ℕ)
    (u : CoveringUDot Coefficients.Ring datum Coefficients.q pi) :
    toIntegrable datum highestWeight
      (representation datum highestWeight u
        (integrabilityGenerator datum highestWeight i)) = 0 := by
  rw [← integrableRepresentation_toIntegrable, toIntegrable_generator, map_zero]

/-- A mixed-weight representative, with no assertion that its quotient image is nonzero. -/
def representative : datum.serreF Coefficients.q pi :=
  datum.toSerreF Coefficients.q pi (θ Coefficients.Ring 0) +
    (Coefficients.q : Coefficients.Ring) • 1

/-- The descended form computes on this representative and any second representative. -/
theorem representative_pairing (y : datum.serreF Coefficients.q pi) :
    integrablePolarization datum highestWeight dominant
      (toIntegrable datum highestWeight representative) (toIntegrable datum highestWeight y) =
      polarization datum highestWeight representative y := rfl

/-- An explicit scalar computation in the descended polarization. -/
theorem vacuum_pairing :
    integrablePolarization datum highestWeight dominant
      (toIntegrable datum highestWeight 1) (toIntegrable datum highestWeight representative) =
      (Coefficients.q : Coefficients.Ring) := by
  rw [integrablePolarization_toIntegrable, polarization_one_left]
  simp [representative]

/-- Every quotient vector has the constructed finite-support weight resolution. -/
theorem weight_resolution (x : IntegrableQuotient datum highestWeight) :
    Finsupp.lsum Coefficients.Ring (fun _ : ℕ →₀ ℤ ↦
      (LinearMap.id : Module.End Coefficients.Ring (IntegrableQuotient datum highestWeight)))
      (integrableGrading datum highestWeight x) = x :=
  sum_integrableGrading datum highestWeight x

/-- Global weight/Chevalley covariance holds on arbitrary quotient vectors. -/
theorem weight_chevalley (f : (ℕ →₀ ℤ) → Coefficients.Ring) (positive : Bool)
    (i : ℕ) (x : IntegrableQuotient datum highestWeight) :
    integrableWeight datum highestWeight f
      (integrableChevalley datum highestWeight positive i x) =
      integrableChevalley datum highestWeight positive i
        (integrableWeight datum highestWeight
          (fun μ ↦ f (μ + halfRoot datum positive i)) x) :=
  integrableWeight_chevalley datum highestWeight f positive i x

/-- The same-action lowest adjointness uses the descended J-normalized form. -/
theorem lowest_adjoint
    (u : CoveringUDot Coefficients.Ring datum Coefficients.q pi)
    (x y : IntegrableQuotient datum highestWeight) :
    lowestPolarization datum highestWeight dominant
      (lowestRepresentation datum highestWeight u x) y =
      lowestPolarization datum highestWeight dominant x
        (lowestRepresentation datum highestWeight
          (rho datum Coefficients.q pi pi_sq u).unop y) :=
  lowestPolarization_adjoint datum highestWeight dominant u x y

end OddMath.CoveringQuantum.UDot.IntegrableQuotientExamples
