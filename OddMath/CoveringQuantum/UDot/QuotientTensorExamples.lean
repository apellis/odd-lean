/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorPolarization
import OddMath.CoveringQuantum.UDot.VermaWeightExamples

/-!
# Quotient tensor actions and J-polarization on infinite non-bar data

The original highest/omega-lowest quotient tensor is instantiated on a countably
infinite, non-bar-consistent datum with two explicit dominant weights. Both factors
contain generated sums of words of different degrees. No nonzero assertion about
these generated vectors is needed or made. The full Serre relations hold on arbitrary
tensors; the constructed unital and modified actions and their adjointness are also
exercised on these generated inputs, for both coproduct choices.

The conventions are Clark IV v2 §2.4 Delta1/Delta2, v=q^-1 and Proposition 5.8
rho/tau1-prime, not the printed tau1/Delta3/Delta4 pairing of §5.3. The source's
finite, bar-consistent setting is narrower than the datum used here. These are
consumers of the tensor prerequisites for TensorGram.MixedGram, not a Gram-limit
or nondegeneracy assertion.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.QuotientTensorExamples
open Coefficients PreF GenericVerma VermaWeightExamples TensorProduct

/-- The highest weight of the first factor. -/
def highestWeight : ℕ →₀ ℤ := Finsupp.single 0 4 + Finsupp.single 1 2

/-- The highest weight underlying the omega-lowest second factor. -/
def lowestWeight : ℕ →₀ ℤ := Finsupp.single 0 2 + Finsupp.single 1 4

theorem highest_dominant (i : ℕ) : 0 ≤ datum.h i highestWeight := by
  simp only [datum, RootDatum.h, highestWeight, Finsupp.lapply_apply, Finsupp.add_apply]
  exact add_nonneg (by simp only [Finsupp.single_apply]; split_ifs <;> omega)
    (by simp only [Finsupp.single_apply]; split_ifs <;> omega)

theorem lowest_dominant (i : ℕ) : 0 ≤ datum.h i lowestWeight := by
  simp only [datum, RootDatum.h, lowestWeight, Finsupp.lapply_apply, Finsupp.add_apply]
  exact add_nonneg (by simp only [Finsupp.single_apply]; split_ifs <;> omega)
    (by simp only [Finsupp.single_apply]; split_ifs <;> omega)

/-- Neither finiteness nor bar-consistency holds in this example. -/
theorem applicability : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent :=
  ⟨inferInstance, not_barConsistent⟩

/-- A representative with constant, one-letter and two-letter terms. -/
def leftRepresentative : datum.serreF Coefficients.q pi :=
  1 + datum.toSerreF Coefficients.q pi (θ Coefficients.Ring 0) +
    (Coefficients.q : Coefficients.Ring) •
      datum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [1, 0])

/-- A different inhomogeneous representative for the second factor. -/
def rightRepresentative : datum.serreF Coefficients.q pi :=
  (Coefficients.q : Coefficients.Ring) • 1 +
    datum.toSerreF Coefficients.q pi (θ Coefficients.Ring 1) +
      pi • datum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [0, 0])

/-- A generated input in the original highest quotient. -/
def leftInput : IntegrableQuotient datum highestWeight :=
  integrableChevalley datum highestWeight false 0
    (toIntegrable datum highestWeight leftRepresentative)

/-- A generated input in the quotient underlying the omega-lowest factor. -/
def rightInput : IntegrableQuotient datum lowestWeight :=
  integrableChevalley datum lowestWeight false 1
    (toIntegrable datum lowestWeight rightRepresentative)

/-- The original quotient tensor, not a replacement presentation. -/
abbrev Space :=
  IntegrableQuotient datum highestWeight ⊗[Coefficients.Ring]
    IntegrableQuotient datum lowestWeight

/-- The tensor of the two original vacua. -/
def vacuum : Space :=
  toIntegrable datum highestWeight 1 ⊗ₜ toIntegrable datum lowestWeight 1

/-- Both tensor factors are generated from the displayed inhomogeneous representatives. -/
def input : Space := leftInput ⊗ₜ rightInput

/-- Actual E evaluation in either coproduct, including its toral/Koszul summand. -/
theorem E_input (s : Bool) (i : ℕ) :
    tensorE datum highestWeight lowestWeight s i input =
      integrableChevalley datum highestWeight true i leftInput ⊗ₜ rightInput +
        tensorTwist datum highestWeight s i leftInput ⊗ₜ
          integrableChevalley datum lowestWeight false i rightInput :=
  tensorE_tmul datum highestWeight lowestWeight s i leftInput rightInput

/-- Actual F evaluation retains the omega-lowest action and its J factor. -/
theorem F_input (s : Bool) (i : ℕ) :
    tensorF datum highestWeight lowestWeight s i input =
      integrableChevalley datum highestWeight false i leftInput ⊗ₜ
        tensorK datum lowestWeight i rightInput +
      tensorFTwist datum highestWeight s i leftInput ⊗ₜ lowestF datum lowestWeight i rightInput :=
  tensorF_tmul datum highestWeight lowestWeight s i leftInput rightInput

/-- Full positive Serre, evaluated on any tensor, not just the vacuum. -/
theorem positive_serre (s : Bool) {i j : ℕ} (hij : i ≠ j) (x : Space) :
    (∑ r ∈ Finset.range (datum.serreDeg i j + 1),
      datum.serreCoeff Coefficients.q pi i j r •
        (tensorE datum highestWeight lowestWeight s i ^ (datum.serreDeg i j - r) *
          tensorE datum highestWeight lowestWeight s j *
            tensorE datum highestWeight lowestWeight s i ^ r)) x = 0 := by
  rw [tensorE_serre datum highestWeight lowestWeight s hij, LinearMap.zero_apply]

/-- Full negative Serre, evaluated on any tensor, not just the vacuum. -/
theorem negative_serre (s : Bool) {i j : ℕ} (hij : i ≠ j) (x : Space) :
    (∑ r ∈ Finset.range (datum.serreDeg i j + 1),
      datum.serreCoeff Coefficients.q pi i j r •
        (tensorF datum highestWeight lowestWeight s i ^ (datum.serreDeg i j - r) *
          tensorF datum highestWeight lowestWeight s j *
            tensorF datum highestWeight lowestWeight s i ^ r)) x = 0 := by
  rw [tensorF_serre datum highestWeight lowestWeight s hij, LinearMap.zero_apply]

/-- The mixed relation at any weight, with both equal and unequal colours allowed. -/
theorem mixed (s : Bool) (i j : ℕ) (μ : ℕ →₀ ℤ) :
    tensorEBlock datum highestWeight lowestWeight s i (μ - datum.α j) *
        tensorFBlock datum highestWeight lowestWeight s j μ -
      pi ^ (datum.parity i * datum.parity j).val •
        (tensorFBlock datum highestWeight lowestWeight s j (μ + datum.α i) *
          tensorEBlock datum highestWeight lowestWeight s i μ) =
      if i = j then qpInt (datum.qi Coefficients.q i) (datum.pii pi i) (datum.h i μ) •
        tensorProject datum highestWeight lowestWeight μ else 0 :=
  tensorBlock_comm datum highestWeight lowestWeight s i j μ

/-- The actual envelope unit acts as the identity on the generated input. -/
theorem unit_input (s : Bool) :
    tensorRepresentation datum highestWeight lowestWeight s 1 input = input := by simp

/-- Multiplication is represented on the entire tensor space. -/
theorem action_mul (s : Bool)
    (u v : CoveringUDot Coefficients.Ring datum Coefficients.q pi) (x : Space) :
    tensorRepresentation datum highestWeight lowestWeight s (u * v) x =
      tensorRepresentation datum highestWeight lowestWeight s u
        (tensorRepresentation datum highestWeight lowestWeight s v x) := by
  rw [map_mul, Module.End.mul_apply]

/-- The constructed form on the same quotient tensor. -/
def form : LinearMap.BilinForm Coefficients.Ring Space :=
  tensorPolarization datum highestWeight lowestWeight highest_dominant lowest_dominant

/-- The vacuum normalization follows from the two descended quotient forms. -/
theorem vacuum_norm : form vacuum vacuum = 1 :=
  tensorPolarization_vacuum datum highestWeight lowestWeight highest_dominant lowest_dominant

/-- All envelope elements are adjoint on arbitrary vectors in this concrete tensor. -/
theorem whole_adjoint (s : Bool)
    (u : CoveringUDot Coefficients.Ring datum Coefficients.q pi) (x y : Space) :
    form (tensorRepresentation datum highestWeight lowestWeight s u x) y =
      form x (tensorRepresentation datum highestWeight lowestWeight (!s)
        (rho datum Coefficients.q pi pi_sq u).unop y) :=
  tensorPolarization_adjoint datum highestWeight lowestWeight
    highest_dominant lowest_dominant s u x y

/-- In particular, whole-algebra adjointness evaluates on generated inhomogeneous inputs. -/
theorem generated_adjoint (s : Bool)
    (u : CoveringUDot Coefficients.Ring datum Coefficients.q pi) :
    form (tensorRepresentation datum highestWeight lowestWeight s u input) (input + vacuum) =
      form input (tensorRepresentation datum highestWeight lowestWeight (!s)
        (rho datum Coefficients.q pi pi_sq u).unop (input + vacuum)) :=
  whole_adjoint s u input (input + vacuum)

/-- The original modified algebra has the same adjointness on the generated inputs. -/
theorem modified_adjoint (s : Bool) (u : modified datum Coefficients.q pi) :
    form (tensorModifiedRepresentation datum highestWeight lowestWeight s u input)
        (input + vacuum) =
      form input (tensorModifiedRepresentation datum highestWeight lowestWeight (!s)
        (rhoModified datum Coefficients.q pi pi_sq u) (input + vacuum)) :=
  tensorPolarization_modified_adjoint datum highestWeight lowestWeight
    highest_dominant lowest_dominant s u input (input + vacuum)

end OddMath.CoveringQuantum.UDot.QuotientTensorExamples
