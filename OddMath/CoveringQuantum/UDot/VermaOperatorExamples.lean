/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.VermaSerre
import OddMath.CoveringQuantum.SerreDerivExamples

/-!
# Infinite-colour quotient lowering operators

The orthogonal even datum on `ℕ` exercises the quotient operators and positive
Serre action in the generic covering ring. It is not bar consistent. The vacuum
and one-generator formulas use the quantum integers of [BE2] §10 and the lowering
formula derived from [CHW1] Proposition 2.2.2(b). Unlike the finite-colour radical
presentation in [CHW1], these statements use the Serre quotient directly.
They assert neither faithfulness nor the modified-form identity of [BE2] Theorem 10.3.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot.VermaOperatorExamples

open PreF Coefficients SerreDerivExamples

local notation "H" => orthogonalEven.serreF Coefficients.q pi

/-- The example has infinitely many colours and is not bar consistent. -/
theorem infinite_nonbar : Infinite ℕ ∧ ¬ orthogonalEven.BarConsistent :=
  ⟨infinite_colours, orthogonalEven_not_barConsistent⟩

/-- The normalization denominator is a unit at every colour. -/
theorem denominator_isUnit (i : ℕ) :
    IsUnit (vermaDenominator orthogonalEven Coefficients.q pi i) :=
  GenericVerma.vermaDenominator_isUnit orthogonalEven i

/-- Lowering annihilates the vacuum of the Serre quotient. -/
theorem lower_vacuum (i : ℕ) (n : ℤ) :
    GenericVerma.lower orthogonalEven i n (1 : H) = 0 :=
  GenericVerma.lower_one orthogonalEven i n

/-- Lowering a generator has the prescribed quantum-integer normalization. -/
theorem lower_generator (i : ℕ) (n : ℤ) :
    GenericVerma.lower orthogonalEven i n
      (orthogonalEven.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
    qpInt (orthogonalEven.qi Coefficients.q i) (orthogonalEven.pii pi i) n • (1 : H) :=
  GenericVerma.lower_θ_self orthogonalEven i n

/-- The mixed commutator on the vacuum, in the quotient rather than the free algebra. -/
theorem commutator_vacuum (i : ℕ) (n : ℤ) :
    GenericVerma.lower orthogonalEven i n
        (orthogonalEven.toSerreF Coefficients.q pi (θ Coefficients.Ring i) * 1) -
      pi ^ (orthogonalEven.parity i * orthogonalEven.parity i).val •
        (orthogonalEven.toSerreF Coefficients.q pi (θ Coefficients.Ring i) *
          GenericVerma.lower orthogonalEven i n (1 : H)) =
    qpInt (orthogonalEven.qi Coefficients.q i) (orthogonalEven.pii pi i) n • (1 : H) := by
  simp only [mul_one, lower_vacuum, mul_zero, smul_zero, sub_zero, lower_generator]

/-- The positive Serre relation holds for endomorphisms of the infinite-colour quotient. -/
theorem lower_serre (n : ℕ → ℤ) :
    (FreeAlgebra.lift Coefficients.Ring fun i ↦ GenericVerma.lower orthogonalEven i (n i))
      (orthogonalEven.serreElt Coefficients.q pi 0 1) = 0 :=
  GenericVerma.lower_serre orthogonalEven n (by decide : (0 : ℕ) ≠ 1)

/-- The positive-half action sends its generator to the constructed lowering operator. -/
theorem action_generator (n : ℕ → ℤ) (i : ℕ) :
    GenericVerma.positiveAction orthogonalEven n
      (orthogonalEven.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
      GenericVerma.lower orthogonalEven i (n i) :=
  GenericVerma.positiveAction_θ orthogonalEven n i

/-- A positive generator acts on the matching negative generator by the quantum integer. -/
theorem action_generator_generator (n : ℕ → ℤ) (i : ℕ) :
    GenericVerma.positiveAction orthogonalEven n
      (orthogonalEven.toSerreF Coefficients.q pi (θ Coefficients.Ring i))
      (orthogonalEven.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
    qpInt (orthogonalEven.qi Coefficients.q i) (orthogonalEven.pii pi i) (n i) • (1 : H) := by
  rw [action_generator, lower_generator]

/-- A contextual Serre relation acts by zero on every vector of the quotient. -/
theorem action_contextualRelation (n : ℕ → ℤ) (x : H) :
    GenericVerma.positiveAction orthogonalEven n
      (orthogonalEven.toSerreF Coefficients.q pi contextualRelation) x = 0 := by
  rw [(orthogonalEven.mem_serreIdeal Coefficients.q pi _).mp contextualRelation_mem,
    map_zero, LinearMap.zero_apply]

end OddMath.CoveringQuantum.UDot.VermaOperatorExamples
