import OddMath.QuiverHecke.ReservoirVacuumExamples
import OddMath.QuiverHecke.ReservoirWeights
import OddMath.QuiverHecke.ReservoirCoordinates
import OddMath.QuiverHecke.ReservoirWeightRestriction

open CategoryTheory

open OddMath.QuiverHecke OddMath.QuiverHecke.ReservoirWeights

example (μ : Bool → ℤ) (m : ℕ) :
    ∃ μp μm : Bool → ℤ, μm - μp = μ ∧
      (∀ i, ReservoirVacuumExamples.datum.h i μp = probeLevel μ m i) ∧
      (∀ i, ReservoirVacuumExamples.datum.h i μm = reservoirLevel μ m i) :=
  exists_weights_of_pairing_surjective ReservoirVacuumExamples.datum
    (fun h => ⟨h, rfl⟩) μ m

example (N : ℕ) : ∃ m, ∀ i : Bool,
    N ≤ probeLevel (fun i => if i then (-3 : ℤ) else 2) m i ∧
    N ≤ reservoirLevel (fun i => if i then (-3 : ℤ) else 2) m i :=
  levels_cofinal _ N

#print axioms level_difference
#print axioms reservoir_parity
#print axioms observation_bound
#print axioms exists_weights_of_pairing_surjective
#print axioms odd_pairing_invariant
#print axioms exists_extended_weights
#print axioms pairingExtension_cartanMatrix
#print axioms restrictRouquierFamily
#print axioms restrictRouquierFamily_obj

example (μ : Bool → ℤ) (m : ℕ) :
    ∃ μp μm : (Bool → ℤ) × (Bool → ℤ), μm - μp = (μ, 0) ∧
      (∀ i, (pairingExtension ReservoirVacuumExamples.datum).h i μp = probeLevel μ m i) ∧
      (∀ i, (pairingExtension ReservoirVacuumExamples.datum).h i μm = reservoirLevel μ m i) :=
  exists_extended_weights ReservoirVacuumExamples.datum μ m

open OddMath.QuiverHecke
#check ReservoirVacuumExamples.recover_two_odd_series
#check ReservoirVacuumExamples.mixed_parity_detect
#check ReservoirVacuumExamples.crossing_window_injective
#check ReservoirVacuumExamples.crossing_two_exterior_ne_zero
#print axioms reservoirWindowCoordinates_apply
#print axioms exists_bounded_reservoir_extraction

example (f : ExtendedAtMost ReservoirVacuumExamples.datum ReservoirVacuumExamples.params
    [false, true] [true, false] 2) :
    reservoirWindowCoordinates ReservoirVacuumExamples.datum ReservoirVacuumExamples.params
      (fun _ => 5) [false, true] [true, false] 2
      ((ELVRelationSpan ReservoirVacuumExamples.datum ReservoirVacuumExamples.params
        (fun _ => 5) [false, true] [true, false]).mkQ f) = f :=
  reservoirWindowCoordinates_apply _ _ _ _ _ _ (N := 5) (fun _ => le_rfl) (by decide) f

#print axioms FusedFixedWeightFamily.upward_independence_at
#print axioms OddMath.SKM.reservoir_coefficients_recovered
#print axioms ReservoirVacuumEvaluation.normalized_bubbles
#print axioms ReservoirVacuumEvaluation.odd_bubble_vacuum
#print axioms ReservoirVacuumEvaluation.observe_coefficient
#print axioms FusedFixedWeightFamily.vacuum_evaluations_jointly_detect
#print axioms upward_independence_of_fused_fixed_weight_families
