import OddMath.QuiverHecke.ReservoirCoverage
import OddMath.QuiverHecke.ReservoirVacuumExamples

/-! Concrete consumers of connected regular coordinates, corresponding to
`Categorification/KLR/CyclotomicAction/VacuumProduct.lean` and
`Categorification/KLR/Unfurling/GenericVacuumWordCoordinates.lean`.
This is the regular quotient stage, not an instance of the still-open fused
categorical family. -/
noncomputable section
namespace OddMath.QuiverHecke.ReservoirRegularExamples
open CategoryTheory
open ReservoirVacuumExamples ReservoirWeights

example : ∃ recover :
    ReservoirQuotient datum params (reservoirLevel (fun b => if b then 1 else 0) 3)
      [false, true] [true, false] →ₗ[ℚ]
    ReservoirQuotient datum params (reservoirLevel (fun b => if b then 1 else 0) 3)
      [false, true] [true, false],
    ∀ (a : SKM.SYM datum ℚ)
      (f : (pres datum params).obj (ob datum [false, true]) ⟶
        (pres datum params).obj (ob datum [true, false])),
      sourceCoefficientHom datum params a f ∈
        ExtendedAtMost datum params [false, true] [true, false] 3 →
      recover (reservoirPostcomp datum params (reservoirLevel (fun b => if b then 1 else 0) 3)
        (sourceCoefficientHom datum params 1 f)
        (reservoirPostcomp datum params (reservoirLevel (fun b => if b then 1 else 0) 3)
          (sourceCoefficientHom datum params a (𝟙 _))
          (reservoirRegularGenerator datum params
            (reservoirLevel (fun b => if b then 1 else 0) 3) [false, true]))) =
        (ELVRelationSpan datum params (reservoirLevel (fun b => if b then 1 else 0) 3)
          [false, true] [true, false]).mkQ (sourceCoefficientHom datum params a f) :=
  regularVacuumWindow_coordinates datum params (fun b => if b then 1 else 0) 3 _ _

/-- This regular cyclic action is nonzero on the crossing/exterior-product window. -/
example : ∃ f : coefficientObj datum params [false, true] ⟶
    coefficientObj datum params [true, false],
    reservoirPostcomp datum params (fun _ => 5) f
      (reservoirRegularGenerator datum params (fun _ => 5) [false, true]) ≠ 0 :=
  ⟨_, by simpa only [reservoirPostcomp_generator] using crossing_two_exterior_ne_zero⟩

#print axioms reservoirPostcomp_generator
#print axioms reservoirRegular_injective_on_window
#print axioms reservoirSourceOrder_source
#print axioms reservoirSourceOrder_involutive
#print axioms exists_reservoir_source_coordinates
#print axioms regularVacuumWindow_coordinates
#print axioms regularVacuumWindow_covers
#print axioms exists_regular_vacuum_window
#print axioms balanced_regular_vacuums_detect
end OddMath.QuiverHecke.ReservoirRegularExamples
