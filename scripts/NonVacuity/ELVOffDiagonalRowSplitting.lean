import NonVacuity.SerreComplex
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRowSplitting
import Lean.Util.CollectAxioms

noncomputable section
namespace OffDiagonalRowConsumer
open OddMath OddMath.QuiverHecke ELVOld
open NonVacuity.SerreComplex

def movingOdd : {i : Bool // datum.parity i = 1} := ⟨true, rfl⟩

/-- Connected mixed B2 data, with different source and target orders. -/
def mixedDivision :
    (offDiagonalBoundaryRowHigh datum scalars (fun _ => 3) movingOdd [true, false] [false, true] ×
      offDiagonalBoundaryRowWindow datum scalars (fun _ => 3) movingOdd [true, false] [false, true]) ≃ₗ[ℚ]
      (ℕ →₀ Old datum scalars (fun _ => 3) [true, false] [false, true]) :=
  offDiagonalBoundaryRowDivisionEquiv datum scalars (fun _ => 3) 0 movingOdd [true, false] [false, true]

example (f : ℕ →₀ Old datum scalars (fun _ => 3) [true, false] [false, true]) :
    mixedDivision (mixedDivision.symm f) = f :=
  mixedDivision.apply_symm_apply f

example (x : offDiagonalBoundaryRowHigh datum scalars (fun _ => 3) movingOdd [true, false] [false, true] ×
    offDiagonalBoundaryRowWindow datum scalars (fun _ => 3) movingOdd [true, false] [false, true]) :
    mixedDivision.symm (mixedDivision x) = x :=
  mixedDivision.symm_apply_apply x

theorem mixedPositiveHeight :
    outputSDegree datum true [true, false] ≤
      endpointQPDegree datum (fun _ => 3) true [true, false] := by
  have h := endpointQPDegree_sub_outputSDegree datum (fun _ => 3) true [true, false]
  norm_num [SKM.Datum.h, SKM.Datum.α, datum] at h ⊢
  omega

def mixedPositive :
    ((ℕ →₀ Old datum scalars (fun _ => 3) [true, false] [false, true]) ×
      offDiagonalBoundaryRowWindow datum scalars (fun _ => 3) movingOdd [true, false] [false, true]) ≃ₗ[ℚ]
      (ℕ →₀ Old datum scalars (fun _ => 3) [true, false] [false, true]) :=
  offDiagonalBoundaryPositiveEquiv datum scalars (fun _ => 3) 0 movingOdd
    [true, false] [false, true] mixedPositiveHeight

example (f : ℕ →₀ Old datum scalars (fun _ => 3) [true, false] [false, true]) :
    mixedPositive (mixedPositive.symm f) = f :=
  mixedPositive.apply_symm_apply f

/-- Repeated odd colour and an actual negative-height old-Hom row. -/
theorem mixedNegativeHeight :
    endpointQPDegree datum (fun _ => 1) true [true, true, false] ≤
      outputSDegree datum true [true, true, false] := by
  have h := endpointQPDegree_sub_outputSDegree datum (fun _ => 1) true [true, true, false]
  norm_num [SKM.Datum.h, SKM.Datum.α, datum] at h ⊢
  omega

def mixedNegative :
    (offDiagonalBoundaryKernelWindow datum scalars (fun _ => 1) movingOdd
      [true, true, false] [false, true, true] ×
      (ℕ →₀ Old datum scalars (fun _ => 1) [true, true, false] [false, true, true])) ≃ₗ[ℚ]
      (ℕ →₀ Old datum scalars (fun _ => 1) [true, true, false] [false, true, true]) :=
  offDiagonalBoundaryNegativeEquiv datum scalars (fun _ => 1) 0 movingOdd
    [true, true, false] [false, true, true] mixedNegativeHeight

example (f : ℕ →₀ Old datum scalars (fun _ => 1) [true, true, false] [false, true, true]) :
    mixedNegative (mixedNegative.symm f) = f :=
  mixedNegative.apply_symm_apply f

example (x : offDiagonalBoundaryKernelWindow datum scalars (fun _ => 1) movingOdd
    [true, true, false] [false, true, true] ×
    (ℕ →₀ Old datum scalars (fun _ => 1) [true, true, false] [false, true, true])) :
    mixedNegative.symm (mixedNegative x) = x :=
  mixedNegative.symm_apply_apply x

end OffDiagonalRowConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRowDivision,
    `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRowSplitting]
  for owner in owners do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} declarations in {owner}"
