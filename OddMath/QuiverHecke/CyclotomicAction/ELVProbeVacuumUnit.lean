import OddMath.QuiverHecke.CyclotomicAction.ELVUnitCoefficientRows
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSupport

/-! # An occupied vacuum probe append unit

The positive-level probe in `SwappedVacuumBubbles.md`, §1, is tested on
its canonical nonzero empty vector. The existing inverse unit matrix
splits the append unit; no new polynomial quotient presentation is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
namespace OddMath.QuiverHecke
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

variable [Fintype I] (m : I → ℕ)

omit [Fintype I] in
private theorem probeCutoff_pos (i : I) (hi : 0 < m i) : 0 < probeCutoff D m i := by
  change 0 < probeDotExponent D i * m i
  apply Nat.mul_pos _ hi
  unfold probeDotExponent
  split_ifs <;> decide

/-- The actual regular probe vacuum satisfies the required scalar-evaluation property. -/
theorem probeOldVacuumRegular_evaluates :
    ProbeEvaluatesCoefficients D m Sc [] (probeOldVacuumRegular D Sc m) :=
  probeOldModule_evaluatesCoefficients D m Sc [] _

end OddMath.QuiverHecke
