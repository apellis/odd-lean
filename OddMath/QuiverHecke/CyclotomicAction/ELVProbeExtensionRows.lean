import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitCoefficientRows
import OddMath.QuiverHecke.CyclotomicAction.ELVFullyFaithfulInduction

/-! # Ground-valued inverse rows of the extended regular probe

The probe side of `SwappedVacuumNonpositiveBubbles.md`, §2, needs the
last inverse unit-matrix row with scalar target. We specialize the prescribed
full-old inverse row to the canonical extension of the regular probe,
using its literal empty scalar coordinate and fully faithful inclusion unit.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ProbeExtensionCoefficient
open BalancedInduction CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "M" => probeOldVacuumRegular D Sc m
local notation "s" => probeOldVacuumObject D Sc m
local notation "J" => oldContentInclusion D Sc cut []
local notation "L" => induced J M
local notation "t" => OldContentCategory.obj (probeOldVacuumObject D Sc m)


omit [Fintype I] in
private theorem height (i : I) :
    0 ≤ contentCrossingHeight D cut i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

private def topSlot (i : I) (hN : 0 < cut i) :
    Fin (contentUnitCount D cut i (([] : List I) : Multiset I)) :=
  ⟨cut i - 1, by rw [VacuumCoefficient.count]; omega⟩

/-- Scalar insertion into the canonical full old extension of the regular probe. -/
def scalarUnit : k →ₗ[k] (L).obj t :=
  (unit J (M).toFunctor s).comp (probeVacuumScalarEquiv D Sc m).toLinearMap

/-- Decode the same empty component, using the inverse of the prescribed
fully faithful inclusion unit and the original empty scalar coordinate. -/
def scalarCoordinate : (L).obj t →ₗ[k] k :=
  (probeVacuumScalarEquiv D Sc m).symm.toLinearMap.comp
    (fullyFaithfulUnitInverse J (M).toFunctor s)

/-- The two empty-coordinate maps retain the original scalar normalization. -/
theorem scalarCoordinate_unit (c : k) :
    scalarCoordinate D Sc m (scalarUnit D Sc m c) = c := by
  have h := LinearMap.congr_fun (fullyFaithfulUnitInverse_unit J (M).toFunctor s)
    (probeVacuumScalarEquiv D Sc m c)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  change (probeVacuumScalarEquiv D Sc m).symm
    (fullyFaithfulUnitInverse J (M).toFunctor s
      (unit J (M).toFunctor s (probeVacuumScalarEquiv D Sc m c))) = c
  rw [h]
  exact (probeVacuumScalarEquiv D Sc m).symm_apply_apply c

/-- The literal last old inverse row with its output decoded in the ground ring. -/
def functional (i : I) (hN : 0 < cut i) :
    mateTargetSpace D Sc cut i L t →ₗ[k] k :=
  (scalarCoordinate D Sc m).comp
    (moduleUnitCoefficient D Sc cut L i t (height D m i) (topSlot D m i hN))

/-- The prescribed extraction window, on every scalar input, before
restricting to fixed content. -/
theorem functional_dot_window (i : I) (hN : 0 < cut i)
    (a : ℕ) (ha : a < cut i) (c : k) :
    functional D Sc m i hN
      (((actualInductionDot D Sc cut i L ((append D Sc cut i).obj t)) ^ a)
        (unit (append D Sc cut i) (L).toFunctor t (scalarUnit D Sc m c))) =
      if a + 1 = cut i then c else 0 := by
  have h := moduleUnitCoefficient_dot_window D Sc cut L i t (height D m i)
    (topSlot D m i hN) a (by
      change a < contentUnitCount D cut i (([] : List I) : Multiset I)
      simpa only [VacuumCoefficient.count] using ha)
    (scalarUnit D Sc m c)
  change moduleUnitCoefficient D Sc cut L i t (height D m i) (topSlot D m i hN)
    (((actualInductionDot D Sc cut i L ((append D Sc cut i).obj t)) ^ a)
      ((((adjunctionUnit (append D Sc cut i)).app L).total t) (scalarUnit D Sc m c))) =
    if a = (topSlot D m i hN).val then scalarUnit D Sc m c else 0 at h
  rw [adjunctionUnit_total_apply] at h
  change moduleUnitCoefficient D Sc cut L i t (height D m i) (topSlot D m i hN)
    (((actualInductionDot D Sc cut i L ((append D Sc cut i).obj t)) ^ a)
      (unit (append D Sc cut i) (L).toFunctor t (scalarUnit D Sc m c))) =
    if a = cut i - 1 then scalarUnit D Sc m c else 0 at h
  change scalarCoordinate D Sc m _ = _
  rw [h]
  have he : (a = cut i - 1) ↔ a + 1 = cut i := by omega
  by_cases hh : a + 1 = cut i
  · rw [ite_eq_left (he.mpr hh), ite_eq_left hh, scalarCoordinate_unit]
  · rw [ite_eq_right (fun hEq => hh (he.mp hEq)), ite_eq_right hh, map_zero]


end OddMath.QuiverHecke.ELVOld.ProbeExtensionCoefficient
