import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingStoredLocal
import OddMath.SKM.RouquierInverseRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapUniqueness

/-! # The stored probe cap in the full OLD coefficient coordinates

SwappedActionAssembly F2: the missing-colour inverse cap is the
prescribed boundary coefficient, transported through the even upper-loop
chart. All module components and full OLD coefficients are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ : List I} (h : (i :: γ).Perm μ) (hi : i ∉ γ)
local notation "count" => contentUnitCount D (probeCutoff D m) i (γ : Multiset I)
local notation "L" => probeMissingStoredLoc D Sc m γ i h hi
local notation "V" => probeMissingStoredCoefficients D Sc m γ i h hi

/-- The raw stored local cap is the top boundary coefficient, with no
normalization scalar inserted. -/
theorem probeMissingStoredLoc_cap_eq (hn : 0 < count) : (L).capL = (V).cap := by
  have hcount : (count : ℤ) = contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) :=
    contentUnitCount_cast D (probeCutoff D m) i (γ : Multiset I)
      (contentCrossingHeight_nonneg_of_not_mem D (probeCutoff D m) γ i hi)
  apply (V).hom_ext
  intro n hnc
  have hh : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) < 0 := by omega
  have hw := (L).cupD_capL hh (n := n) (by omega)
  have he : (- -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) - 1).toNat = count - 1 := by omega
  calc
    _ = if n = count - 1 then 𝟙 _ else 0 := by
      simpa only [he, SKM.SuperRouquierLoc.cupD, SKM.RouquierBoundary.cup] using hw
    _ = _ := ((V).cup_cap hn hnc).symm

/-- The explicit selected upper-loop chart transports the stored cap to
the un-reindexed evaluated OLD boundary cap. -/
theorem probeMissingStoredLoc_cap_chart (hn : 0 < count) :
    (L).capL = (probeAppendUpperLoopSuperIso D Sc m γ i h).inv ≫
      (probeEvaluatedMissingCoefficients D Sc m γ i hi).cap := by
  rw [probeMissingStoredLoc_cap_eq D Sc m γ i h hi hn]
  simp only [SKM.RouquierBoundary.Coefficients.cap, hn, ite_true]
  rfl

/-- On the original regular probe, the full OLD boundary cap is precisely
its prescribed native vacuum cap. The finite moments are proved from the
constructed boundary inverse. -/
theorem probeMissingBoundary_regular_cap [Fintype I]
    (hP : 0 < probeCutoff D m i) :
    (contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)).cap.total
      (probeOldVacuumRegular D Sc m) = ProbeVacuumCap.cap D Sc m i hP := by
  apply ProbeVacuumCap.cap_eq_of_unitDot_window D Sc m i hP
  intro a ha
  let W := contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)
  have hp : 0 < contentUnitCount D (probeCutoff D m) i (([] : List I) : Multiset I) := by
    simpa only [VacuumCoefficient.count] using hP
  have hw := W.cup_cap hp (j := a) (by simpa only [VacuumCoefficient.count] using ha)
  have ht := congrArg (fun η => η.total (probeOldVacuumRegular D Sc m)) hw
  rw [Superfunctor.comp_total] at ht
  have hu : (SKM.RouquierBoundary.cup
      (inductionModuleAdjunction (k := k) (oldContentAppend D Sc (probeCutoff D m) [] i))
      (inductionModuleDot (oldContentAppend D Sc (probeCutoff D m) [] i)
        (oldContentAppendDot_supernatural D Sc (probeCutoff D m) [] i)) a).total
          (probeOldVacuumRegular D Sc m) =
      unitDotColumn (oldContentAppend D Sc (probeCutoff D m) [] i)
        (probeOldContentAppendDot_supernatural D Sc m [] i) (probeOldVacuumRegular D Sc m) a := by
    rw [inductionModuleUnitPower_eq, gridUnitColumnTransformation_total]
  rw [hu] at ht
  by_cases he : a + 1 = probeCutoff D m i
  · have he' : a = contentUnitCount D (probeCutoff D m) i (([] : List I) : Multiset I) - 1 := by
      rw [VacuumCoefficient.count]; omega
    rw [ite_eq_left he'] at ht
    exact (ht.trans (SuperNatTrans.id_total
      (𝟭 (Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k)))
      (probeOldVacuumRegular D Sc m))).trans (ite_eq_left he).symm
  · have he' : a ≠ contentUnitCount D (probeCutoff D m) i (([] : List I) : Multiset I) - 1 := by
      rw [VacuumCoefficient.count]; omega
    rw [ite_eq_right he'] at ht
    simpa only [SuperNatTrans.total, Superfunctor.zero_app, zero_add, ite_eq_right he] using ht

end OddMath.QuiverHecke
