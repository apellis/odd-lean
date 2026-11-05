import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.VacuumWindow
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedResidualInversion

/-! # The chosen unit inverse on the supported vacuum sector

SwappedVacuumNonpositiveBubbles §1 (2) and §4 (13): at formal content
zero the reservoir source and probe target are absent. The actual
negative augmented inverse therefore supplies a unit-window inverse of
the surviving positive mixed bend. Its finite cap rows have no extra
minus; only its inverse principal changes sign. The inverse comparison
square retains the original augmented matrix and all its path indices.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld ProbeWindow
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local instance vacuumInverseHomPi (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

/-- The formal vacuum height is the difference of the prescribed levels. -/
theorem vacuum_height_eq (i : I) : D.h i ((P).wt (0,0)) =
    (probeCutoff D m i : ℤ) - cutoff i := by
  change D.h i ((ΛP - contentWeight D 0) + (-ΛR + contentWeight D 0)) = _
  simp only [map_zero, sub_zero, add_zero, map_add, map_neg]
  change D.h i ΛP + -D.h i ΛR = _
  rw [← hP i, ← hR i]
  rfl

/-- The negative augmented window has exactly the expected `N-P` slots. -/
theorem vacuum_negative_window_length (i : I) :
    (-D.h i ((P).wt (0,0))).toNat = cutoff i - probeCutoff D m i := by
  rw [vacuum_height_eq]
  omega

/-- The specified inverse of the positive mixed bend and its native
reservoir unit columns, extracted from the actual negative matrix. -/
def vacuumCupInverseData [Finite I]
    (sy : Symmetrizer D) (hc : Sc.Homogeneous) (i : I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR (0,0))
    (β : WeightBlocks D ΛR ((P).muM (0,0)))
    (hh : D.h i ((P).wt (0,0)) ≤ 0) :
    CupInverseData (O := (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR (0,0) β).obj Z.obj)
      ((P).centralPaddedSigma (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
        i (0,0) Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR (0,0) β) true false)
      (fun n : Fin (-D.h i ((P).wt (0,0))).toNat => (P).centralPaddedUnit i (0,0) Z.obj
        (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR (0,0) β) false n) := by
  let E := reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR (0,0) β
  let c := elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc
  letI : IsIso (negMap
      (-((P).centralPaddedSigma c i (0,0) Z.obj E false false))
      (-((P).centralPaddedSigma c i (0,0) Z.obj E true true))
      (-((P).centralPaddedSigma c i (0,0) Z.obj E false true))
      (-((P).centralPaddedSigma c i (0,0) Z.obj E true false))
      ((P).centralPaddedUnit i (0,0) Z.obj E false)
      (fun n : Fin (-D.h i ((P).wt (0,0))).toNat => (P).centralPaddedUnit i (0,0) Z.obj E true n)) :=
    (centralFactorMatrix_content_isIso D Sc m cutoff bound ΛP ΛR hP hR sy hc i (0,0) Z β).2 hh
  refine negMapCupInverseData ((P).centralPaddedSigma c i (0,0) Z.obj E false false)
    ((P).centralPaddedSigma c i (0,0) Z.obj E true true)
    ((P).centralPaddedSigma c i (0,0) Z.obj E false true)
    ((P).centralPaddedSigma c i (0,0) Z.obj E true false)
    ((P).centralPaddedUnit i (0,0) Z.obj E false)
    (fun n : Fin (-D.h i ((P).wt (0,0))).toNat => (P).centralPaddedUnit i (0,0) Z.obj E true n) ?_ ?_
  · have hn : ¬StepValid (up i) false ((0,0) : Sector I) := by simp [StepValid]
    simpa only [sectorFamilyCorner, dite_eq_right hn] using Limits.isZero_zero _
  · have hn : ¬StepValid (dn i) true ((0,0) : Sector I) := by simp [StepValid]
    simpa only [sectorFamilyCorner, dite_eq_right hn] using Limits.isZero_zero _

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
