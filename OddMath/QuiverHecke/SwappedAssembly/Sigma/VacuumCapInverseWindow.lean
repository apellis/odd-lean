/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.PositiveVacuumWindow
import OddMath.QuiverHecke.SwappedAssembly.Sigma.VacuumInverseWindow

/-! # The chosen cap inverse on the supported vacuum sector at positive height

Positive-height counterpart of `vacuumCupInverseData`, toward Brundan–Ellis,
*Super Kac–Moody 2-categories*, §8 (research issue #345). At formal content zero
the reservoir source and probe target are absent, so the actual positive augmented
inverse supplies a cap-window inverse of the surviving positive mixed bend
`centralPaddedSigma true false`. Its windows are the native probe cap rows
`centralPaddedCap true n`, `n < h`, and its principal entry and inverse columns are
the literal entries of the inverse of the prescribed positive factor matrix.
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
local instance vacuumCapInverseHomPi (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

/-- The positive augmented window has exactly the expected `P-N` slots. -/
theorem vacuum_positive_window_length (i : I) :
    (D.h i ((P).wt (0,0))).toNat = probeCutoff D m i - cutoff i := by
  rw [vacuum_height_eq]
  omega

/-- The specified inverse of the positive mixed bend and its native
probe cap rows, extracted from the actual positive factor matrix. -/
def vacuumCapInverseData [Finite I] [Fact Sc.PureNilpotent]
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)
    (hwin : ReservoirWindowIdeal D Sc m cutoff bound ΛP ΛR hP hR) (i : I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR (0,0))
    (β : WeightBlocks D ΛR ((P).muM (0,0)))
    (hh : 0 ≤ D.h i ((P).wt (0,0))) :
    CapInverseData (O := (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR (0,0) β).obj Z.obj)
      ((P).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot)
        i (0,0) Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR (0,0) β) true false)
      (fun n : Fin (D.h i ((P).wt (0,0))).toNat => (P).centralPaddedCap i (0,0) Z.obj
        (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR (0,0) β) true n) := by
  let E := reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR (0,0) β
  let c := elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot
  letI : IsIso (posMap
      ((P).centralPaddedSigma c i (0,0) Z.obj E false false)
      ((P).centralPaddedSigma c i (0,0) Z.obj E true true)
      ((P).centralPaddedSigma c i (0,0) Z.obj E false true)
      ((P).centralPaddedSigma c i (0,0) Z.obj E true false)
      ((P).centralPaddedCap i (0,0) Z.obj E false)
      (fun n : Fin (D.h i ((P).wt (0,0))).toNat => (P).centralPaddedCap i (0,0) Z.obj E true n)) :=
    (centralFactorMatrix_content_isIsoOf D Sc m cutoff bound ΛP ΛR hP hR hdot hwin i (0,0) Z β).1 hh
  refine ⟨_, _, posMap_isCapInverse_of_zero_corners
    ((P).centralPaddedSigma c i (0,0) Z.obj E false false)
    ((P).centralPaddedSigma c i (0,0) Z.obj E true true)
    ((P).centralPaddedSigma c i (0,0) Z.obj E false true)
    ((P).centralPaddedSigma c i (0,0) Z.obj E true false)
    ((P).centralPaddedCap i (0,0) Z.obj E false)
    (fun n : Fin (D.h i ((P).wt (0,0))).toNat => (P).centralPaddedCap i (0,0) Z.obj E true n)
    ?_ ?_⟩
  · have hn : ¬StepValid (up i) false ((0,0) : Sector I) := by simp [StepValid]
    simpa only [sectorFamilyCorner, dite_eq_right hn] using Limits.isZero_zero _
  · have hn : ¬StepValid (dn i) true ((0,0) : Sector I) := by simp [StepValid]
    simpa only [sectorFamilyCorner, dite_eq_right hn] using Limits.isZero_zero _

/-- The finite inverse columns are precisely the columns of the inverse of
the actual positive factor matrix, with no scalar or sign inserted. -/
theorem vacuumCapInverseData_window [Finite I] [Fact Sc.PureNilpotent]
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)
    (hwin : ReservoirWindowIdeal D Sc m cutoff bound ΛP ΛR hP hR) (i : I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR (0,0))
    (β : WeightBlocks D ΛR ((P).muM (0,0)))
    (hh : 0 ≤ D.h i ((P).wt (0,0))) (n : Fin (D.h i ((P).wt (0,0))).toNat) :
    let _ := (centralFactorMatrix_content_isIsoOf D Sc m cutoff bound ΛP ΛR hP hR hdot hwin i (0,0) Z β).1 hh
    (vacuumCapInverseData D Sc m cutoff bound ΛP ΛR hP hR hdot hwin i Z β hh).window n =
      inv ((P).augPosFactorMatrix (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot)
        i ((P).wt (0,0)) (0,0) Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR (0,0) β))
          (some (some n)) (some none) := rfl

/-- The chosen principal entry is the `(probe source, reservoir target)` entry
of the inverse of the actual positive factor matrix. -/
theorem vacuumCapInverseData_principal [Finite I] [Fact Sc.PureNilpotent]
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)
    (hwin : ReservoirWindowIdeal D Sc m cutoff bound ΛP ΛR hP hR) (i : I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR (0,0))
    (β : WeightBlocks D ΛR ((P).muM (0,0)))
    (hh : 0 ≤ D.h i ((P).wt (0,0))) :
    let _ := (centralFactorMatrix_content_isIsoOf D Sc m cutoff bound ΛP ΛR hP hR hdot hwin i (0,0) Z β).1 hh
    (vacuumCapInverseData D Sc m cutoff bound ΛP ΛR hP hR hdot hwin i Z β hh).principal =
      inv ((P).augPosFactorMatrix (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot)
        i ((P).wt (0,0)) (0,0) Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR (0,0) β))
          none (some none) := rfl

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
