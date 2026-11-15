/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.TwoSector
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

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
