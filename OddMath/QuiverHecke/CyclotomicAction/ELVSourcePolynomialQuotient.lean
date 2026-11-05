/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVSourceSplitting
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryPolynomial

/-! # Polynomial quotient of the prescribed source column

The source cokernel in `DeformedMackeyBoundary.md` is identified with the
existing long polynomial coordinates. The prescribed P induces the existing
odd polynomial boundary on this quotient. No crossing-column injectivity,
bimodule naturality or inverse categorical matrix is assumed or asserted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
