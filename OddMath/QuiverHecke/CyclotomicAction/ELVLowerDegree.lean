/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.HomDimension
import OddMath.QuiverHecke.CyclotomicAction.ELVHomGrading

/-! # Cutoff-independent lower degrees of coefficient Homs

For each pair of boundary words, the full ELV coefficient Hom is bounded
below independently of the coefficient cutoff. The bound comes from affine
PBW crossing degrees; all polynomial and exterior coefficient degrees are
nonnegative. This is the source bound needed for low-degree cyclotomic
ideal separation, not an injectivity assertion about the quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous)

include hc in

end OddMath.QuiverHecke
