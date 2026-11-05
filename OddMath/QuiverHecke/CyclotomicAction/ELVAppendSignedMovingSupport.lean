/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendMovingSupport
/-! # Signed append moving powers in every degree

The actual append moving power shifts finite append-PBW support and twists
the entire old-Hom coefficient by its parity. No even-power hypothesis is
imposed. These signed top and support formulas supply the odd-cutoff step
in the literal endpoint ELV polynomial normalization of
`DeformedBoundaryDivision.md` §3.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

end OddMath.QuiverHecke.ELVOld
