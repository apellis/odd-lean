/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVSourcePolynomialRows

/-! # Polynomial rows as old-word idempotent summands

The concrete row insertion identifies the finite polynomial row module with
finite families in the right ideals `e(t) B[s]`. This uses the old-word matrix
idempotents themselves and allows zero corners and empty content.
-/

noncomputable section
open CategoryTheory MulOpposite
open scoped Classical DirectSum
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

end OddMath.QuiverHecke.ELVOld
