/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMonicPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVEndpointLeading
import Mathlib.Algebra.Polynomial.Div

/-! # Ordered endpoint–QP numerator normalization

The polynomial here uses append QP factors, not full reverse-chain norm factors.
Its endpoint factor is kept on the left in endomorphism multiplication.
This is the numerator for the right-division step of
`DeformedBoundaryDivision.md` §3 and §5.
-/
noncomputable section
open CategoryTheory Polynomial
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

end OddMath.QuiverHecke.ELVOld
