/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendQPTransport
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendNormRegularity
/-! # Highest append-PBW coefficients of the actual signed QP factors

`appendQPFactor_top` identifies the literal unit highest coefficient, including
disconnected colours and repeated-even signs. `appendQPFactor_above` proves
the accompanying degree bound. Finite maximal append support then proves
`appendProjection_qpProduct_regular` for the actual all-word ordered product.
These are direct append-side inputs to `DeformedBoundaryDivision.md` §3,
not a transported prepend regularity or the full reverse-chain norm.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def appendQPDegree (i j : I) : ℕ :=
  if j = i then if D.parity i = 1 then 2 else 0 else D.dn i j

def appendQPUnit (i j : I) : kˣ :=
  if j = i then if D.parity i = 1 then 1 else -1 else Sc.t i j

end OddMath.QuiverHecke.ELVOld
