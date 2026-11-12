/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMonicPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVEndpointLeading
import Mathlib.Algebra.Polynomial.Div
/-! # Signed old-Hom division by the ordered endpoint–QP numerator

`endpointQP_top` and `endpointQP_above` assemble the actual unit highest action,
including the full old-Hom twist. `endpointQP_division` uses these statements
and finite support to divide every old-only append target by the prescribed
chronological numerator, leaving support strictly below its moving degree.
No arbitrary polynomial-evaluation multiplicativity or output S identity is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def endpointQPDegree (i : I) (v : List I) : ℕ := cutoff i +
  ((List.range v.length).map (fun b => appendQPDegree D i (v.getD b i))).sum

def appendQPProductUnit (i : I) (v : List I) : kˣ :=
  ((List.range v.length).map (fun b => appendQPUnit D Sc i (v.getD b i))).prod

end OddMath.QuiverHecke.ELVOld
