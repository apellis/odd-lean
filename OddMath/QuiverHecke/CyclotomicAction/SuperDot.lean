/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LastDot
import OddMath.QuiverHecke.CyclotomicAction.SuperInduction
import StringDiagrams.Super.Functor

/-!
# The homogeneous dot on cyclotomic superinduction

Ports the dot construction of `Categorification/KLR/CyclotomicAction/Induction.lean`
using the last-dot relation from `CyclotomicAction/Slides.lean`.
For the signed-left, ordinary-right superbimodule convention the corner map is
`x ↦ (-1)^{|i||x|} x c`, not unsigned right multiplication by the last dot `c`.
No square, braid or KKO relation is asserted here.
-/

noncomputable section
open CategoryTheory StringDiagrams
open Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => inductionCorner D Sc i a ha n
local notation "GB" => cyclotomicParity D Sc a ha (n + 1)
local notation "GA" => cyclotomicParity D Sc a ha n
local notation "c" => cyclotomicLastDot D Sc i a n
local notation "d" => D.parity i

private theorem dot_mul_mem (x : CyclotomicAlgebra D Sc a (n + 1))
    (_hx : x ∈ inductionCornerSubmodule D Sc i a n) :
    x * c ∈ inductionCornerSubmodule D Sc i a n := by
  change (x * c) * cyclotomicAppend D Sc i a n 1 = x * c
  rw [mul_assoc, (cyclotomicLastDot_corner D Sc i a n).2]

end OddMath.QuiverHecke
