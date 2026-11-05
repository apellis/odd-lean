/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.RouquierMateKernel
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightDot

/-!
# Dotted cup and cap kernels at one height

Write `A`, `B` for the deformed cyclotomic algebras at heights `n`, `n + 1` of the extended
tower, `φ : A → B` for the strand map of colour `i`, `e = φ(1)`, `P = B e`, `Q = e B` for the
induction and restriction corners of `GlobalHeightAdjunction`, `x ∈ B` for the last dot and
`p = |i|`. This file constructs the kernels of display (2)/(4) of
`docs/Nondegeneracy/DeformedMatrixComparison.md` without the normalizing signs `d_k`:

* the dotted cup `j_k : A ⟶ e B ⊗_B B e`, `a ↦ x^k φ(a) ⊗ e` (so `u_k = d_k j_k`);
* the dotted cap `κ_k : B e ⊗_A e B ⟶ B`, `y ⊗ z ↦ (-1)^{kp|y|} y x^k z`
  (so `c_k = d_k κ_k`).

In the Rouquier mate at the weight steps `x₀ → x₁ → x₂` the dotted cup is used for the
second step (at one height higher than the cap), so both kernels are stated at one level `n`.
Both are superbimodule morphisms of parity `k p`. The only input is the signed commutation
`φ(r) x = (-1)^{p|r|} x φ(r)` of the last dot (`heightLastDot_comm`), iterated in
`heightAppend_mul_heightLastDot_pow`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open SuperBimodule
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
  (m : ℕ)

local notation "A₀" => heightAlgebra D Sc a n
local notation "B₁" => heightAlgebra D Sc a (n + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "GB" => heightParity D Sc a ha (n + 1)
local notation "φ₁" => heightAppend D Sc a i n
local notation "x₁" => heightLastDot D Sc a i n
local notation "P₁" => heightInductionCorner D Sc i a ha n
local notation "Q₁" => heightRestrictionCorner D Sc i a ha n
local notation "p" => D.parity i
local notation "kp" => ((m : ZMod 2) * D.parity i)

/-! ### The dotted cup -/

/-! ### The dotted cap -/

end OddMath.QuiverHecke.CyclotomicAction
