/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightAdjunction
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightCrossing

/-!
# The Rouquier mate kernel at one height

Write `A`, `B`, `C` for the deformed cyclotomic algebras at heights `n`, `n + 1`, `n + 2` of
the extended tower, `φ : A → B` and `φ₂ : B → C` for the strand maps of colour `i`, and
`τ ∈ C` for the crossing of the last two `i`-strands. The induction and restriction corners
`P₁ = B e`, `Q₁ = e B`, `P₂ = C e₂`, `Q₂ = e₂ C` are those of `GlobalHeightAdjunction`.

This file constructs the kernel of the Rouquier mate on these corners,
`s : B e ⊗_A e B → e₂ C ⊗_C C e₂`, `x ⊗ y ↦ -(-1)^{p|x|} φ₂(x) τ φ₂(y) ⊗ e₂`,
where `p = |i|`. It is the descended source map `s = -F̄ J` of display (2) in
`docs/Nondegeneracy/DeformedMatrixComparison.md`: `J(x ⊗ y) = (-1)^{p|x|} x ⊗ π^p y` carries
the Koszul sign and `F̄` multiplies through the crossing. The construction uses only the
signed intertwining relation `φ₂(φ r) τ = (-1)^{p|r|} τ φ₂(φ r)` of the crossing
(`heightLastCrossing_intertwines` with `j = i`).

## Main declarations

* `rouquierMateKernel`: the superbimodule morphism `tensor P₁ Q₁ ⟶ tensor Q₂ P₂`.
* `rouquierMateKernel_parity`: it has parity `|i|`.
* `rouquierMateKernel_apply`: its value on homogeneous elementary tensors.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open SuperBimodule
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "C₂" => heightAlgebra D Sc a (n + 1 + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "GB" => heightParity D Sc a ha (n + 1)
local notation "GC" => heightParity D Sc a ha (n + 1 + 1)
local notation "φ₁" => heightAppend D Sc a i n
local notation "φ₂" => heightAppend D Sc a i (n + 1)
local notation "τ" => heightLastCrossing D Sc a i i n
local notation "P₁" => heightInductionCorner D Sc i a ha n
local notation "Q₁" => heightRestrictionCorner D Sc i a ha n
local notation "P₂" => heightInductionCorner D Sc i a ha (n + 1)
local notation "Q₂" => heightRestrictionCorner D Sc i a ha (n + 1)
local notation "p" => D.parity i

end OddMath.QuiverHecke.CyclotomicAction
