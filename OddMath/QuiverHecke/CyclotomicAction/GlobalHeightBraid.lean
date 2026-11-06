/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightBlockCross
import OddMath.QuiverHecke.CyclotomicAction.GlobalSlideAlgebra
import OddMath.QuiverHecke.CyclotomicAction.Square
import OddMath.QuiverHecke.MixedRelations

/-!
# The equal-colour braid on three inductions at every height

The module half of the same-colour braid relation of
`Categorification/KLR/CyclotomicAction/GlobalBraid.lean` (`globalCross_sameBraid`), at a fixed
height of the extended tower. With `t₁` the crossing of the two inner inductions under the
outer induction and `t₂` the crossing of the two outer inductions,

  `t₂ ≫ t₁ ≫ t₂ = t₁ ≫ t₂ ≫ t₁`

on every module (`heightSuperInduction_braid_same`).

Every element of a balanced tensor `P ⊗ N` with `P` an induction corner is the action of
an algebra element on `e ⊗ N`, with `e` the colour-cut idempotent
(`heightInductionCorner_btmul_eq_lact`), and the idempotent can be moved past the action
of the lower algebra (`heightInductionCorner_btmul_lact`). On `e ⊗ e ⊗ N` the crossing acts
by left multiplication by the last-pair crossing (`heightSuperInductionCrossing_idempotent`);
the braid then follows from `heightLastCrossing_braid_same`, the signs on the two sides
agreeing term by term.
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

section Corner
variable (n : ℕ)

local notation "P" => heightInductionCorner D Sc i a ha n
local notation "e" => heightInductionCornerIdempotent D Sc i a ha n
local notation "φ" => heightAppend D Sc a i n

end Corner

section Crossing
variable (n : ℕ)

local notation "P₀" => heightInductionCorner D Sc i a ha n
local notation "P₁" => heightInductionCorner D Sc i a ha (n + 1)
local notation "e₀" => heightInductionCornerIdempotent D Sc i a ha n
local notation "e₁" => heightInductionCornerIdempotent D Sc i a ha (n + 1)
local notation "d" => D.parity i * D.parity i

end Crossing

section Braid
variable (n : ℕ)

local notation "P₀" => heightInductionCorner D Sc i a ha n
local notation "P₁" => heightInductionCorner D Sc i a ha (n + 1)
local notation "P₂" => heightInductionCorner D Sc i a ha (n + 1 + 1)
local notation "e₀" => heightInductionCornerIdempotent D Sc i a ha n
local notation "e₁" => heightInductionCornerIdempotent D Sc i a ha (n + 1)
local notation "e₂" => heightInductionCornerIdempotent D Sc i a ha (n + 1 + 1)
local notation "d" => D.parity i * D.parity i
local notation "φ₁" => heightAppend D Sc a i (n + 1)
local notation "φ₂" => heightAppend D Sc a i (n + 1 + 1)

end Braid

end OddMath.QuiverHecke.CyclotomicAction
