/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.RouquierCupCapKernel
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightCrossing

/-!
# The dotted unit, dotted counit and Rouquier mate through the kernels, at one height

Write `A`, `B`, `C` for the deformed cyclotomic algebras at heights `n`, `n + 1`, `n + 2`,
`P = B e`, `Q = e B` for the induction and restriction corners of colour `i` at height `n`,
`P₂`, `Q₂` for those at height `n + 1`, `x` for the last dot and `p = |i|`. The functor-level
data of the Rouquier interface, evaluated on a module `M`, factor through the kernels of
`RouquierCupCapKernel` and `RouquierMateKernel` tensored with `M`:

* the `m`-th power of the dot on `P` (`heightInductionDotPow`) is
  `y ↦ (-1)^{m p |y|} d_m y x^m`, with `d_m = (-1)^{p (m choose 2)}` (`rouquierDotSign`);
* the dotted unit `M → Q ⊗ P ⊗ M`, the unit followed by the `m`-th dot power, is
  `d_m` times the dotted cup `j_m ⊗ M` (`heightSuperUnit_dotPow`);
* the dotted counit `P ⊗ Q ⊗ M → M`, the `m`-th dot power followed by the counit, is
  `d_m` times the dotted cap `κ_m ⊗ M` (`heightDotPow_superCounit`);
* the mate `P ⊗ Q ⊗ M → Q₂ ⊗ P₂ ⊗ M`, unit at height `n + 1`, then the crossing `ψ`, then the
  counit at height `n`, is minus the mate kernel `s ⊗ M` (`heightRouquierMate_eq`). For the
  signed crossing `-ψ` of `globalRouquierData` it is `s ⊗ M`.

These are the height-level forms of the identifications `u_m = d_m j_m`, `c_m = d_m κ_m`
and of the mate kernel in display (2)/(4) of `docs/Nondegeneracy/DeformedMatrixComparison.md`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open SuperBimodule
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v

/-- The normalizing sign `d_m = (-1)^{p (m choose 2)}` of the `m`-th dot power. -/
def rouquierDotSign (p : ZMod 2) : ℕ → ℤ
  | 0 => 1
  | m + 1 => rouquierDotSign p m * koszulSign p (m : ZMod 2)

variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "A₀" => heightAlgebra D Sc a n
local notation "B₁" => heightAlgebra D Sc a (n + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "GB" => heightParity D Sc a ha (n + 1)
local notation "φ₁" => heightAppend D Sc a i n
local notation "φ₂" => heightAppend D Sc a i (n + 1)
local notation "x₁" => heightLastDot D Sc a i n
local notation "P₁" => heightInductionCorner D Sc i a ha n
local notation "Q₁" => heightRestrictionCorner D Sc i a ha n
local notation "P₂" => heightInductionCorner D Sc i a ha (n + 1)
local notation "Q₂" => heightRestrictionCorner D Sc i a ha (n + 1)
local notation "p" => D.parity i

/-! ### Powers of the dot on the induction corner -/

/-- The `m`-th power of the dot on `P = B e`, in the order of `SKM.rouquierPower`. -/
def heightInductionDotPow : ℕ → (P₁ ⟶ P₁)
  | 0 => 𝟙 P₁
  | m + 1 => heightInductionDotPow m ≫ heightInductionSuperDot D Sc i a ha n

/-! ### The dotted unit and the dotted counit -/

/-! ### The Rouquier mate -/

end OddMath.QuiverHecke.CyclotomicAction
