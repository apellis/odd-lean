/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendLeftCrossing

/-!
# The two-sided append corner decomposition on induced modules

For a left `Hn (n+1)`-module `M`, the decomposition `appendCornerEquiv` of the two-sided
append corner `ψ(1) Hn (n+2) ψ(1)` descends along the balanced tensor product
`Ind M = Hn (n+2) ψ(1) ⊗_(Hn (n+1)) M`: the `ψ(1)`-fixed part of `Ind M` is

`⊕_(j ≤ n, m) ψ'(1) M  ⊕  ⊕_m M`,

with `(j, m, y) ↦ ψ(c'_j x^m) τ ⊗ y` and `(m, y) ↦ z^m ⊗ y`. Both round trips use only
`appendCornerEquiv` and the right `ψ(Hn (n+1))`-linearity of its summand maps, not
flatness of `M`. This is the module form of the append-side Mackey decomposition of
`AppendCoordinates.md` §4 (Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Lemma 8.1,
mirror form).
-/

noncomputable section
open Categorification MulOpposite
namespace OddMath.QuiverHecke
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (n : ℕ) (M : Type w) [AddCommGroup M] [Module (Hn D Sc (n + 1)) M]
local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
local notation "C" => InductionAlong.Corner ψ
local notation "T" => InductionAlong.Ind M ψ

/-! ## Finite sums of elementary tensors along an additive family of corner elements -/

section Family
variable {ι : Type*} (Φ : (ι →₀ Hn D Sc (n + 1)) →+ Hn D Sc (n + 1 + 1))
  (hΦ : ∀ x, Φ x * appendAlgebra D Sc i (n + 1) 1 = Φ x)

/-- The family `Φ` with values in the right corner. -/
def appendFamilyCorner : (ι →₀ Hn D Sc (n + 1)) →+ C :=
  AddMonoidHom.codRestrict Φ _ hΦ

/-- `Σ_q Φ(single q 1) ⊗ y_q`. -/
def appendFamilyTensor : (ι →₀ M) →+ T :=
  Finsupp.liftAddHom fun q =>
    { toFun := fun y => InductionAlong.Ind.tmul
        (appendFamilyCorner D Sc i n Φ hΦ (Finsupp.single q 1)) y
      map_zero' := InductionAlong.Ind.tmul_zero _
      map_add' := InductionAlong.Ind.tmul_add _ }

end Family

/-! ## The two summand families -/

/-! ## Coordinates of a corner element -/

/-! ## The descent -/

end OddMath.QuiverHecke
