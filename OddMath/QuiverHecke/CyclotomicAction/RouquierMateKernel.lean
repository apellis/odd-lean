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

/-- The algebra element `-φ₂(sgn x) τ φ₂(y)` underlying the mate kernel. -/
def rouquierMateKernelElement (x : (P₁).toSVec) (y : (Q₁).toSVec) : C₂ :=
  -(φ₂ ((P₁).toSVec.sgn p x).val * τ * φ₂ y.val)

theorem rouquierMateKernelElement_left (x : (P₁).toSVec) (y : (Q₁).toSVec) :
    φ₂ 1 * rouquierMateKernelElement D Sc i a ha n x y =
      rouquierMateKernelElement D Sc i a ha n x y := by
  unfold rouquierMateKernelElement
  rw [mul_neg, ← mul_assoc, ← mul_assoc, ← map_mul, one_mul]

/-- The kernel element as an element of the upper restriction corner `e₂ C`. -/
def rouquierMateKernelCorner (x : (P₁).toSVec) (y : (Q₁).toSVec) : (Q₂).toSVec :=
  ⟨rouquierMateKernelElement D Sc i a ha n x y, rouquierMateKernelElement_left D Sc i a ha n x y⟩

/-- The kernel is bilinear in the two corner factors. -/
def rouquierMateKernelBi : (P₁).toSVec →ₗ[k] (Q₁).toSVec →ₗ[k] (Q₂).toSVec where
  toFun x :=
    { toFun := fun y => rouquierMateKernelCorner D Sc i a ha n x y
      map_add' := fun y z => by
        apply Subtype.ext
        change -(_ * _ * φ₂ (y.val + z.val)) = -(_ * _ * φ₂ y.val) + -(_ * _ * φ₂ z.val)
        rw [map_add, mul_add, neg_add]
      map_smul' := fun c y => by
        apply Subtype.ext
        change -(_ * _ * φ₂ (c • y.val)) = c • -(_ * _ * φ₂ y.val)
        rw [map_smul, mul_smul_comm, smul_neg] }
  map_add' x y := by
    ext z
    apply Subtype.ext
    change -(φ₂ ((P₁).toSVec.sgn p (x + y)).val * _ * _) =
      -(φ₂ ((P₁).toSVec.sgn p x).val * _ * _) + -(φ₂ ((P₁).toSVec.sgn p y).val * _ * _)
    rw [map_add]
    change -(φ₂ (((P₁).toSVec.sgn p x).val + ((P₁).toSVec.sgn p y).val) * _ * _) = _
    rw [map_add, add_mul, add_mul, neg_add]
  map_smul' c x := by
    ext z
    apply Subtype.ext
    change -(φ₂ ((P₁).toSVec.sgn p (c • x)).val * _ * _) =
      c • -(φ₂ ((P₁).toSVec.sgn p x).val * _ * _)
    rw [map_smul]
    change -(φ₂ (c • ((P₁).toSVec.sgn p x).val) * _ * _) = _
    rw [map_smul, smul_mul_assoc, smul_mul_assoc, smul_neg]

private theorem sgn_action {q : ZMod 2} {f : (P₁).toSVec ⟶ (P₁).toSVec}
    (hf : f ∈ SVec.parityHom (P₁).toSVec (P₁).toSVec q) (x : (P₁).toSVec) :
    (P₁).toSVec.sgn p (f x) = sign k (q * p) • f ((P₁).toSVec.sgn p x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf p) x

omit [Fintype I] in
private theorem parity_mul_self : p * p = p := by
  rcases parity_eq_zero_or_one (D.parity i) with h | h <;> rw [h] <;> decide

/-- The kernel is balanced over the lower algebra `A`: the Koszul sign of `J` cancels the
sign of the crossing intertwiner. -/
theorem rouquierMateKernel_balance (x : (P₁).toSVec) (r : heightAlgebra D Sc a n)
    (y : (Q₁).toSVec) :
    rouquierMateKernelBi D Sc i a ha n ((P₁).ract r x) y =
      rouquierMateKernelBi D Sc i a ha n x ((Q₁).lact r y) := by
  induction r using SuperBimodule.alg_induction_on GA with
  | zero => simp
  | add r s hr hs =>
    rw [map_add, map_add, SVec.add_apply, SVec.add_apply, map_add, LinearMap.add_apply, map_add,
      hr, hs]
  | hom q r hr =>
    have h := sgn_action D Sc i a ha n ((P₁).ract_mem q r hr) x
    apply Subtype.ext
    change -(φ₂ ((P₁).toSVec.sgn p ((P₁).ract r x)).val * τ * φ₂ y.val) =
      -(φ₂ ((P₁).toSVec.sgn p x).val * τ * φ₂ (φ₁ r * y.val))
    rw [h]
    change -(φ₂ (sign k (q * p) • (((P₁).toSVec.sgn p x).val * φ₁ r)) * τ * φ₂ y.val) = _
    have hi := heightLastCrossing_intertwines D Sc a i i ha n hr
    rw [map_smul, map_mul, smul_mul_assoc, smul_mul_assoc, mul_assoc _ (φ₂ (φ₁ r)), hi,
      parity_mul_self, map_mul, mul_smul_comm, smul_mul_assoc, Supercategory.sign_mul, Int.cast_smul_eq_zsmul,
      koszulSign_smul_smul, mul_assoc, mul_assoc, mul_assoc]

/-- The identification `z ↦ z ⊗ e₂` of `e₂ C` with elements of `e₂ C ⊗_C C e₂`. -/
def rouquierMateKernelTarget : (Q₂).toSVec →ₗ[k] (tensor Q₂ P₂).toSVec where
  toFun z := btmul Q₂ P₂ z (heightInductionCornerIdempotent D Sc i a ha (n + 1))
  map_add' z w := btmul_add_left _ _ z w _
  map_smul' c z := btmul_smul_left _ _ c z _

/-- The linear map on the balanced tensor product. -/
def rouquierMateKernelLinear : (tensor P₁ Q₁).toSVec →ₗ[k] (tensor Q₂ P₂).toSVec :=
  rouquierMateKernelTarget D Sc i a ha n ∘ₗ
    tensorLift (rouquierMateKernelBi D Sc i a ha n) (rouquierMateKernel_balance D Sc i a ha n)

@[simp] theorem rouquierMateKernelLinear_btmul (x : (P₁).toSVec) (y : (Q₁).toSVec) :
    rouquierMateKernelLinear D Sc i a ha n (btmul P₁ Q₁ x y) =
      btmul Q₂ P₂ (rouquierMateKernelCorner D Sc i a ha n x y)
        (heightInductionCornerIdempotent D Sc i a ha (n + 1)) := by
  change rouquierMateKernelTarget D Sc i a ha n
    (tensorLift (rouquierMateKernelBi D Sc i a ha n) _ (btmul P₁ Q₁ x y)) = _
  rw [tensorLift_btmul]
  rfl

end OddMath.QuiverHecke.CyclotomicAction
