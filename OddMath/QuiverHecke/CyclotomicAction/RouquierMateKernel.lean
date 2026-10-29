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

/-- On homogeneous `x` the kernel element displays the Koszul sign of `J`. -/
theorem rouquierMateKernelElement_of_mem {q : ZMod 2} {x : (P₁).toSVec}
    (hx : x ∈ (P₁).toSVec.part q) (y : (Q₁).toSVec) :
    rouquierMateKernelElement D Sc i a ha n x y =
      -(koszulSign q p • (φ₂ x.val * τ * φ₂ y.val)) := by
  unfold rouquierMateKernelElement
  rw [SVec.sgn_apply_of_mem p hx]
  change -(φ₂ (sign k (q * p) • x.val) * τ * φ₂ y.val) = _
  rw [map_smul, smul_mul_assoc, smul_mul_assoc, Supercategory.sign_mul, Int.cast_smul_eq_zsmul]

theorem rouquierMateKernelCorner_mem {q r : ZMod 2} {x : (P₁).toSVec} {y : (Q₁).toSVec}
    (hx : x ∈ (P₁).toSVec.part q) (hy : y ∈ (Q₁).toSVec.part r) :
    rouquierMateKernelCorner D Sc i a ha n x y ∈ (Q₂).toSVec.part (q + r + p) := by
  apply (heightRestrictionCorner_mem_part_iff D Sc i a ha (n + 1)).mpr
  change rouquierMateKernelElement D Sc i a ha n x y ∈ GC (q + r + p)
  rw [rouquierMateKernelElement_of_mem D Sc i a ha n hx]
  have hx' := heightAppend_parity D Sc a ha i (n + 1)
    ((heightInductionCorner_mem_part_iff D Sc i a ha n).mp hx)
  have hy' := heightAppend_parity D Sc a ha i (n + 1)
    ((heightRestrictionCorner_mem_part_iff D Sc i a ha n).mp hy)
  have hm := SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem hx'
    (heightLastCrossing_parity D Sc a i i ha n)) hy'
  have he : q + r + p = q + p * p + r := by rw [parity_mul_self]; ring
  rw [he]
  exact neg_mem (Submodule.smul_of_tower_mem _ _ hm)

/-- The mate kernel has parity `|i|`. -/
theorem rouquierMateKernelLinear_mem :
    SVec.ofHom (rouquierMateKernelLinear D Sc i a ha n) ∈
      SVec.parityHom (tensor P₁ Q₁).toSVec (tensor Q₂ P₂).toSVec p := by
  apply tensor_mem_parity_of_btmul
  intro q r x y hx hy
  change rouquierMateKernelLinear D Sc i a ha n (btmul P₁ Q₁ x y) ∈ _
  rw [rouquierMateKernelLinear_btmul, ← add_zero (q + r + p)]
  exact btmul_mem_part _ _ (rouquierMateKernelCorner_mem D Sc i a ha n hx hy)
    (heightInductionCornerIdempotent_mem D Sc i a ha (n + 1))

/-- The kernel `s = -F̄ J` of the Rouquier mate, as a superbimodule morphism of parity `|i|`. -/
def rouquierMateKernel : tensor P₁ Q₁ ⟶ tensor Q₂ P₂ :=
  ⟨SVec.ofHom (rouquierMateKernelLinear D Sc i a ha n), by
    apply (isHom_iff_of_mem (rouquierMateKernelLinear_mem D Sc i a ha n)).mpr
    constructor
    · intro q b hb
      apply tensor_hom_ext P₁ Q₁
      intro x y
      change rouquierMateKernelLinear D Sc i a ha n ((tensor P₁ Q₁).lact b (btmul P₁ Q₁ x y)) =
        sign k (q * p) • (tensor Q₂ P₂).lact b
          (rouquierMateKernelLinear D Sc i a ha n (btmul P₁ Q₁ x y))
      rw [lact_btmul, rouquierMateKernelLinear_btmul, rouquierMateKernelLinear_btmul, lact_btmul,
        ← btmul_smul_left]
      congr 1
      apply Subtype.ext
      have h := sgn_action D Sc i a ha n ((P₁).lact_mem q b hb) x
      change -(φ₂ ((P₁).toSVec.sgn p ((P₁).lact b x)).val * τ * φ₂ y.val) =
        sign k (q * p) • (φ₂ b * -(φ₂ ((P₁).toSVec.sgn p x).val * τ * φ₂ y.val))
      rw [h]
      change -(φ₂ (sign k (q * p) • (b * ((P₁).toSVec.sgn p x).val)) * τ * φ₂ y.val) = _
      rw [map_smul, map_mul, smul_mul_assoc, smul_mul_assoc, mul_neg, smul_neg, mul_assoc,
        mul_assoc, mul_assoc]
    · intro b
      apply tensor_hom_ext P₁ Q₁
      intro x y
      change rouquierMateKernelLinear D Sc i a ha n ((tensor P₁ Q₁).ract b (btmul P₁ Q₁ x y)) =
        (tensor Q₂ P₂).ract b (rouquierMateKernelLinear D Sc i a ha n (btmul P₁ Q₁ x y))
      rw [ract_btmul, rouquierMateKernelLinear_btmul, rouquierMateKernelLinear_btmul, ract_btmul]
      have he : (P₂).ract b (heightInductionCornerIdempotent D Sc i a ha (n + 1)) =
          (P₂).lact (φ₂ b) (heightInductionCornerIdempotent D Sc i a ha (n + 1)) := by
        apply Subtype.ext
        change φ₂ 1 * φ₂ b = φ₂ b * φ₂ 1
        rw [← map_mul, ← map_mul, mul_one, one_mul]
      rw [he, ← btmul_ract_lact]
      congr 1
      apply Subtype.ext
      change -(φ₂ ((P₁).toSVec.sgn p x).val * τ * φ₂ (y.val * b)) =
        -(φ₂ ((P₁).toSVec.sgn p x).val * τ * φ₂ y.val) * φ₂ b
      rw [map_mul, neg_mul, mul_assoc _ (φ₂ y.val)]⟩

theorem rouquierMateKernel_parity :
    rouquierMateKernel D Sc i a ha n ∈ Supercategory.parity (R := k) _ _ p :=
  (mem_parity_iff).mpr (rouquierMateKernelLinear_mem D Sc i a ha n)

/-- Evaluation of the mate kernel on a homogeneous elementary tensor:
`x ⊗ y ↦ -(-1)^{|x||i|} φ₂(x) τ φ₂(y) ⊗ e₂`. -/
theorem rouquierMateKernel_apply {q : ZMod 2} {x : (P₁).toSVec}
    (hx : x ∈ (P₁).toSVec.part q) (y : (Q₁).toSVec) :
    (rouquierMateKernel D Sc i a ha n).1 (btmul P₁ Q₁ x y) =
      btmul Q₂ P₂ (rouquierMateKernelCorner D Sc i a ha n x y)
        (heightInductionCornerIdempotent D Sc i a ha (n + 1)) ∧
    (rouquierMateKernelCorner D Sc i a ha n x y).val =
      -(koszulSign q p • (φ₂ x.val * τ * φ₂ y.val)) :=
  ⟨rouquierMateKernelLinear_btmul D Sc i a ha n x y,
    rouquierMateKernelElement_of_mem D Sc i a ha n hx y⟩

end OddMath.QuiverHecke.CyclotomicAction
