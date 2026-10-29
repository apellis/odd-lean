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

/-- The last dot commutes with the strand map up to the iterated Koszul sign. -/
theorem heightAppend_mul_heightLastDot_pow (a : I → _root_.Polynomial k) (i : I)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) {q : ZMod 2}
    {r : heightAlgebra D Sc a n} (hr : r ∈ heightParity D Sc a ha n q) (m : ℕ) :
    heightAppend D Sc a i n r * heightLastDot D Sc a i n ^ m =
      koszulSign q ((m : ZMod 2) * D.parity i) •
        (heightLastDot D Sc a i n ^ m * heightAppend D Sc a i n r) := by
  induction m with
  | zero => simp [koszulSign]
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc,
      heightLastDot_comm D Sc a i ha n hr, mul_smul_comm, smul_smul, ← mul_assoc,
      ← koszulSign_add_right, Nat.cast_succ, add_mul, one_mul]

/-- Powers of the last dot are homogeneous of parity `m |i|`. -/
theorem heightLastDot_pow_parity (a : I → _root_.Polynomial k) (i : I)
    (ha : CyclotomicPolynomialParity D a) (n m : ℕ) :
    heightLastDot D Sc a i n ^ m ∈ heightParity D Sc a ha (n + 1) ((m : ZMod 2) * D.parity i) := by
  have h := SetLike.pow_mem_graded m (heightLastDot_parity D Sc a i ha n)
  rwa [nsmul_eq_mul] at h

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

include ha in
theorem rouquierCupElement_left (b : A₀) :
    φ₁ 1 * (x₁ ^ m * φ₁ b) = x₁ ^ m * φ₁ b := by
  rw [← mul_assoc, heightAppend_mul_heightLastDot_pow D Sc a i ha n
    (SetLike.one_mem_graded GA) m, smul_mul_assoc, mul_assoc, ← map_mul, one_mul]
  simp [koszulSign]

/-- The linear dotted cup `b ↦ x^m φ(b) ⊗ e`. -/
def rouquierCupKernelLinear : A₀ →ₗ[k] (tensor Q₁ P₁).toSVec where
  toFun b := btmul Q₁ P₁ ⟨x₁ ^ m * φ₁ b, rouquierCupElement_left D Sc i a ha n m b⟩
    (heightInductionCornerIdempotent D Sc i a ha n)
  map_add' b c := by
    rw [← btmul_add_left]
    congr 1
    apply Subtype.ext
    change x₁ ^ m * φ₁ (b + c) = x₁ ^ m * φ₁ b + x₁ ^ m * φ₁ c
    rw [map_add, mul_add]
  map_smul' c b := by
    rw [RingHom.id_apply, ← btmul_smul_left]
    congr 1
    apply Subtype.ext
    change x₁ ^ m * φ₁ (c • b) = c • (x₁ ^ m * φ₁ b)
    rw [map_smul, mul_smul_comm]

theorem rouquierCupKernelLinear_mem :
    SVec.ofHom (rouquierCupKernelLinear D Sc i a ha n m) ∈
      SVec.parityHom (regular GA).toSVec (tensor Q₁ P₁).toSVec kp := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q b hb
  rw [show q + kp = (kp + q) + 0 by ring]
  apply btmul_mem_part
  · apply (heightRestrictionCorner_mem_part_iff D Sc i a ha n).mpr
    exact SetLike.GradedMul.mul_mem (heightLastDot_pow_parity D Sc a i ha n m)
      (heightAppend_parity D Sc a ha i n ((mem_regularSVec_part_iff GA).mp hb))
  · exact heightInductionCornerIdempotent_mem D Sc i a ha n

/-- The dotted cup `j_m : A ⟶ e B ⊗_B B e`, of parity `m |i|`. -/
def rouquierCupKernel : regular GA ⟶ tensor Q₁ P₁ :=
  ⟨SVec.ofHom (rouquierCupKernelLinear D Sc i a ha n m), by
    apply (isHom_iff_of_mem (rouquierCupKernelLinear_mem D Sc i a ha n m)).mpr
    constructor
    · intro q b' hb'
      apply SVec.hom_ext
      intro (b : A₀)
      change rouquierCupKernelLinear D Sc i a ha n m (b' * b) =
        sign k (q * kp) • (tensor Q₁ P₁).lact b' (rouquierCupKernelLinear D Sc i a ha n m b)
      change _ = sign k (q * kp) • btmul Q₁ P₁ ((Q₁).lact b' _) _
      rw [← btmul_smul_left]
      show btmul Q₁ P₁ _ _ = btmul Q₁ P₁ _ _
      congr 1
      apply Subtype.ext
      change x₁ ^ m * φ₁ (b' * b) = sign k (q * kp) • (φ₁ b' * (x₁ ^ m * φ₁ b))
      rw [← mul_assoc (φ₁ b'), heightAppend_mul_heightLastDot_pow D Sc a i ha n hb' m,
        smul_mul_assoc, Supercategory.sign_mul, Int.cast_smul_eq_zsmul, koszulSign_smul_smul,
        map_mul, mul_assoc]
    · intro b'
      apply SVec.hom_ext
      intro (b : A₀)
      change rouquierCupKernelLinear D Sc i a ha n m (b * b') =
        (tensor Q₁ P₁).ract b' (rouquierCupKernelLinear D Sc i a ha n m b)
      change _ = btmul Q₁ P₁ _ ((P₁).ract b' _)
      have he : (P₁).ract b' (heightInductionCornerIdempotent D Sc i a ha n) =
          (P₁).lact (φ₁ b') (heightInductionCornerIdempotent D Sc i a ha n) := by
        apply Subtype.ext
        change φ₁ 1 * φ₁ b' = φ₁ b' * φ₁ 1
        rw [← map_mul, ← map_mul, mul_one, one_mul]
      rw [he, ← btmul_ract_lact]
      show btmul Q₁ P₁ _ _ = btmul Q₁ P₁ _ _
      congr 1
      apply Subtype.ext
      change x₁ ^ m * φ₁ (b * b') = x₁ ^ m * φ₁ b * φ₁ b'
      rw [map_mul, mul_assoc]⟩

theorem rouquierCupKernel_parity :
    rouquierCupKernel D Sc i a ha n m ∈ Supercategory.parity (R := k) _ _ kp :=
  (mem_parity_iff).mpr (rouquierCupKernelLinear_mem D Sc i a ha n m)

/-- Evaluation of the dotted cup. -/
theorem rouquierCupKernel_apply (b : A₀) :
    (rouquierCupKernel D Sc i a ha n m).1 b =
      btmul Q₁ P₁ ⟨x₁ ^ m * φ₁ b, rouquierCupElement_left D Sc i a ha n m b⟩
        (heightInductionCornerIdempotent D Sc i a ha n) := rfl

/-! ### The dotted cap -/

/-- The bilinear dotted cap `x ⊗ y ↦ sgn_{m p}(x) x₁^m y`. -/
def rouquierCapKernelBi : (P₁).toSVec →ₗ[k] (Q₁).toSVec →ₗ[k] B₁ where
  toFun x :=
    { toFun := fun y => ((P₁).toSVec.sgn kp x).val * x₁ ^ m * y.val
      map_add' := fun y z => mul_add _ y.val z.val
      map_smul' := fun c y => mul_smul_comm c _ y.val }
  map_add' x y := by
    ext z
    change ((P₁).toSVec.sgn kp (x + y)).val * _ * _ = _
    rw [map_add]
    change (((P₁).toSVec.sgn kp x).val + ((P₁).toSVec.sgn kp y).val) * _ * _ = _
    rw [add_mul, add_mul]
    rfl
  map_smul' c x := by
    ext z
    change ((P₁).toSVec.sgn kp (c • x)).val * _ * _ = _
    rw [map_smul]
    change (c • ((P₁).toSVec.sgn kp x).val) * _ * _ = _
    rw [smul_mul_assoc, smul_mul_assoc]
    rfl

private theorem cap_sgn_action {q : ZMod 2} {f : (P₁).toSVec ⟶ (P₁).toSVec}
    (hf : f ∈ SVec.parityHom (P₁).toSVec (P₁).toSVec q) (x : (P₁).toSVec) :
    (P₁).toSVec.sgn kp (f x) = sign k (q * kp) • f ((P₁).toSVec.sgn kp x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf kp) x

theorem rouquierCapKernel_balance (x : (P₁).toSVec) (r : heightAlgebra D Sc a n)
    (y : (Q₁).toSVec) :
    rouquierCapKernelBi D Sc i a ha n m ((P₁).ract r x) y =
      rouquierCapKernelBi D Sc i a ha n m x ((Q₁).lact r y) := by
  induction r using SuperBimodule.alg_induction_on GA with
  | zero => simp
  | add r s hr hs =>
    rw [map_add, map_add, SVec.add_apply, SVec.add_apply, map_add, LinearMap.add_apply, map_add,
      hr, hs]
  | hom q r hr =>
    have h := cap_sgn_action D Sc i a ha n m ((P₁).ract_mem q r hr) x
    change ((P₁).toSVec.sgn kp ((P₁).ract r x)).val * x₁ ^ m * y.val =
      ((P₁).toSVec.sgn kp x).val * x₁ ^ m * (φ₁ r * y.val)
    rw [h]
    change (sign k (q * kp) • (((P₁).toSVec.sgn kp x).val * φ₁ r)) * x₁ ^ m * y.val = _
    rw [smul_mul_assoc, smul_mul_assoc, mul_assoc _ (φ₁ r),
      heightAppend_mul_heightLastDot_pow D Sc a i ha n hr m, mul_smul_comm, smul_mul_assoc,
      Supercategory.sign_mul, Int.cast_smul_eq_zsmul, koszulSign_smul_smul, mul_assoc, mul_assoc,
      mul_assoc]

/-- The linear dotted cap on the balanced tensor product. -/
def rouquierCapKernelLinear : (tensor P₁ Q₁).toSVec →ₗ[k] B₁ :=
  tensorLift (rouquierCapKernelBi D Sc i a ha n m) (rouquierCapKernel_balance D Sc i a ha n m)

@[simp] theorem rouquierCapKernelLinear_btmul (x : (P₁).toSVec) (y : (Q₁).toSVec) :
    rouquierCapKernelLinear D Sc i a ha n m (btmul P₁ Q₁ x y) =
      ((P₁).toSVec.sgn kp x).val * x₁ ^ m * y.val :=
  tensorLift_btmul _ _ x y

/-- On homogeneous `x` the cap displays the sign `(-1)^{m p |x|}`. -/
theorem rouquierCapKernelLinear_btmul_of_mem {q : ZMod 2} {x : (P₁).toSVec}
    (hx : x ∈ (P₁).toSVec.part q) (y : (Q₁).toSVec) :
    rouquierCapKernelLinear D Sc i a ha n m (btmul P₁ Q₁ x y) =
      koszulSign q kp • (x.val * x₁ ^ m * y.val) := by
  rw [rouquierCapKernelLinear_btmul, SVec.sgn_apply_of_mem kp hx]
  change (sign k (q * kp) • x.val) * _ * _ = _
  rw [smul_mul_assoc, smul_mul_assoc, Supercategory.sign_mul, Int.cast_smul_eq_zsmul]

theorem rouquierCapKernelLinear_mem :
    SVec.ofHom (rouquierCapKernelLinear D Sc i a ha n m) ∈
      SVec.parityHom (tensor P₁ Q₁).toSVec (regular GB).toSVec kp := by
  apply tensor_mem_parity_of_btmul
  intro q r x y hx hy
  change rouquierCapKernelLinear D Sc i a ha n m (btmul P₁ Q₁ x y) ∈ (regularSVec GB).part _
  rw [rouquierCapKernelLinear_btmul_of_mem D Sc i a ha n m hx, mem_regularSVec_part_iff]
  have hm := SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem
    ((heightInductionCorner_mem_part_iff D Sc i a ha n).mp hx)
    (heightLastDot_pow_parity D Sc a i ha n m))
    ((heightRestrictionCorner_mem_part_iff D Sc i a ha n).mp hy)
  have he : q + r + kp = q + kp + r := by ring
  rw [he]
  exact Submodule.smul_of_tower_mem _ _ hm

/-- The dotted cap `κ_m : B e ⊗_A e B ⟶ B`, of parity `m |i|`. -/
def rouquierCapKernel : tensor P₁ Q₁ ⟶ regular GB :=
  ⟨SVec.ofHom (rouquierCapKernelLinear D Sc i a ha n m), by
    apply (isHom_iff_of_mem (rouquierCapKernelLinear_mem D Sc i a ha n m)).mpr
    constructor
    · intro q b hb
      apply tensor_hom_ext P₁ Q₁
      intro x y
      change rouquierCapKernelLinear D Sc i a ha n m ((tensor P₁ Q₁).lact b (btmul P₁ Q₁ x y)) =
        sign k (q * kp) • (b * rouquierCapKernelLinear D Sc i a ha n m (btmul P₁ Q₁ x y))
      rw [lact_btmul, rouquierCapKernelLinear_btmul, rouquierCapKernelLinear_btmul,
        cap_sgn_action D Sc i a ha n m ((P₁).lact_mem q b hb) x]
      change (sign k (q * kp) • (b * ((P₁).toSVec.sgn kp x).val)) * _ * _ = _
      rw [smul_mul_assoc, smul_mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    · intro b
      apply tensor_hom_ext P₁ Q₁
      intro x y
      change rouquierCapKernelLinear D Sc i a ha n m ((tensor P₁ Q₁).ract b (btmul P₁ Q₁ x y)) =
        rouquierCapKernelLinear D Sc i a ha n m (btmul P₁ Q₁ x y) * b
      rw [ract_btmul, rouquierCapKernelLinear_btmul, rouquierCapKernelLinear_btmul]
      exact (mul_assoc _ y.val b).symm⟩

theorem rouquierCapKernel_parity :
    rouquierCapKernel D Sc i a ha n m ∈ Supercategory.parity (R := k) _ _ kp :=
  (mem_parity_iff).mpr (rouquierCapKernelLinear_mem D Sc i a ha n m)

end OddMath.QuiverHecke.CyclotomicAction
