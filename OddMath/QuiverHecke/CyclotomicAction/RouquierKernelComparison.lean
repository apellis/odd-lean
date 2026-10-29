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

theorem rouquierDotSign_succ (p : ZMod 2) (m : ℕ) :
    rouquierDotSign p (m + 1) = rouquierDotSign p m * koszulSign p (m : ZMod 2) := rfl

/-- The sign recursion of the dot power. -/
theorem rouquierDotPow_sign (p q μ : ZMod 2) :
    koszulSign (q + μ * p) p * koszulSign q (μ * p) =
      koszulSign q ((μ + 1) * p) * koszulSign p μ := by
  fin_cases p <;> fin_cases q <;> fin_cases μ <;> decide

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

theorem heightInductionDotPow_parity (m : ℕ) :
    heightInductionDotPow D Sc i a ha n m ∈ parity (R := k) P₁ P₁ ((m : ZMod 2) * p) := by
  induction m with
  | zero =>
    change 𝟙 P₁ ∈ _
    simpa using id_mem P₁
  | succ m ih =>
    have h := comp_mem ih (heightInductionSuperDot_parity D Sc i a ha n)
    rwa [Nat.cast_succ, add_mul, one_mul]

/-- On a homogeneous corner element, `x^m` acts with the sign `(-1)^{m p |y|} d_m`. -/
theorem heightInductionDotPow_apply (m : ℕ) {q : ZMod 2} (y : (P₁).toSVec)
    (hy : y ∈ (P₁).toSVec.part q) :
    ((heightInductionDotPow D Sc i a ha n m).1 y).val =
      (koszulSign q ((m : ZMod 2) * p) * rouquierDotSign p m) • (y.val * x₁ ^ m) := by
  induction m with
  | zero => simp [heightInductionDotPow, rouquierDotSign]
  | succ m ih =>
    have hm : (heightInductionDotPow D Sc i a ha n m).1 y ∈
        (P₁).toSVec.part (q + (m : ZMod 2) * p) :=
      SVec.apply_mem_part (mem_parity_iff.1 (heightInductionDotPow_parity D Sc i a ha n m)) hy
    change ((heightInductionSuperDot D Sc i a ha n).1
      ((heightInductionDotPow D Sc i a ha n m).1 y)).val = _
    rw [heightInductionSuperDot_apply D Sc i a ha n _ hm, ih, smul_mul_assoc, smul_smul,
      mul_assoc, ← pow_succ, rouquierDotSign_succ]
    congr 1
    have hs := rouquierDotPow_sign p q (m : ZMod 2)
    rw [Nat.cast_succ]
    linear_combination (rouquierDotSign p m) * hs

/-! ### The dotted unit and the dotted counit -/

include ha in
theorem heightAppend_one_mul_lastDot_pow (m : ℕ) :
    φ₁ 1 * x₁ ^ m = x₁ ^ m * φ₁ 1 := by
  rw [heightAppend_mul_heightLastDot_pow D Sc a i ha n (SetLike.one_mem_graded GA) m]
  simp [koszulSign]

/-- **The dotted unit is `d_m` times the dotted cup**: the unit `M → Q ⊗ P ⊗ M` followed by
the `m`-th dot power on `P` equals `d_m (j_m ⊗ M)`, up to the unitor and associator. -/
theorem heightSuperUnit_dotPow (m : ℕ) (M : HeightModules D Sc a ha n) :
    heightSuperUnitComponent D Sc i a ha n M ≫
        SuperBimodule.whiskerLeft Q₁
          (SuperBimodule.whiskerRight (heightInductionDotPow D Sc i a ha n m) M) =
      ((rouquierDotSign p m : ℤ) : k) •
        ((leftUnitor M).inv ≫ SuperBimodule.whiskerRight (rouquierCupKernel D Sc i a ha n m) M ≫
          (assoc Q₁ P₁ M).hom) := by
  apply SuperBimodule.hom_ext
  apply SVec.hom_ext
  intro mm
  have hpow := heightInductionDotPow_apply D Sc i a ha n m
    (heightInductionCornerIdempotent D Sc i a ha n)
    (heightInductionCornerIdempotent_mem D Sc i a ha n)
  have he : (heightInductionDotPow D Sc i a ha n m).1
      (heightInductionCornerIdempotent D Sc i a ha n) =
      (rouquierDotSign p m : k) • (P₁).lact (x₁ ^ m)
        (heightInductionCornerIdempotent D Sc i a ha n) := by
    apply Subtype.ext
    rw [hpow]
    change _ = (rouquierDotSign p m : k) • (x₁ ^ m * φ₁ 1)
    rw [koszulSign_zero_left, one_mul, ← Int.cast_smul_eq_zsmul k,
      ← heightAppend_one_mul_lastDot_pow D Sc i a ha n m]
    rfl
  change (SuperBimodule.whiskerLeft Q₁
      (SuperBimodule.whiskerRight (heightInductionDotPow D Sc i a ha n m) M)).1
      (btmul Q₁ (tensor P₁ M) (heightRestrictionCornerOf D Sc i a ha n 1)
        (btmul P₁ M (heightInductionCornerIdempotent D Sc i a ha n) mm)) =
    (rouquierDotSign p m : k) • (assoc Q₁ P₁ M).hom.1
      (btmul (tensor Q₁ P₁) M ((rouquierCupKernel D Sc i a ha n m).1 (1 : A₀)) mm)
  rw [whiskerLeft_btmul (hg := whiskerRight_mem P₁ (heightInductionDotPow_parity D Sc i a ha n m) M)
      (hm := heightRestrictionCornerOf_one_mem D Sc i a ha n), zero_mul, Supercategory.sign_zero,
    one_smul, whiskerRight_btmul, he, btmul_smul_left, ← lact_btmul, btmul_smul_right,
    ← btmul_ract_lact, rouquierCupKernel_apply, assoc_hom_btmul]
  congr 2
  apply Subtype.ext
  change φ₁ 1 * x₁ ^ m = x₁ ^ m * φ₁ 1
  exact heightAppend_one_mul_lastDot_pow D Sc i a ha n m

/-- **The dotted counit is `d_m` times the dotted cap**: the `m`-th dot power on `P` followed by
the counit `P ⊗ Q ⊗ M → M` equals `d_m (κ_m ⊗ M)`, up to the associator and unitor. -/
theorem heightDotPow_superCounit (m : ℕ) (M : HeightModules D Sc a ha (n + 1)) :
    SuperBimodule.whiskerRight (heightInductionDotPow D Sc i a ha n m) (tensor Q₁ M) ≫
        heightSuperCounitComponent D Sc i a ha n M =
      ((rouquierDotSign p m : ℤ) : k) •
        ((assoc P₁ Q₁ M).inv ≫ SuperBimodule.whiskerRight (rouquierCapKernel D Sc i a ha n m) M ≫
          (leftUnitor M).hom) := by
  apply SuperBimodule.hom_ext
  refine tensor_hom_ext_homogeneous P₁ (tensor Q₁ M) fun q _ x z hx hz => ?_
  clear hz
  induction z using tensor_induction_on with
  | zero => simp only [btmul_zero_right, SVec.hom_map_zero]
  | add z w hz hw => simp only [btmul_add_right, SVec.hom_map_add, hz, hw]
  | btmul y mm =>
    change heightSuperCounitLinear D Sc i a ha n M
        (btmul P₁ (tensor Q₁ M) ((heightInductionDotPow D Sc i a ha n m).1 x) (btmul Q₁ M y mm)) =
      (rouquierDotSign p m : k) • (leftUnitor M).hom.1
        ((SuperBimodule.whiskerRight (rouquierCapKernel D Sc i a ha n m) M).1
          ((assoc P₁ Q₁ M).inv.1 (btmul P₁ (tensor Q₁ M) x (btmul Q₁ M y mm))))
    rw [heightSuperCounitLinear_btmul_btmul, assoc_inv_btmul, whiskerRight_btmul]
    change _ = (rouquierDotSign p m : k) • M.lact
      (rouquierCapKernelLinear D Sc i a ha n m (btmul P₁ Q₁ x y)) mm
    rw [rouquierCapKernelLinear_btmul_of_mem D Sc i a ha n m hx,
      heightInductionDotPow_apply D Sc i a ha n m x hx, mul_assoc,
      mul_comm (koszulSign _ _), ← smul_smul, map_zsmul, LinearMap.smul_apply,
      Int.cast_smul_eq_zsmul, smul_mul_assoc, smul_mul_assoc, mul_assoc, map_zsmul, map_zsmul,
      LinearMap.smul_apply, LinearMap.smul_apply]

/-! ### The Rouquier mate -/

omit [Fintype I] in
private theorem parity_mul_self' : p * p = p := by
  rcases parity_eq_zero_or_one (D.parity i) with h | h <;> rw [h] <;> decide

/-- **The mate through the kernel**: the unit at height `n + 1`, the crossing `ψ` and the counit
at height `n`, evaluated on `P ⊗ Q ⊗ M`, equal minus the mate kernel `s ⊗ M`, up to
associators. -/
theorem heightRouquierMate_eq (M : HeightModules D Sc a ha (n + 1)) :
    heightSuperUnitComponent D Sc i a ha (n + 1) (tensor P₁ (tensor Q₁ M)) ≫
        SuperBimodule.whiskerLeft Q₂ (heightInductionCrossingApp D Sc i i a ha n (tensor Q₁ M)) ≫
        SuperBimodule.whiskerLeft Q₂
          (SuperBimodule.whiskerLeft P₂ (heightSuperCounitComponent D Sc i a ha n M)) =
      -((assoc P₁ Q₁ M).inv ≫ SuperBimodule.whiskerRight (rouquierMateKernel D Sc i a ha n) M ≫
          (assoc Q₂ P₂ M).hom) := by
  apply SuperBimodule.hom_ext
  refine tensor_hom_ext_homogeneous P₁ (tensor Q₁ M) fun q _ x z hx hz => ?_
  clear hz
  induction z using tensor_induction_on with
  | zero => simp only [btmul_zero_right, SVec.hom_map_zero]
  | add z w hz hw => simp only [btmul_add_right, SVec.hom_map_add, hz, hw]
  | btmul y mm =>
    have hxB : x.val ∈ GB q := (heightInductionCorner_mem_part_iff D Sc i a ha n).1 hx
    set z0 := heightCompositionCornerBi D Sc i i a ha n
      (heightInductionCornerIdempotent D Sc i a ha (n + 1)) x with hz0def
    have hz0v : z0.val = φ₂ x.val := by
      change φ₂ 1 * φ₂ x.val = _
      rw [← map_mul, one_mul]
    have hz0 : z0 ∈ (heightCompositionCorner D Sc i i a ha n).toSVec.part q :=
      (heightCompositionCorner_mem_part_iff D Sc i i a ha n).2 (by
        rw [hz0v]; exact heightAppend_parity D Sc a ha i (n + 1) hxB)
    set u := heightCompositionCornerInclusion D Sc i i a ha n
      ((heightCompositionSuperCrossing D Sc i i a ha n).1 z0) with hudef
    have huv : u.val = koszulSign q p • (φ₂ x.val * heightLastCrossing D Sc a i i n) := by
      change ((heightCompositionSuperCrossing D Sc i i a ha n).1 z0).val = _
      rw [heightCompositionSuperCrossing_apply D Sc i i a ha n _ hz0, hz0v,
        parity_mul_self' D i]
    have hcross : (heightInductionCrossingApp D Sc i i a ha n (tensor Q₁ M)).1
        (btmul P₂ (tensor P₁ (tensor Q₁ M)) (heightInductionCornerIdempotent D Sc i a ha (n + 1))
          (btmul P₁ (tensor Q₁ M) x (btmul Q₁ M y mm))) =
        btmul P₂ (tensor P₁ (tensor Q₁ M)) u
          (btmul P₁ (tensor Q₁ M) (heightInductionCornerIdempotent D Sc i a ha n)
            (btmul Q₁ M y mm)) := by
      change ((heightInductionFunctorComparison D Sc i i a ha n).inv.app (tensor Q₁ M)).1
          ((SuperBimodule.whiskerRight (heightCompositionSuperCrossing D Sc i i a ha n)
            (tensor Q₁ M)).1
            (((heightInductionFunctorComparison D Sc i i a ha n).hom.app (tensor Q₁ M)).1
              (btmul P₂ (tensor P₁ (tensor Q₁ M))
                (heightInductionCornerIdempotent D Sc i a ha (n + 1))
                (btmul P₁ (tensor Q₁ M) x (btmul Q₁ M y mm))))) = _
      rw [heightInductionFunctorComparison_hom_btmul, whiskerRight_btmul]
      change (assoc P₂ P₁ (tensor Q₁ M)).hom.1
        ((SuperBimodule.whiskerRight (heightInductionCompositionIso D Sc i i a ha n).inv
          (tensor Q₁ M)).1 (btmul _ (tensor Q₁ M)
            ((heightCompositionSuperCrossing D Sc i i a ha n).1 z0) (btmul Q₁ M y mm))) = _
      rw [whiskerRight_btmul, heightInductionCompositionIso_inv_apply, assoc_hom_btmul]
    have hcounit : (heightSuperCounitComponent D Sc i a ha n M).1
        (btmul P₁ (tensor Q₁ M) (heightInductionCornerIdempotent D Sc i a ha n)
          (btmul Q₁ M y mm)) = M.lact y.val mm := by
      change heightSuperCounitLinear D Sc i a ha n M _ = _
      rw [heightSuperCounitLinear_btmul_btmul]
      have hy : φ₁ 1 * y.val = y.val := y.2
      change M.lact (φ₁ 1 * y.val) mm = _
      rw [hy]
    obtain ⟨hmate, hmatev⟩ := rouquierMateKernel_apply D Sc i a ha n hx y
    set c := rouquierMateKernelCorner D Sc i a ha n x y with hcdef
    change (SuperBimodule.whiskerLeft Q₂
        (SuperBimodule.whiskerLeft P₂ (heightSuperCounitComponent D Sc i a ha n M))).1
        ((SuperBimodule.whiskerLeft Q₂
          (heightInductionCrossingApp D Sc i i a ha n (tensor Q₁ M))).1
          (btmul Q₂ _ (heightRestrictionCornerOf D Sc i a ha (n + 1) 1)
            (btmul P₂ (tensor P₁ (tensor Q₁ M))
              (heightInductionCornerIdempotent D Sc i a ha (n + 1))
              (btmul P₁ (tensor Q₁ M) x (btmul Q₁ M y mm))))) =
      -((assoc Q₂ P₂ M).hom.1 ((SuperBimodule.whiskerRight (rouquierMateKernel D Sc i a ha n) M).1
        ((assoc P₁ Q₁ M).inv.1 (btmul P₁ (tensor Q₁ M) x (btmul Q₁ M y mm)))))
    rw [whiskerLeft_btmul (hg := heightInductionCrossingApp_mem D Sc i i a ha n (tensor Q₁ M))
        (hm := heightRestrictionCornerOf_one_mem D Sc i a ha (n + 1)), zero_mul,
      Supercategory.sign_zero, one_smul, hcross]
    change (SuperBimodule.whiskerLeft Q₂
        (SuperBimodule.whiskerLeft P₂ (heightSuperCounitComponent D Sc i a ha n M))).1
        (btmul Q₂ (tensor P₂ (tensor P₁ (tensor Q₁ M)))
          (heightRestrictionCornerOf D Sc i a ha (n + 1) 1)
          (btmul P₂ (tensor P₁ (tensor Q₁ M)) u
            (btmul P₁ (tensor Q₁ M) (heightInductionCornerIdempotent D Sc i a ha n)
              (btmul Q₁ M y mm)))) = _
    rw [whiskerLeft_btmul_even (hg := whiskerLeft_mem P₂ _ (heightSuperCounitComponent_mem D Sc i a ha n M)),
      whiskerLeft_btmul_even (hg := heightSuperCounitComponent_mem D Sc i a ha n M), hcounit,
      assoc_inv_btmul, whiskerRight_btmul, hmate, assoc_hom_btmul, ← btmul_ract_lact]
    have hw : (P₂).ract y.val u =
        (P₂).lact ((P₂).ract y.val u).val (heightInductionCornerIdempotent D Sc i a ha (n + 1)) := by
      apply Subtype.ext
      exact (((P₂).ract y.val u).2).symm
    rw [hw, ← lact_btmul, ← btmul_ract_lact]
    have hc : (Q₂).ract ((P₂).ract y.val u).val (heightRestrictionCornerOf D Sc i a ha (n + 1) 1) =
        -c := by
      apply Subtype.ext
      change heightAppend D Sc a i (n + 1) 1 * (u.val * φ₂ y.val) = -c.val
      rw [hmatev, huv, neg_neg, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← mul_assoc,
        ← map_mul, one_mul]
    rw [hc, ← neg_one_zsmul c, btmul_zsmul_left, neg_one_zsmul]

end OddMath.QuiverHecke.CyclotomicAction
