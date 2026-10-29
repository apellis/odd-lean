/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightAdjunction
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightCrossing

/-!
# The two-colour mate kernel at one height

Write `A`, `B`, `C` for the deformed cyclotomic algebras at heights `n`, `n + 1`, `n + 2` of
the extended tower and `φᵢ, φⱼ` for the strand maps of colours `i` and `j`. Let
`c ∈ C` be the crossing of the last two strands with colours `i` (left) and `j` (right),
`heightLastCrossing a i j n`, of parity `d = |i||j|`. The relevant corners of
`GlobalHeightAdjunction` are the induction corners `P₁ = B eⱼ`, `P₂ = C eⱼ` of colour `j`
and the restriction corners `Q₁ = eᵢ B`, `Q₂ = eᵢ C` of colour `i`.

This file constructs the kernel of the mate of the two-colour crossing (relation (1.12) of
Brundan–Ellis, arXiv:1701.04133v2, Definition 1.5) on these corners,
`s : B eⱼ ⊗_A eᵢ B → eᵢ C ⊗_C C eⱼ`, `x ⊗ y ↦ (-1)^{d|x|} φᵢ(x) c φⱼ(y) ⊗ eⱼ`,
and identifies the mate (unit at height `n + 1`, crossing, counit at height `n`) evaluated
on `P₁ ⊗ Q₁ ⊗ M` with `s ⊗ M` (`heightMixedMate_eq`). The construction uses only the
signed intertwining relation
`φᵢ(φⱼ r) c = (-1)^{d|r|} c φⱼ(φᵢ r)` (`heightLastCrossing_intertwines`).

The isomorphism property of `s` for `i ≠ j` is the cyclotomic distinct-colour Mackey
isomorphism `B eⱼ ⊗_A eᵢ B ≅ eᵢ C eⱼ` (Kang–Kashiwara–Oh, arXiv:1206.5933v2, Theorem 9.1 and
(9.2)–(9.3); `docs/Nondegeneracy/MulticolourCyclotomicAction.md`).

## Main declarations

* `mixedMateKernel`: the superbimodule morphism `tensor P₁ Q₁ ⟶ tensor Q₂ P₂`.
* `mixedMateKernel_parity`: it has parity `|i||j|`.
* `mixedMateKernel_apply`: its value on homogeneous elementary tensors.
* `heightMixedMate_eq`: the height-level mate is `s ⊗ M`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open SuperBimodule
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i j : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "C₂" => heightAlgebra D Sc a (n + 1 + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "GB" => heightParity D Sc a ha (n + 1)
local notation "GC" => heightParity D Sc a ha (n + 1 + 1)
local notation "φi₁" => heightAppend D Sc a i n
local notation "φj₁" => heightAppend D Sc a j n
local notation "φi₂" => heightAppend D Sc a i (n + 1)
local notation "φj₂" => heightAppend D Sc a j (n + 1)
local notation "c" => heightLastCrossing D Sc a i j n
local notation "P₁" => heightInductionCorner D Sc j a ha n
local notation "Q₁" => heightRestrictionCorner D Sc i a ha n
local notation "P₂" => heightInductionCorner D Sc j a ha (n + 1)
local notation "Q₂" => heightRestrictionCorner D Sc i a ha (n + 1)
local notation "d" => D.parity i * D.parity j

/-- The algebra element `φᵢ(sgn x) c φⱼ(y)` underlying the mixed mate kernel. -/
def mixedMateKernelElement (x : (P₁).toSVec) (y : (Q₁).toSVec) : C₂ :=
  φi₂ ((P₁).toSVec.sgn d x).val * c * φj₂ y.val

theorem mixedMateKernelElement_left (x : (P₁).toSVec) (y : (Q₁).toSVec) :
    φi₂ 1 * mixedMateKernelElement D Sc i j a ha n x y =
      mixedMateKernelElement D Sc i j a ha n x y := by
  unfold mixedMateKernelElement
  rw [← mul_assoc, ← mul_assoc, ← map_mul, one_mul]

/-- The kernel element as an element of the upper restriction corner `eᵢ C`. -/
def mixedMateKernelCorner (x : (P₁).toSVec) (y : (Q₁).toSVec) : (Q₂).toSVec :=
  ⟨mixedMateKernelElement D Sc i j a ha n x y, mixedMateKernelElement_left D Sc i j a ha n x y⟩

/-- The kernel is bilinear in the two corner factors. -/
def mixedMateKernelBi : (P₁).toSVec →ₗ[k] (Q₁).toSVec →ₗ[k] (Q₂).toSVec where
  toFun x :=
    { toFun := fun y => mixedMateKernelCorner D Sc i j a ha n x y
      map_add' := fun y z => by
        apply Subtype.ext
        change _ * _ * φj₂ (y.val + z.val) = _ * _ * φj₂ y.val + _ * _ * φj₂ z.val
        rw [map_add, mul_add]
      map_smul' := fun r y => by
        apply Subtype.ext
        change _ * _ * φj₂ (r • y.val) = r • (_ * _ * φj₂ y.val)
        rw [map_smul, mul_smul_comm] }
  map_add' x y := by
    ext z
    apply Subtype.ext
    change φi₂ ((P₁).toSVec.sgn d (x + y)).val * _ * _ =
      φi₂ ((P₁).toSVec.sgn d x).val * _ * _ + φi₂ ((P₁).toSVec.sgn d y).val * _ * _
    rw [map_add]
    change φi₂ (((P₁).toSVec.sgn d x).val + ((P₁).toSVec.sgn d y).val) * _ * _ = _
    rw [map_add, add_mul, add_mul]
  map_smul' r x := by
    ext z
    apply Subtype.ext
    change φi₂ ((P₁).toSVec.sgn d (r • x)).val * _ * _ =
      r • (φi₂ ((P₁).toSVec.sgn d x).val * _ * _)
    rw [map_smul]
    change φi₂ (r • ((P₁).toSVec.sgn d x).val) * _ * _ = _
    rw [map_smul, smul_mul_assoc, smul_mul_assoc]

private theorem sgn_action {q : ZMod 2} {f : (P₁).toSVec ⟶ (P₁).toSVec}
    (hf : f ∈ SVec.parityHom (P₁).toSVec (P₁).toSVec q) (x : (P₁).toSVec) :
    (P₁).toSVec.sgn d (f x) = sign k (q * d) • f ((P₁).toSVec.sgn d x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf d) x

/-- The kernel is balanced over the lower algebra `A`: the Koszul sign of `x` cancels the
sign of the crossing intertwiner. -/
theorem mixedMateKernel_balance (x : (P₁).toSVec) (r : heightAlgebra D Sc a n)
    (y : (Q₁).toSVec) :
    mixedMateKernelBi D Sc i j a ha n ((P₁).ract r x) y =
      mixedMateKernelBi D Sc i j a ha n x ((Q₁).lact r y) := by
  induction r using SuperBimodule.alg_induction_on GA with
  | zero => simp
  | add r s hr hs =>
    rw [map_add, map_add, SVec.add_apply, SVec.add_apply, map_add, LinearMap.add_apply, map_add,
      hr, hs]
  | hom q r hr =>
    have h := sgn_action D Sc i j a ha n ((P₁).ract_mem q r hr) x
    apply Subtype.ext
    change φi₂ ((P₁).toSVec.sgn d ((P₁).ract r x)).val * c * φj₂ y.val =
      φi₂ ((P₁).toSVec.sgn d x).val * c * φj₂ (φi₁ r * y.val)
    rw [h]
    change φi₂ (sign k (q * d) • (((P₁).toSVec.sgn d x).val * φj₁ r)) * c * φj₂ y.val = _
    have hi := heightLastCrossing_intertwines D Sc a i j ha n hr
    rw [map_smul, map_mul, smul_mul_assoc, smul_mul_assoc, mul_assoc _ (φi₂ (φj₁ r)), hi,
      map_mul, mul_smul_comm, smul_mul_assoc, Supercategory.sign_mul, Int.cast_smul_eq_zsmul,
      koszulSign_smul_smul, mul_assoc, mul_assoc, mul_assoc]

/-- The identification `z ↦ z ⊗ eⱼ` of `eᵢ C` with elements of `eᵢ C ⊗_C C eⱼ`. -/
def mixedMateKernelTarget : (Q₂).toSVec →ₗ[k] (tensor Q₂ P₂).toSVec where
  toFun z := btmul Q₂ P₂ z (heightInductionCornerIdempotent D Sc j a ha (n + 1))
  map_add' z w := btmul_add_left _ _ z w _
  map_smul' r z := btmul_smul_left _ _ r z _

/-- The linear map on the balanced tensor product. -/
def mixedMateKernelLinear : (tensor P₁ Q₁).toSVec →ₗ[k] (tensor Q₂ P₂).toSVec :=
  mixedMateKernelTarget D Sc i j a ha n ∘ₗ
    tensorLift (mixedMateKernelBi D Sc i j a ha n) (mixedMateKernel_balance D Sc i j a ha n)

@[simp] theorem mixedMateKernelLinear_btmul (x : (P₁).toSVec) (y : (Q₁).toSVec) :
    mixedMateKernelLinear D Sc i j a ha n (btmul P₁ Q₁ x y) =
      btmul Q₂ P₂ (mixedMateKernelCorner D Sc i j a ha n x y)
        (heightInductionCornerIdempotent D Sc j a ha (n + 1)) := by
  change mixedMateKernelTarget D Sc i j a ha n
    (tensorLift (mixedMateKernelBi D Sc i j a ha n) _ (btmul P₁ Q₁ x y)) = _
  rw [tensorLift_btmul]
  rfl

/-- On homogeneous `x` the kernel element displays the Koszul sign. -/
theorem mixedMateKernelElement_of_mem {q : ZMod 2} {x : (P₁).toSVec}
    (hx : x ∈ (P₁).toSVec.part q) (y : (Q₁).toSVec) :
    mixedMateKernelElement D Sc i j a ha n x y =
      koszulSign q d • (φi₂ x.val * c * φj₂ y.val) := by
  unfold mixedMateKernelElement
  rw [SVec.sgn_apply_of_mem d hx]
  change φi₂ (sign k (q * d) • x.val) * c * φj₂ y.val = _
  rw [map_smul, smul_mul_assoc, smul_mul_assoc, Supercategory.sign_mul, Int.cast_smul_eq_zsmul]

theorem mixedMateKernelCorner_mem {q r : ZMod 2} {x : (P₁).toSVec} {y : (Q₁).toSVec}
    (hx : x ∈ (P₁).toSVec.part q) (hy : y ∈ (Q₁).toSVec.part r) :
    mixedMateKernelCorner D Sc i j a ha n x y ∈ (Q₂).toSVec.part (q + r + d) := by
  apply (heightRestrictionCorner_mem_part_iff D Sc i a ha (n + 1)).mpr
  change mixedMateKernelElement D Sc i j a ha n x y ∈ GC (q + r + d)
  rw [mixedMateKernelElement_of_mem D Sc i j a ha n hx]
  have hx' := heightAppend_parity D Sc a ha i (n + 1)
    ((heightInductionCorner_mem_part_iff D Sc j a ha n).mp hx)
  have hy' := heightAppend_parity D Sc a ha j (n + 1)
    ((heightRestrictionCorner_mem_part_iff D Sc i a ha n).mp hy)
  have hm := SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem hx'
    (heightLastCrossing_parity D Sc a i j ha n)) hy'
  have he : q + r + d = q + d + r := by ring
  rw [he]
  exact Submodule.smul_of_tower_mem _ _ hm

/-- The mixed mate kernel has parity `|i||j|`. -/
theorem mixedMateKernelLinear_mem :
    SVec.ofHom (mixedMateKernelLinear D Sc i j a ha n) ∈
      SVec.parityHom (tensor P₁ Q₁).toSVec (tensor Q₂ P₂).toSVec d := by
  apply tensor_mem_parity_of_btmul
  intro q r x y hx hy
  change mixedMateKernelLinear D Sc i j a ha n (btmul P₁ Q₁ x y) ∈ _
  rw [mixedMateKernelLinear_btmul, ← add_zero (q + r + d)]
  exact btmul_mem_part _ _ (mixedMateKernelCorner_mem D Sc i j a ha n hx hy)
    (heightInductionCornerIdempotent_mem D Sc j a ha (n + 1))

/-- The kernel of the two-colour mate, as a superbimodule morphism of parity `|i||j|`. -/
def mixedMateKernel : tensor P₁ Q₁ ⟶ tensor Q₂ P₂ :=
  ⟨SVec.ofHom (mixedMateKernelLinear D Sc i j a ha n), by
    apply (isHom_iff_of_mem (mixedMateKernelLinear_mem D Sc i j a ha n)).mpr
    constructor
    · intro q b hb
      apply tensor_hom_ext P₁ Q₁
      intro x y
      change mixedMateKernelLinear D Sc i j a ha n ((tensor P₁ Q₁).lact b (btmul P₁ Q₁ x y)) =
        sign k (q * d) • (tensor Q₂ P₂).lact b
          (mixedMateKernelLinear D Sc i j a ha n (btmul P₁ Q₁ x y))
      rw [lact_btmul, mixedMateKernelLinear_btmul, mixedMateKernelLinear_btmul, lact_btmul,
        ← btmul_smul_left]
      congr 1
      apply Subtype.ext
      have h := sgn_action D Sc i j a ha n ((P₁).lact_mem q b hb) x
      change φi₂ ((P₁).toSVec.sgn d ((P₁).lact b x)).val * c * φj₂ y.val =
        sign k (q * d) • (φi₂ b * (φi₂ ((P₁).toSVec.sgn d x).val * c * φj₂ y.val))
      rw [h]
      change φi₂ (sign k (q * d) • (b * ((P₁).toSVec.sgn d x).val)) * c * φj₂ y.val = _
      rw [map_smul, map_mul, smul_mul_assoc, smul_mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    · intro b
      apply tensor_hom_ext P₁ Q₁
      intro x y
      change mixedMateKernelLinear D Sc i j a ha n ((tensor P₁ Q₁).ract b (btmul P₁ Q₁ x y)) =
        (tensor Q₂ P₂).ract b (mixedMateKernelLinear D Sc i j a ha n (btmul P₁ Q₁ x y))
      rw [ract_btmul, mixedMateKernelLinear_btmul, mixedMateKernelLinear_btmul, ract_btmul]
      have he : (P₂).ract b (heightInductionCornerIdempotent D Sc j a ha (n + 1)) =
          (P₂).lact (φj₂ b) (heightInductionCornerIdempotent D Sc j a ha (n + 1)) := by
        apply Subtype.ext
        change φj₂ 1 * φj₂ b = φj₂ b * φj₂ 1
        rw [← map_mul, ← map_mul, mul_one, one_mul]
      rw [he, ← btmul_ract_lact]
      congr 1
      apply Subtype.ext
      change φi₂ ((P₁).toSVec.sgn d x).val * c * φj₂ (y.val * b) =
        φi₂ ((P₁).toSVec.sgn d x).val * c * φj₂ y.val * φj₂ b
      rw [map_mul, mul_assoc _ (φj₂ y.val)]⟩

theorem mixedMateKernel_parity :
    mixedMateKernel D Sc i j a ha n ∈ Supercategory.parity (R := k) _ _ d :=
  (mem_parity_iff).mpr (mixedMateKernelLinear_mem D Sc i j a ha n)

/-- Evaluation of the mixed mate kernel on a homogeneous elementary tensor:
`x ⊗ y ↦ (-1)^{|x||i||j|} φᵢ(x) c φⱼ(y) ⊗ eⱼ`. -/
theorem mixedMateKernel_apply {q : ZMod 2} {x : (P₁).toSVec}
    (hx : x ∈ (P₁).toSVec.part q) (y : (Q₁).toSVec) :
    (mixedMateKernel D Sc i j a ha n).1 (btmul P₁ Q₁ x y) =
      btmul Q₂ P₂ (mixedMateKernelCorner D Sc i j a ha n x y)
        (heightInductionCornerIdempotent D Sc j a ha (n + 1)) ∧
    (mixedMateKernelCorner D Sc i j a ha n x y).val =
      koszulSign q d • (φi₂ x.val * c * φj₂ y.val) :=
  ⟨mixedMateKernelLinear_btmul D Sc i j a ha n x y,
    mixedMateKernelElement_of_mem D Sc i j a ha n hx y⟩

/-! ### The mate through the kernel -/

/-- **The two-colour mate through the kernel**: the unit of colour `i` at height `n + 1`, the
crossing `ψ` of colours `i, j` and the counit of colour `i` at height `n`, evaluated on
`P₁ ⊗ Q₁ ⊗ M`, equal the mixed mate kernel `s ⊗ M`, up to associators. -/
theorem heightMixedMate_eq (M : HeightModules D Sc a ha (n + 1)) :
    heightSuperUnitComponent D Sc i a ha (n + 1) (tensor P₁ (tensor Q₁ M)) ≫
        SuperBimodule.whiskerLeft Q₂ (heightInductionCrossingApp D Sc i j a ha n (tensor Q₁ M)) ≫
        SuperBimodule.whiskerLeft Q₂
          (SuperBimodule.whiskerLeft P₂ (heightSuperCounitComponent D Sc i a ha n M)) =
      (assoc P₁ Q₁ M).inv ≫ SuperBimodule.whiskerRight (mixedMateKernel D Sc i j a ha n) M ≫
          (assoc Q₂ P₂ M).hom := by
  apply SuperBimodule.hom_ext
  refine tensor_hom_ext_homogeneous P₁ (tensor Q₁ M) fun q _ x z hx hz => ?_
  clear hz
  induction z using tensor_induction_on with
  | zero => simp only [btmul_zero_right, SVec.hom_map_zero]
  | add z w hz hw => simp only [btmul_add_right, SVec.hom_map_add, hz, hw]
  | btmul y mm =>
    have hxB : x.val ∈ GB q := (heightInductionCorner_mem_part_iff D Sc j a ha n).1 hx
    set z0 := heightCompositionCornerBi D Sc i j a ha n
      (heightInductionCornerIdempotent D Sc i a ha (n + 1)) x with hz0def
    have hz0v : z0.val = φi₂ x.val := by
      change φi₂ 1 * φi₂ x.val = _
      rw [← map_mul, one_mul]
    have hz0 : z0 ∈ (heightCompositionCorner D Sc i j a ha n).toSVec.part q :=
      (heightCompositionCorner_mem_part_iff D Sc i j a ha n).2 (by
        rw [hz0v]; exact heightAppend_parity D Sc a ha i (n + 1) hxB)
    set u := heightCompositionCornerInclusion D Sc j i a ha n
      ((heightCompositionSuperCrossing D Sc i j a ha n).1 z0) with hudef
    have huv : u.val = koszulSign q d • (φi₂ x.val * c) := by
      change ((heightCompositionSuperCrossing D Sc i j a ha n).1 z0).val = _
      rw [heightCompositionSuperCrossing_apply D Sc i j a ha n _ hz0, hz0v]
    have hcross : (heightInductionCrossingApp D Sc i j a ha n (tensor Q₁ M)).1
        (btmul (heightInductionCorner D Sc i a ha (n + 1)) (tensor P₁ (tensor Q₁ M))
          (heightInductionCornerIdempotent D Sc i a ha (n + 1))
          (btmul P₁ (tensor Q₁ M) x (btmul Q₁ M y mm))) =
        btmul P₂ (tensor (heightInductionCorner D Sc i a ha n) (tensor Q₁ M)) u
          (btmul (heightInductionCorner D Sc i a ha n) (tensor Q₁ M)
            (heightInductionCornerIdempotent D Sc i a ha n) (btmul Q₁ M y mm)) := by
      change ((heightInductionFunctorComparison D Sc j i a ha n).inv.app (tensor Q₁ M)).1
          ((SuperBimodule.whiskerRight (heightCompositionSuperCrossing D Sc i j a ha n)
            (tensor Q₁ M)).1
            (((heightInductionFunctorComparison D Sc i j a ha n).hom.app (tensor Q₁ M)).1
              (btmul (heightInductionCorner D Sc i a ha (n + 1)) (tensor P₁ (tensor Q₁ M))
                (heightInductionCornerIdempotent D Sc i a ha (n + 1))
                (btmul P₁ (tensor Q₁ M) x (btmul Q₁ M y mm))))) = _
      rw [heightInductionFunctorComparison_hom_btmul, whiskerRight_btmul]
      change (assoc P₂ (heightInductionCorner D Sc i a ha n) (tensor Q₁ M)).hom.1
        ((SuperBimodule.whiskerRight (heightInductionCompositionIso D Sc j i a ha n).inv
          (tensor Q₁ M)).1 (btmul _ (tensor Q₁ M)
            ((heightCompositionSuperCrossing D Sc i j a ha n).1 z0) (btmul Q₁ M y mm))) = _
      rw [whiskerRight_btmul, heightInductionCompositionIso_inv_apply, assoc_hom_btmul]
    have hcounit : (heightSuperCounitComponent D Sc i a ha n M).1
        (btmul (heightInductionCorner D Sc i a ha n) (tensor Q₁ M)
          (heightInductionCornerIdempotent D Sc i a ha n) (btmul Q₁ M y mm)) =
          M.lact y.val mm := by
      change heightSuperCounitLinear D Sc i a ha n M _ = _
      rw [heightSuperCounitLinear_btmul_btmul]
      have hy : φi₁ 1 * y.val = y.val := y.2
      change M.lact (φi₁ 1 * y.val) mm = _
      rw [hy]
    obtain ⟨hmate, hmatev⟩ := mixedMateKernel_apply D Sc i j a ha n hx y
    set w := mixedMateKernelCorner D Sc i j a ha n x y with hwdef
    change (SuperBimodule.whiskerLeft Q₂
        (SuperBimodule.whiskerLeft P₂ (heightSuperCounitComponent D Sc i a ha n M))).1
        ((SuperBimodule.whiskerLeft Q₂
          (heightInductionCrossingApp D Sc i j a ha n (tensor Q₁ M))).1
          (btmul Q₂ _ (heightRestrictionCornerOf D Sc i a ha (n + 1) 1)
            (btmul (heightInductionCorner D Sc i a ha (n + 1)) (tensor P₁ (tensor Q₁ M))
              (heightInductionCornerIdempotent D Sc i a ha (n + 1))
              (btmul P₁ (tensor Q₁ M) x (btmul Q₁ M y mm))))) =
      (assoc Q₂ P₂ M).hom.1 ((SuperBimodule.whiskerRight (mixedMateKernel D Sc i j a ha n) M).1
        ((assoc P₁ Q₁ M).inv.1 (btmul P₁ (tensor Q₁ M) x (btmul Q₁ M y mm))))
    rw [whiskerLeft_btmul (hg := heightInductionCrossingApp_mem D Sc i j a ha n (tensor Q₁ M))
        (hm := heightRestrictionCornerOf_one_mem D Sc i a ha (n + 1)), zero_mul,
      Supercategory.sign_zero, one_smul, hcross]
    change (SuperBimodule.whiskerLeft Q₂
        (SuperBimodule.whiskerLeft P₂ (heightSuperCounitComponent D Sc i a ha n M))).1
        (btmul Q₂ (tensor P₂ (tensor (heightInductionCorner D Sc i a ha n) (tensor Q₁ M)))
          (heightRestrictionCornerOf D Sc i a ha (n + 1) 1)
          (btmul P₂ (tensor (heightInductionCorner D Sc i a ha n) (tensor Q₁ M)) u
            (btmul (heightInductionCorner D Sc i a ha n) (tensor Q₁ M)
              (heightInductionCornerIdempotent D Sc i a ha n) (btmul Q₁ M y mm)))) = _
    rw [whiskerLeft_btmul_even
        (hg := whiskerLeft_mem P₂ _ (heightSuperCounitComponent_mem D Sc i a ha n M)),
      whiskerLeft_btmul_even (hg := heightSuperCounitComponent_mem D Sc i a ha n M), hcounit,
      assoc_inv_btmul, whiskerRight_btmul, hmate, assoc_hom_btmul, ← btmul_ract_lact]
    have hw : (P₂).ract y.val u =
        (P₂).lact ((P₂).ract y.val u).val (heightInductionCornerIdempotent D Sc j a ha (n + 1)) := by
      apply Subtype.ext
      exact (((P₂).ract y.val u).2).symm
    rw [hw, ← lact_btmul, ← btmul_ract_lact]
    have hc : (Q₂).ract ((P₂).ract y.val u).val (heightRestrictionCornerOf D Sc i a ha (n + 1) 1) =
        w := by
      apply Subtype.ext
      change heightAppend D Sc a i (n + 1) 1 * (u.val * φj₂ y.val) = w.val
      rw [hmatev, huv, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← mul_assoc,
        ← map_mul, one_mul]
    rw [hc]

end OddMath.QuiverHecke.CyclotomicAction
