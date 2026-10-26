/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightAdjunction
import OddMath.QuiverHecke.CyclotomicAction.CrossingTransformation

/-!
# The crossing on composed induction at every height

Supports the crossing of `Categorification/KLR/CyclotomicAction/GlobalCross.lean`
from the empty word. `heightLastCrossing` is the last-pair crossing of the
extended tower: on two strands it is the image of `affineLastCrossing` in the
height-two quotient, and above it is `cyclotomicLastCrossing`. The two-colour
corner of `InductionComposition`, the comparison of
`InductionFunctorComparison`, the signed corner map of `SuperCrossing` and the
transported crossing of `CrossingTransformation` use only the signed
intertwining and cut identities of the last crossing, and are restated along
`heightAppend`. The result `heightSuperInductionCrossing` is homogeneous of
parity `|i||j|`; at positive height it is built from the same corners as
`cyclotomicSuperInductionCrossing` (`heightInductionCorner_succ`).
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

section LastCrossing
variable (a : I → _root_.Polynomial k) (i j : I)

/-- The last-pair crossing of the extended tower, two strands up. -/
def heightLastCrossing : (n : ℕ) → heightAlgebra D Sc a (n + 1 + 1)
  | 0 => cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i j 0)
  | n + 1 => cyclotomicLastCrossing D Sc i j a n

theorem heightLastCrossing_parity (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    heightLastCrossing D Sc a i j n ∈
      heightParity D Sc a ha (n + 1 + 1) (D.parity i * D.parity j) := by
  cases n with
  | zero => exact cyclotomicMk_parity D Sc a ha 1 (affineLastCrossing_parity D Sc i j 0)
  | succ n => exact cyclotomicLastCrossing_parity D Sc i j a ha n

theorem heightLastCrossing_intertwines (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    {p : ZMod 2} {r : heightAlgebra D Sc a n} (hr : r ∈ heightParity D Sc a ha n p) :
    heightAppend D Sc a i (n + 1) (heightAppend D Sc a j n r) * heightLastCrossing D Sc a i j n =
      Supercategory.koszulSign p (D.parity i * D.parity j) •
        (heightLastCrossing D Sc a i j n *
          heightAppend D Sc a j (n + 1) (heightAppend D Sc a i n r)) := by
  cases n with
  | zero =>
    change cyclotomicMk D Sc a 1 (appendAlgebra D Sc i 1 (appendAlgebra D Sc j 0 r)) *
        cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i j 0) =
      Supercategory.koszulSign p (D.parity i * D.parity j) •
        (cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i j 0) *
          cyclotomicMk D Sc a 1 (appendAlgebra D Sc j 1 (appendAlgebra D Sc i 0 r)))
    rw [← map_mul, ← map_mul, ← map_zsmul]
    exact congrArg (cyclotomicMk D Sc a 1) (affineLastCrossing_intertwines D Sc i j 0 hr)
  | succ n => exact cyclotomicLastCrossing_intertwines D Sc i j a ha n hr

theorem heightLastCrossing_corner (n : ℕ) :
    heightAppend D Sc a i (n + 1) (heightAppend D Sc a j n 1) * heightLastCrossing D Sc a i j n =
      heightLastCrossing D Sc a i j n ∧
    heightLastCrossing D Sc a i j n * heightAppend D Sc a j (n + 1) (heightAppend D Sc a i n 1) =
      heightLastCrossing D Sc a i j n := by
  cases n with
  | zero =>
    change cyclotomicMk D Sc a 1 (appendAlgebra D Sc i 1 (appendAlgebra D Sc j 0 1)) *
        cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i j 0) =
        cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i j 0) ∧
      cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i j 0) *
        cyclotomicMk D Sc a 1 (appendAlgebra D Sc j 1 (appendAlgebra D Sc i 0 1)) =
        cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i j 0)
    rw [← map_mul, ← map_mul, (affineLastCrossing_corner D Sc i j 0).1,
      (affineLastCrossing_corner D Sc i j 0).2]
    exact ⟨rfl, rfl⟩
  | succ n => exact cyclotomicLastCrossing_corner D Sc i j a n

end LastCrossing

/-! ### From `InductionComposition` -/

section InductionComposition
variable (i j : I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "A" => heightAlgebra D Sc a n
local notation "B" => heightAlgebra D Sc a (n + 1)
local notation "C" => heightAlgebra D Sc a (n + 1 + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "GC" => heightParity D Sc a ha (n + 1 + 1)
local notation "φ" => heightAppend D Sc a i (n + 1)
local notation "ψ" => heightAppend D Sc a j n
local notation "θ" => NonUnitalAlgHom.comp φ ψ
local notation "V" => SuperBimodule.regularSVec GC
local notation "reg" => SuperBimodule.regular GC
local notation "P" => heightInductionCorner D Sc i a ha (n + 1)
local notation "Q" => heightInductionCorner D Sc j a ha n

/-- The composite inclusion preserves parity. -/
theorem heightCompositionAppend_parity {p : ZMod 2} {x : A} (hx : x ∈ GA p) :
    θ x ∈ GC p :=
  heightAppend_parity D Sc a ha i (n + 1)
    (heightAppend_parity D Sc a ha j n hx)

/-- The two-colour left ideal `C θ(1) = C φᵢ(eⱼ)`. -/
def heightCompositionCornerSubmodule : Submodule k C where
  carrier := {x | x * θ 1 = x}
  zero_mem' := zero_mul _
  add_mem' hx hy := by dsimp at *; rw [add_mul, hx, hy]
  smul_mem' c x hx := by dsimp at *; rw [smul_mul_assoc, hx]

theorem heightCompositionCorner_odd_mem (x : C) (hx : x ∈ heightCompositionCornerSubmodule D Sc i j a n) :
    (V).odd x ∈ heightCompositionCornerSubmodule D Sc i j a n := by
  have he := (reg).ract_mem 0 (θ 1)
    (heightCompositionAppend_parity D Sc i j a ha n (SetLike.one_mem_graded GA))
  have h := SVec.apply_proj_of_mem he 1 x
  change (V).proj 1 x * θ 1 = (V).proj (1 + 0) (x * θ 1) at h
  change x * θ 1 = x at hx
  change SuperBimodule.algProj GC 1 x * θ 1 = SuperBimodule.algProj GC 1 x
  simpa only [add_zero, SuperBimodule.regularSVec_proj, hx] using h

/-- The colour-cut ideal with the inherited parity. -/
def heightCompositionCornerSpace : SVec k :=
  SVec.sub V (heightCompositionCornerSubmodule D Sc i j a n) (heightCompositionCorner_odd_mem D Sc i j a ha n)

theorem heightCompositionCorner_left_mem (b x : C) (hx : x ∈ heightCompositionCornerSubmodule D Sc i j a n) :
    b * x ∈ heightCompositionCornerSubmodule D Sc i j a n := by
  change (b * x) * θ 1 = b * x
  rw [mul_assoc, hx]

theorem heightCompositionCorner_right_mem (r : A) (x : C) :
    x * θ r ∈ heightCompositionCornerSubmodule D Sc i j a n := by
  change (x * θ r) * θ 1 = x * θ r
  rw [mul_assoc, ← map_mul, mul_one]

/-- The `(C,A)`-superbimodule with right action through the composite inclusion. -/
def heightCompositionCorner : SuperBimodule GC GA where
  toSVec := heightCompositionCornerSpace D Sc i j a ha n
  lact :=
    { toFun := fun b => SVec.restrictHom ((reg).lact b) (heightCompositionCorner_left_mem D Sc i j a n b)
      map_add' := by
        intro b c
        apply SVec.hom_ext
        intro x
        apply Subtype.ext
        exact add_mul b c x.1
      map_smul' := by
        intro c b
        apply SVec.hom_ext
        intro x
        apply Subtype.ext
        exact smul_mul_assoc c b x.1 }
  ract :=
    { toFun := fun r => SVec.restrictHom ((reg).ract (θ r))
        (fun x _ => heightCompositionCorner_right_mem D Sc i j a n r x)
      map_add' := by
        intro r s
        apply SVec.hom_ext
        intro x
        apply Subtype.ext
        change x.1 * θ (r + s) = x.1 * θ r + x.1 * θ s
        rw [map_add, mul_add]
      map_smul' := by
        intro c r
        apply SVec.hom_ext
        intro x
        apply Subtype.ext
        change x.1 * θ (c • r) = c • (x.1 * θ r)
        rw [map_smul, mul_smul_comm] }
  lact_one := by
    apply SVec.hom_ext
    intro x
    apply Subtype.ext
    exact one_mul x.1
  lact_mul b c := by
    apply SVec.hom_ext
    intro x
    apply Subtype.ext
    exact mul_assoc b c x.1
  ract_one := by
    apply SVec.hom_ext
    intro x
    apply Subtype.ext
    exact x.2
  ract_mul r s := by
    apply SVec.hom_ext
    intro x
    apply Subtype.ext
    change x.1 * θ (r * s) = (x.1 * θ r) * θ s
    rw [map_mul, mul_assoc]
  lact_ract b r := by
    apply SVec.hom_ext
    intro x
    apply Subtype.ext
    exact mul_assoc b x.1 (θ r)
  lact_mem p b hb := SVec.restrictHom_mem ((reg).lact_mem p b hb)
    (heightCompositionCorner_left_mem D Sc i j a n b)
  ract_mem p r hr := SVec.restrictHom_mem
    ((reg).ract_mem p (θ r) (heightCompositionAppend_parity D Sc i j a ha n hr))
    (fun x _ => heightCompositionCorner_right_mem D Sc i j a n r x)


local notation "T" => heightCompositionCorner D Sc i j a ha n

/-- Parity in the composite corner is inherited from the quotient algebra. -/
theorem heightCompositionCorner_mem_part_iff {p : ZMod 2} {x : (T).toSVec} :
    x ∈ (T).toSVec.part p ↔ x.1 ∈ GC p := by
  change x ∈ (SVec.sub _ _ _).part p ↔ _
  rw [SVec.mem_sub_part_iff, mem_regularSVec_part_iff]

/-- Multiplication lands in the two-colour corner. -/
def heightCompositionCornerBi : (P).toSVec →ₗ[k] (Q).toSVec →ₗ[k] (T).toSVec where
  toFun x :=
    { toFun := fun y => ⟨x.1 * φ y.1, by
        change (x.1 * φ y.1) * φ (ψ 1) = x.1 * φ y.1
        rw [mul_assoc, ← map_mul, y.2]⟩
      map_add' := fun y z => Subtype.ext (by
        change x.1 * φ (y.1 + z.1) = x.1 * φ y.1 + x.1 * φ z.1
        rw [map_add, mul_add])
      map_smul' := fun c y => Subtype.ext (by
        change x.1 * φ (c • y.1) = c • (x.1 * φ y.1)
        rw [map_smul, mul_smul_comm]) }
  map_add' x y := by ext z; exact Subtype.ext (add_mul x.1 y.1 (φ z.1))
  map_smul' c x := by ext y; exact Subtype.ext (smul_mul_assoc c x.1 (φ y.1))

/-- The balanced multiplication comparison. -/
def heightCompositionCornerLinear : (tensor P Q).toSVec →ₗ[k] (T).toSVec :=
  tensorLift (heightCompositionCornerBi D Sc i j a ha n) (fun x b y => Subtype.ext (by
    change (x.1 * φ b) * φ y.1 = x.1 * φ (b * y.1)
    rw [map_mul, mul_assoc]))

@[simp] theorem heightCompositionCornerLinear_btmul (x : (P).toSVec) (y : (Q).toSVec) :
    (heightCompositionCornerLinear D Sc i j a ha n (btmul P Q x y)).1 = x.1 * φ y.1 := rfl

/-- The smaller two-colour corner embeds into the last-colour corner. -/
def heightCompositionCornerInclusion : (T).toSVec →ₗ[k] (P).toSVec where
  toFun z := ⟨z.1, by
    change z.1 * φ 1 = z.1
    have hz : z.1 * φ (ψ 1) = z.1 := z.2
    calc
      z.1 * φ 1 = (z.1 * φ (ψ 1)) * φ 1 := by rw [hz]
      _ = z.1 * φ (ψ 1) := by rw [mul_assoc, ← map_mul, mul_one]
      _ = z.1 := hz⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Insert the lower colour idempotent to invert multiplication. -/
def heightCompositionCornerInverseLinear : (T).toSVec →ₗ[k] (tensor P Q).toSVec where
  toFun z := btmul P Q (heightCompositionCornerInclusion D Sc i j a ha n z)
    (heightInductionCornerIdempotent D Sc j a ha n)
  map_add' x y := by rw [map_add, btmul_add_left]
  map_smul' c x := by rw [map_smul, btmul_smul_left]; rfl

/-- Multiplication is even, proved on homogeneous tensor generators. -/
theorem heightCompositionCornerLinear_mem :
    SVec.ofHom (heightCompositionCornerLinear D Sc i j a ha n) ∈
      SVec.parityHom (tensor P Q).toSVec (T).toSVec 0 := by
  apply tensor_mem_parity_of_btmul
  intro p q x y hx hy
  apply (heightCompositionCorner_mem_part_iff D Sc i j a ha n).mpr
  change x.1 * φ y.1 ∈ GC (p + q + 0)
  rw [add_zero]
  exact SetLike.GradedMul.mul_mem
    ((heightInductionCorner_mem_part_iff D Sc i a ha (n + 1)).mp hx)
    (heightAppend_parity D Sc a ha i (n + 1)
      ((heightInductionCorner_mem_part_iff D Sc j a ha n).mp hy))

/-- Inserting the even lower idempotent preserves parity. -/
theorem heightCompositionCornerInverseLinear_mem :
    SVec.ofHom (heightCompositionCornerInverseLinear D Sc i j a ha n) ∈
      SVec.parityHom (T).toSVec (tensor P Q).toSVec 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro p z hz
  apply btmul_mem_part
  · apply (heightInductionCorner_mem_part_iff D Sc i a ha (n + 1)).mpr
    exact (heightCompositionCorner_mem_part_iff D Sc i j a ha n).mp hz
  · exact heightInductionCornerIdempotent_mem D Sc j a ha n

/-- Multiplication intertwines both algebra actions. -/
def heightCompositionCornerHom : tensor P Q ⟶ T :=
  ⟨SVec.ofHom (heightCompositionCornerLinear D Sc i j a ha n), by
    apply (isHom_iff_of_mem (heightCompositionCornerLinear_mem D Sc i j a ha n)).mpr
    constructor
    · intro p c _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply tensor_hom_ext P Q
      intro x y
      apply Subtype.ext
      change (heightCompositionCornerLinear D Sc i j a ha n
        ((tensor P Q).lact c (btmul P Q x y))).1 =
          c * (heightCompositionCornerLinear D Sc i j a ha n (btmul P Q x y)).1
      rw [lact_btmul, heightCompositionCornerLinear_btmul, heightCompositionCornerLinear_btmul]
      exact mul_assoc c x.1 (φ y.1)
    · intro r
      apply tensor_hom_ext P Q
      intro x y
      apply Subtype.ext
      change (heightCompositionCornerLinear D Sc i j a ha n
        ((tensor P Q).ract r (btmul P Q x y))).1 =
          (heightCompositionCornerLinear D Sc i j a ha n (btmul P Q x y)).1 * φ (ψ r)
      rw [ract_btmul, heightCompositionCornerLinear_btmul, heightCompositionCornerLinear_btmul]
      change x.1 * φ (y.1 * ψ r) = (x.1 * φ y.1) * φ (ψ r)
      rw [map_mul, mul_assoc]⟩

/-- The insertion map intertwines both algebra actions. -/
def heightCompositionCornerInv : T ⟶ tensor P Q :=
  ⟨SVec.ofHom (heightCompositionCornerInverseLinear D Sc i j a ha n), by
    apply (isHom_iff_of_mem (heightCompositionCornerInverseLinear_mem D Sc i j a ha n)).mpr
    constructor
    · intro p c _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply SVec.hom_ext
      intro z
      change btmul P Q _ _ = (tensor P Q).lact c (btmul P Q _ _)
      rw [lact_btmul]
      rfl
    · intro r
      apply SVec.hom_ext
      intro z
      change btmul P Q _ _ = (tensor P Q).ract r (btmul P Q _ _)
      rw [ract_btmul]
      have he : (Q).lact (ψ r) (heightInductionCornerIdempotent D Sc j a ha n) =
          (Q).ract r (heightInductionCornerIdempotent D Sc j a ha n) := by
        apply Subtype.ext
        change ψ r * ψ 1 = ψ 1 * ψ r
        rw [← map_mul, ← map_mul, mul_one, one_mul]
      rw [← he, ← btmul_ract_lact]
      rfl⟩

/-- Insertion followed by multiplication is the identity. -/
theorem heightCompositionCornerLinear_inverse (z : (T).toSVec) :
    heightCompositionCornerLinear D Sc i j a ha n
      (heightCompositionCornerInverseLinear D Sc i j a ha n z) = z := by
  apply Subtype.ext
  exact z.2

/-- Multiplication followed by insertion is the identity on pure tensors. -/
theorem heightCompositionCornerInverseLinear_btmul (x : (P).toSVec) (y : (Q).toSVec) :
    heightCompositionCornerInverseLinear D Sc i j a ha n
      (heightCompositionCornerLinear D Sc i j a ha n (btmul P Q x y)) = btmul P Q x y := by
  change btmul P Q ((P).ract y.1 x) (heightInductionCornerIdempotent D Sc j a ha n) = _
  rw [btmul_ract_lact]
  congr 1
  apply Subtype.ext
  exact y.2

/-- The even superbimodule comparison `C eᵢ ⊗_B B eⱼ ≅ C φᵢ(eⱼ)`. -/
def heightInductionCompositionIso : tensor P Q ≅ T where
  hom := heightCompositionCornerHom D Sc i j a ha n
  inv := heightCompositionCornerInv D Sc i j a ha n
  hom_inv_id := by
    apply SuperBimodule.hom_ext
    apply tensor_hom_ext P Q
    exact heightCompositionCornerInverseLinear_btmul D Sc i j a ha n
  inv_hom_id := by
    apply SuperBimodule.hom_ext
    apply SVec.hom_ext
    exact heightCompositionCornerLinear_inverse D Sc i j a ha n

/-- The comparison sends a pure tensor to the ordered product. -/
@[simp] theorem heightInductionCompositionIso_hom_btmul (x : (P).toSVec) (y : (Q).toSVec) :
    (((heightInductionCompositionIso D Sc i j a ha n).hom).1 (btmul P Q x y)).1 =
      x.1 * φ y.1 := rfl

/-- The inverse inserts the lower idempotent without a parity sign. -/
@[simp] theorem heightInductionCompositionIso_inv_apply (z : (T).toSVec) :
    ((heightInductionCompositionIso D Sc i j a ha n).inv).1 z =
      btmul P Q (heightCompositionCornerInclusion D Sc i j a ha n z)
        (heightInductionCornerIdempotent D Sc j a ha n) := rfl

/-- The comparison is an even map. -/
theorem heightInductionCompositionIso_hom_mem :
    (heightInductionCompositionIso D Sc i j a ha n).hom ∈ Supercategory.parity (R := k) _ _ 0 :=
  mem_parity_iff.mpr (heightCompositionCornerLinear_mem D Sc i j a ha n)

/-- The inverse comparison is an even map. -/
theorem heightInductionCompositionIso_inv_mem :
    (heightInductionCompositionIso D Sc i j a ha n).inv ∈ Supercategory.parity (R := k) _ _ 0 :=
  mem_parity_iff.mpr (heightCompositionCornerInverseLinear_mem D Sc i j a ha n)

end InductionComposition

/-! ### From `InductionFunctorComparison` -/

section InductionFunctorComparison
variable (i j : I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "P" => heightInductionCorner D Sc i a ha (n + 1)
local notation "Q" => heightInductionCorner D Sc j a ha n
local notation "T" => heightCompositionCorner D Sc i j a ha n
local notation "F" => heightSuperInduction D Sc j a ha n ⋙
  heightSuperInduction D Sc i a ha (n + 1)

/-- Induction by the two-colour corner. -/
def heightCompositionCornerFunctor :
    HeightModules D Sc a ha n ⥤ HeightModules D Sc a ha (n + 1 + 1) where
  obj M := tensor T M
  map f := whiskerLeft T f
  map_id M := whiskerLeft_id _ M
  map_comp f g := whiskerLeft_comp _ f g

instance compositionCornerFunctor_additive :
    (heightCompositionCornerFunctor D Sc i j a ha n).Additive where
  map_add := by intros; apply whiskerLeft_add

instance compositionCornerFunctor_linear :
    (heightCompositionCornerFunctor D Sc i j a ha n).Linear k where
  map_smul := by intros; apply whiskerLeft_smul

instance compositionCornerFunctor_super :
    Supercategory.IsSuperfunctor k (heightCompositionCornerFunctor D Sc i j a ha n) where
  map_mem := fun hf => whiskerLeft_mem _ _ hf

/-- The corner isomorphism after tensoring with a supermodule. -/
def heightInductionCompositionTensorIso (M : HeightModules D Sc a ha n) :
    tensor (tensor P Q) M ≅ tensor T M where
  hom := whiskerRight (heightInductionCompositionIso D Sc i j a ha n).hom M
  inv := whiskerRight (heightInductionCompositionIso D Sc i j a ha n).inv M
  hom_inv_id := by rw [← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight]
  inv_hom_id := by rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]

/-- Reassociate, then multiply the two induction corners. -/
def heightInductionFunctorComparisonApp (M : HeightModules D Sc a ha n) :
    (F).obj M ≅ (heightCompositionCornerFunctor D Sc i j a ha n).obj M :=
  (assoc P Q M).symm ≪≫ heightInductionCompositionTensorIso D Sc i j a ha n M

/-- The comparison has even parity. -/
theorem heightInductionFunctorComparisonApp_hom_mem (M : HeightModules D Sc a ha n) :
    (heightInductionFunctorComparisonApp D Sc i j a ha n M).hom ∈
      Supercategory.parity (R := k) _ _ 0 := by
  change ((assoc P Q M).inv ≫
    whiskerRight (heightInductionCompositionIso D Sc i j a ha n).hom M) ∈
      Supercategory.parity (R := k) (tensor P (tensor Q M)) (tensor T M) 0
  simpa only [add_zero] using Supercategory.comp_mem
    (assoc_inv_mem P Q M)
    (whiskerRight_mem _ (heightInductionCompositionIso_hom_mem D Sc i j a ha n) M)

/-- Its inverse is even as well. -/
theorem heightInductionFunctorComparisonApp_inv_mem (M : HeightModules D Sc a ha n) :
    (heightInductionFunctorComparisonApp D Sc i j a ha n M).inv ∈
      Supercategory.parity (R := k) _ _ 0 := by
  change (whiskerRight (heightInductionCompositionIso D Sc i j a ha n).inv M ≫
    (assoc P Q M).hom) ∈
      Supercategory.parity (R := k) (tensor T M) (tensor P (tensor Q M)) 0
  simpa only [add_zero] using Supercategory.comp_mem
    (whiskerRight_mem _ (heightInductionCompositionIso_inv_mem D Sc i j a ha n) M)
    (assoc_hom_mem P Q M)

/-- Naturality includes all homogeneous and inhomogeneous module maps. -/
theorem heightInductionFunctorComparisonApp_naturality
    {M N : HeightModules D Sc a ha n} (f : M ⟶ N) :
    (F).map f ≫ (heightInductionFunctorComparisonApp D Sc i j a ha n N).hom =
      (heightInductionFunctorComparisonApp D Sc i j a ha n M).hom ≫
        (heightCompositionCornerFunctor D Sc i j a ha n).map f := by
  have hassoc : whiskerLeft P (whiskerLeft Q f) ≫ (assoc P Q N).inv =
      (assoc P Q M).inv ≫ whiskerLeft (tensor P Q) f := by
    apply (cancel_mono (assoc P Q N).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [assoc_naturality_right P Q M f, Iso.inv_hom_id_assoc]
  have hcorner : whiskerLeft (tensor P Q) f ≫
      whiskerRight (heightInductionCompositionIso D Sc i j a ha n).hom N =
      whiskerRight (heightInductionCompositionIso D Sc i j a ha n).hom M ≫ whiskerLeft T f := by
    refine Supercategory.induction_on (R := k) f ?_ (fun q g hg => ?_)
      (fun g h hg hh => ?_)
    · rw [whiskerLeft_zero, whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
    · have h := super_interchange (tensor P Q) g
        (heightInductionCompositionIso_hom_mem D Sc i j a ha n) hg
      rw [Supercategory.koszulSign_zero_left, one_smul] at h
      exact h.symm
    · rw [whiskerLeft_add, whiskerLeft_add, Preadditive.add_comp,
        Preadditive.comp_add, hg, hh]
  change whiskerLeft P (whiskerLeft Q f) ≫ ((assoc P Q N).inv ≫
    whiskerRight (heightInductionCompositionIso D Sc i j a ha n).hom N) =
    ((assoc P Q M).inv ≫ whiskerRight (heightInductionCompositionIso D Sc i j a ha n).hom M) ≫
      whiskerLeft T f
  rw [← Category.assoc, hassoc, Category.assoc, hcorner, Category.assoc]

/-- Successive cyclotomic induction is naturally isomorphic to two-colour corner induction. -/
def heightInductionFunctorComparison : F ≅ heightCompositionCornerFunctor D Sc i j a ha n :=
  NatIso.ofComponents (heightInductionFunctorComparisonApp D Sc i j a ha n)
    (fun f => heightInductionFunctorComparisonApp_naturality D Sc i j a ha n f)

/-- On pure tensors the comparison multiplies the two corner factors in order. -/
@[simp] theorem heightInductionFunctorComparison_hom_btmul
    (M : HeightModules D Sc a ha n) (x : (P).toSVec) (y : (Q).toSVec)
    (m : M.toSVec) :
    ((heightInductionFunctorComparison D Sc i j a ha n).hom.app M).1
      (btmul P (tensor Q M) x (btmul Q M y m)) =
      btmul T M (heightCompositionCornerBi D Sc i j a ha n x y) m := by
  change (whiskerRight (heightInductionCompositionIso D Sc i j a ha n).hom M).1
    ((assoc P Q M).inv.1 (btmul P (tensor Q M) x (btmul Q M y m))) = _
  rw [assoc_inv_btmul, whiskerRight_btmul]
  rfl

end InductionFunctorComparison

/-! ### From `SuperCrossing` -/

section SuperCrossing
variable (i j : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => heightCompositionCorner D Sc i j a ha n
local notation "Q" => heightCompositionCorner D Sc j i a ha n
local notation "GC" => heightParity D Sc a ha (n + 1 + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "c" => heightLastCrossing D Sc a i j n
local notation "d" => D.parity i * D.parity j

private theorem heightCrossing_mul_mem (x : heightAlgebra D Sc a (n + 1 + 1))
    (_hx : x ∈ heightCompositionCornerSubmodule D Sc i j a n) :
    x * c ∈ heightCompositionCornerSubmodule D Sc j i a n := by
  change (x * c) * heightAppend D Sc a j (n + 1) (heightAppend D Sc a i n 1) = x * c
  rw [mul_assoc, (heightLastCrossing_corner D Sc a i j n).2]

/-- Parity sign followed by right multiplication by the concrete crossing. -/
def heightCompositionCrossingLinear : (P).toSVec ⟶ (Q).toSVec :=
  SVec.ofHom ((P).toSVec.sgn d) ≫
    SVec.restrictHom ((SuperBimodule.regular GC).ract c) (heightCrossing_mul_mem D Sc i j a n)

/-- The crossing map has parity `|i||j|`. -/
theorem heightCompositionCrossingLinear_parity :
    heightCompositionCrossingLinear D Sc i j a ha n ∈ SVec.parityHom (P).toSVec (Q).toSVec d := by
  change heightCompositionCrossingLinear D Sc i j a ha n ∈ parity (R := k) (P).toSVec (Q).toSVec d
  unfold heightCompositionCrossingLinear
  have hd := SVec.restrictHom_mem (hU := heightCompositionCorner_odd_mem D Sc i j a ha n)
    (hU' := heightCompositionCorner_odd_mem D Sc j i a ha n)
    ((SuperBimodule.regular GC).ract_mem d c
      (heightLastCrossing_parity D Sc a i j ha n)) (heightCrossing_mul_mem D Sc i j a n)
  simpa only [heightCompositionCorner, heightCompositionCornerSpace, SuperBimodule.regular, zero_add] using
    Supercategory.comp_mem (SVec.sgn_mem (P).toSVec d) hd

private theorem heightCrossing_sgn_action {p : ZMod 2} {f : (P).toSVec ⟶ (P).toSVec}
    (hf : f ∈ SVec.parityHom (P).toSVec (P).toSVec p) (x : (P).toSVec) :
    (P).toSVec.sgn d (f x) = sign k (p * d) • f ((P).toSVec.sgn d x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf d) x

/-- The two action laws follow from the proved signed crossing intertwiner. -/
theorem heightCompositionCrossingLinear_isHom :
    SuperBimodule.IsHom P Q (heightCompositionCrossingLinear D Sc i j a ha n) := by
  apply (SuperBimodule.isHom_iff_of_mem (heightCompositionCrossingLinear_parity D Sc i j a ha n)).2
  constructor
  · intro p b hb
    apply SVec.hom_ext
    intro x
    have h := heightCrossing_sgn_action D Sc i j a ha n ((P).lact_mem p b hb) x
    apply Subtype.ext
    change ((P).toSVec.sgn d ((P).lact b x)).val * c =
      sign k (p * d) • (b * (((P).toSVec.sgn d x).val * c))
    rw [h]
    change (sign k (p * d) • (b * ((P).toSVec.sgn d x).val)) * c = _
    rw [smul_mul_assoc, mul_assoc]
  · intro r
    induction r using SuperBimodule.alg_induction_on GA with
    | zero => simp
    | add r s hr hs => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hr, hs]
    | hom p r hr =>
      apply SVec.hom_ext
      intro x
      have h := heightCrossing_sgn_action D Sc i j a ha n ((P).ract_mem p r hr) x
      apply Subtype.ext
      change ((P).toSVec.sgn d ((P).ract r x)).val * c =
        (((P).toSVec.sgn d x).val * c) *
          heightAppend D Sc a j (n + 1) (heightAppend D Sc a i n r)
      rw [h]
      change (sign k (p * d) • (((P).toSVec.sgn d x).val *
        heightAppend D Sc a i (n + 1) (heightAppend D Sc a j n r))) * c = _
      rw [smul_mul_assoc, mul_assoc, heightLastCrossing_intertwines D Sc a i j ha n hr,
        mul_smul_comm, Supercategory.sign_mul, Int.cast_smul_eq_zsmul, koszulSign_smul_smul, mul_assoc]

/-- The homogeneous superbimodule map between the two composition corners. -/
def heightCompositionSuperCrossing : P ⟶ Q :=
  ⟨heightCompositionCrossingLinear D Sc i j a ha n, heightCompositionCrossingLinear_isHom D Sc i j a ha n⟩

theorem heightCompositionSuperCrossing_parity :
    heightCompositionSuperCrossing D Sc i j a ha n ∈ parity (R := k) P Q d :=
  SuperBimodule.mem_parity_iff.2 (heightCompositionCrossingLinear_parity D Sc i j a ha n)

/-- Evaluation on a homogeneous element displays the sign explicitly. -/
theorem heightCompositionSuperCrossing_apply {p : ZMod 2} (x : (P).toSVec)
    (hx : x ∈ (P).toSVec.part p) :
    ((heightCompositionSuperCrossing D Sc i j a ha n).1 x).val =
      koszulSign p d • (x.val * c) := by
  change ((P).toSVec.sgn d x).val * c = _
  rw [SVec.sgn_apply_of_mem d hx]
  change (sign k (p * d) • x.val) * c = _
  rw [smul_mul_assoc, Supercategory.sign_mul, Int.cast_smul_eq_zsmul]

end SuperCrossing

/-! ### From `CrossingTransformation` -/

section CrossingTransformation
variable (i j : I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => heightCompositionCorner D Sc i j a ha n
local notation "Q" => heightCompositionCorner D Sc j i a ha n
local notation "F" => heightSuperInduction D Sc j a ha n ⋙
  heightSuperInduction D Sc i a ha (n + 1)
local notation "G" => heightSuperInduction D Sc i a ha n ⋙
  heightSuperInduction D Sc j a ha (n + 1)
local notation "d" => D.parity i * D.parity j
local notation "e" => heightInductionFunctorComparison D Sc i j a ha n
local notation "e'" => heightInductionFunctorComparison D Sc j i a ha n

/-- Transport the corner crossing along the two even comparison isomorphisms. -/
def heightInductionCrossingApp (M : HeightModules D Sc a ha n) : (F).obj M ⟶ (G).obj M :=
  (e).hom.app M ≫ whiskerRight (heightCompositionSuperCrossing D Sc i j a ha n) M ≫ (e').inv.app M

/-- The transported crossing has parity `|i||j|`. -/
theorem heightInductionCrossingApp_mem (M : HeightModules D Sc a ha n) :
    heightInductionCrossingApp D Sc i j a ha n M ∈ parity (R := k) _ _ d := by
  change ((heightInductionFunctorComparisonApp D Sc i j a ha n M).hom ≫
    whiskerRight (heightCompositionSuperCrossing D Sc i j a ha n) M ≫
      (heightInductionFunctorComparisonApp D Sc j i a ha n M).inv) ∈
        parity (R := k) ((F).obj M) ((G).obj M) d
  simpa only [zero_add, add_zero] using comp_mem
    (heightInductionFunctorComparisonApp_hom_mem D Sc i j a ha n M)
    (comp_mem (whiskerRight_mem P (heightCompositionSuperCrossing_parity D Sc i j a ha n) M)
      (heightInductionFunctorComparisonApp_inv_mem D Sc j i a ha n M))

/-- The comparison introduces no additional naturality sign. -/
theorem heightInductionCrossingApp_naturality
    {M N : HeightModules D Sc a ha n} {q : ZMod 2} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) M N q) :
    (F).map f ≫ heightInductionCrossingApp D Sc i j a ha n N =
      koszulSign d q • (heightInductionCrossingApp D Sc i j a ha n M ≫ (G).map f) := by
  have hcross : whiskerLeft P f ≫ whiskerRight (heightCompositionSuperCrossing D Sc i j a ha n) N =
      koszulSign d q • (whiskerRight (heightCompositionSuperCrossing D Sc i j a ha n) M ≫
        whiskerLeft Q f) := by
    rw [super_interchange P f (heightCompositionSuperCrossing_parity D Sc i j a ha n) hf,
      koszulSign_smul_smul]
  have he := (e).hom.naturality f
  have he' := (e').inv.naturality f
  change (F).map f ≫ (e).hom.app N = (e).hom.app M ≫ whiskerLeft P f at he
  change whiskerLeft Q f ≫ (e').inv.app N = (e').inv.app M ≫ (G).map f at he'
  unfold heightInductionCrossingApp
  rw [← Category.assoc, he, Category.assoc, ← Category.assoc (whiskerLeft P f),
    hcross, Linear.smul_comp, Linear.comp_smul, Category.assoc, he']
  simp only [Category.assoc]

/-- The homogeneous supernatural crossing between the composed induction superfunctors. -/
def heightSuperInductionCrossing : SuperNatTrans k F G where
  app p M := if p = d then heightInductionCrossingApp D Sc i j a ha n M else 0
  app_mem p M := by
    split_ifs with h
    · subst p
      exact heightInductionCrossingApp_mem D Sc i j a ha n M
    · exact Submodule.zero_mem _
  naturality p M N q f hf := by
    split_ifs with h
    · subst p
      exact heightInductionCrossingApp_naturality D Sc i j a ha n f hf
    · simp

/-- All components except parity `|i||j|` vanish. -/
theorem heightSuperInductionCrossing_homogeneous :
    (heightSuperInductionCrossing D Sc i j a ha n).IsHomogeneous d := by
  intro q h
  funext M
  simp [heightSuperInductionCrossing, h]

/-- The component of parity `|i||j|` is precisely the transported corner crossing. -/
@[simp] theorem heightSuperInductionCrossing_app
    (M : HeightModules D Sc a ha n) :
    (heightSuperInductionCrossing D Sc i j a ha n).app d M =
      (e).hom.app M ≫ whiskerRight (heightCompositionSuperCrossing D Sc i j a ha n) M ≫
        (e').inv.app M := by
  simp [heightSuperInductionCrossing, heightInductionCrossingApp]

end CrossingTransformation

end OddMath.QuiverHecke.CyclotomicAction
