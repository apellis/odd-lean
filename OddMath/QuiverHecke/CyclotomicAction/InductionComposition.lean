/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.CornerPairing

/-!
# Composition of cyclotomic induction corners

Ports the corner comparison method of
`Categorification/KLR/CyclotomicAction/Comparison.lean` to two successive
cyclotomic super inductions. Multiplication is in algebra order:
`x ⊗ y ↦ x * φᵢ(y)`, with inverse `z ↦ z ⊗ eⱼ`.
The comparison is even; no interchange of odd factors is performed.
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i j : I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "A" => CyclotomicAlgebra D Sc a n
local notation "B" => CyclotomicAlgebra D Sc a (n + 1)
local notation "C" => CyclotomicAlgebra D Sc a (n + 1 + 1)
local notation "GA" => cyclotomicParity D Sc a ha n
local notation "GC" => cyclotomicParity D Sc a ha (n + 1 + 1)
local notation "φ" => cyclotomicAppend D Sc i a (n + 1)
local notation "ψ" => cyclotomicAppend D Sc j a n
local notation "θ" => NonUnitalAlgHom.comp φ ψ
local notation "V" => SuperBimodule.regularSVec GC
local notation "reg" => SuperBimodule.regular GC
local notation "P" => inductionCorner D Sc i a ha (n + 1)
local notation "Q" => inductionCorner D Sc j a ha n

/-- The composite inclusion preserves parity. -/
theorem compositionAppend_parity {p : ZMod 2} {x : A} (hx : x ∈ GA p) :
    θ x ∈ GC p :=
  cyclotomicAppend_parity D Sc i a ha (n + 1)
    (cyclotomicAppend_parity D Sc j a ha n hx)

/-- The two-colour left ideal `C θ(1) = C φᵢ(eⱼ)`. -/
def compositionCornerSubmodule : Submodule k C where
  carrier := {x | x * θ 1 = x}
  zero_mem' := zero_mul _
  add_mem' hx hy := by dsimp at *; rw [add_mul, hx, hy]
  smul_mem' c x hx := by dsimp at *; rw [smul_mul_assoc, hx]

theorem compositionCorner_odd_mem (x : C) (hx : x ∈ compositionCornerSubmodule D Sc i j a n) :
    (V).odd x ∈ compositionCornerSubmodule D Sc i j a n := by
  have he := (reg).ract_mem 0 (θ 1)
    (compositionAppend_parity D Sc i j a ha n (SetLike.one_mem_graded GA))
  have h := SVec.apply_proj_of_mem he 1 x
  change (V).proj 1 x * θ 1 = (V).proj (1 + 0) (x * θ 1) at h
  change x * θ 1 = x at hx
  change SuperBimodule.algProj GC 1 x * θ 1 = SuperBimodule.algProj GC 1 x
  simpa only [add_zero, SuperBimodule.regularSVec_proj, hx] using h

/-- The colour-cut ideal with the inherited parity. -/
def compositionCornerSpace : SVec k :=
  SVec.sub V (compositionCornerSubmodule D Sc i j a n) (compositionCorner_odd_mem D Sc i j a ha n)

theorem compositionCorner_left_mem (b x : C) (hx : x ∈ compositionCornerSubmodule D Sc i j a n) :
    b * x ∈ compositionCornerSubmodule D Sc i j a n := by
  change (b * x) * θ 1 = b * x
  rw [mul_assoc, hx]

theorem compositionCorner_right_mem (r : A) (x : C) :
    x * θ r ∈ compositionCornerSubmodule D Sc i j a n := by
  change (x * θ r) * θ 1 = x * θ r
  rw [mul_assoc, ← map_mul, mul_one]

/-- The `(C,A)`-superbimodule with right action through the composite inclusion. -/
def compositionCorner : SuperBimodule GC GA where
  toSVec := compositionCornerSpace D Sc i j a ha n
  lact :=
    { toFun := fun b => SVec.restrictHom ((reg).lact b) (compositionCorner_left_mem D Sc i j a n b)
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
        (fun x _ => compositionCorner_right_mem D Sc i j a n r x)
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
    (compositionCorner_left_mem D Sc i j a n b)
  ract_mem p r hr := SVec.restrictHom_mem
    ((reg).ract_mem p (θ r) (compositionAppend_parity D Sc i j a ha n hr))
    (fun x _ => compositionCorner_right_mem D Sc i j a n r x)


local notation "T" => compositionCorner D Sc i j a ha n

/-- Parity in the composite corner is inherited from the quotient algebra. -/
theorem compositionCorner_mem_part_iff {p : ZMod 2} {x : (T).toSVec} :
    x ∈ (T).toSVec.part p ↔ x.1 ∈ GC p := by
  change x ∈ (SVec.sub _ _ _).part p ↔ _
  rw [SVec.mem_sub_part_iff, mem_regularSVec_part_iff]

/-- Multiplication lands in the two-colour corner. -/
def compositionCornerBi : (P).toSVec →ₗ[k] (Q).toSVec →ₗ[k] (T).toSVec where
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
def compositionCornerLinear : (tensor P Q).toSVec →ₗ[k] (T).toSVec :=
  tensorLift (compositionCornerBi D Sc i j a ha n) (fun x b y => Subtype.ext (by
    change (x.1 * φ b) * φ y.1 = x.1 * φ (b * y.1)
    rw [map_mul, mul_assoc]))

@[simp] theorem compositionCornerLinear_btmul (x : (P).toSVec) (y : (Q).toSVec) :
    (compositionCornerLinear D Sc i j a ha n (btmul P Q x y)).1 = x.1 * φ y.1 := rfl

/-- The smaller two-colour corner embeds into the last-colour corner. -/
def compositionCornerInclusion : (T).toSVec →ₗ[k] (P).toSVec where
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
def compositionCornerInverseLinear : (T).toSVec →ₗ[k] (tensor P Q).toSVec where
  toFun z := btmul P Q (compositionCornerInclusion D Sc i j a ha n z)
    (inductionCornerIdempotent D Sc j a ha n)
  map_add' x y := by rw [map_add, btmul_add_left]
  map_smul' c x := by rw [map_smul, btmul_smul_left]; rfl

/-- Multiplication is even, proved on homogeneous tensor generators. -/
theorem compositionCornerLinear_mem :
    SVec.ofHom (compositionCornerLinear D Sc i j a ha n) ∈
      SVec.parityHom (tensor P Q).toSVec (T).toSVec 0 := by
  apply tensor_mem_parity_of_btmul
  intro p q x y hx hy
  apply (compositionCorner_mem_part_iff D Sc i j a ha n).mpr
  change x.1 * φ y.1 ∈ GC (p + q + 0)
  rw [add_zero]
  exact SetLike.GradedMul.mul_mem
    ((inductionCorner_mem_part_iff D Sc i a ha (n + 1)).mp hx)
    (cyclotomicAppend_parity D Sc i a ha (n + 1)
      ((inductionCorner_mem_part_iff D Sc j a ha n).mp hy))

/-- Inserting the even lower idempotent preserves parity. -/
theorem compositionCornerInverseLinear_mem :
    SVec.ofHom (compositionCornerInverseLinear D Sc i j a ha n) ∈
      SVec.parityHom (T).toSVec (tensor P Q).toSVec 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro p z hz
  apply btmul_mem_part
  · apply (inductionCorner_mem_part_iff D Sc i a ha (n + 1)).mpr
    exact (compositionCorner_mem_part_iff D Sc i j a ha n).mp hz
  · exact inductionCornerIdempotent_mem D Sc j a ha n

/-- Multiplication intertwines both algebra actions. -/
def compositionCornerHom : tensor P Q ⟶ T :=
  ⟨SVec.ofHom (compositionCornerLinear D Sc i j a ha n), by
    apply (isHom_iff_of_mem (compositionCornerLinear_mem D Sc i j a ha n)).mpr
    constructor
    · intro p c _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply tensor_hom_ext P Q
      intro x y
      apply Subtype.ext
      change (compositionCornerLinear D Sc i j a ha n
        ((tensor P Q).lact c (btmul P Q x y))).1 =
          c * (compositionCornerLinear D Sc i j a ha n (btmul P Q x y)).1
      rw [lact_btmul, compositionCornerLinear_btmul, compositionCornerLinear_btmul]
      exact mul_assoc c x.1 (φ y.1)
    · intro r
      apply tensor_hom_ext P Q
      intro x y
      apply Subtype.ext
      change (compositionCornerLinear D Sc i j a ha n
        ((tensor P Q).ract r (btmul P Q x y))).1 =
          (compositionCornerLinear D Sc i j a ha n (btmul P Q x y)).1 * φ (ψ r)
      rw [ract_btmul, compositionCornerLinear_btmul, compositionCornerLinear_btmul]
      change x.1 * φ (y.1 * ψ r) = (x.1 * φ y.1) * φ (ψ r)
      rw [map_mul, mul_assoc]⟩

/-- The insertion map intertwines both algebra actions. -/
def compositionCornerInv : T ⟶ tensor P Q :=
  ⟨SVec.ofHom (compositionCornerInverseLinear D Sc i j a ha n), by
    apply (isHom_iff_of_mem (compositionCornerInverseLinear_mem D Sc i j a ha n)).mpr
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
      have he : (Q).lact (ψ r) (inductionCornerIdempotent D Sc j a ha n) =
          (Q).ract r (inductionCornerIdempotent D Sc j a ha n) := by
        apply Subtype.ext
        change ψ r * ψ 1 = ψ 1 * ψ r
        rw [← map_mul, ← map_mul, mul_one, one_mul]
      rw [← he, ← btmul_ract_lact]
      rfl⟩

/-- Insertion followed by multiplication is the identity. -/
theorem compositionCornerLinear_inverse (z : (T).toSVec) :
    compositionCornerLinear D Sc i j a ha n
      (compositionCornerInverseLinear D Sc i j a ha n z) = z := by
  apply Subtype.ext
  exact z.2

/-- Multiplication followed by insertion is the identity on pure tensors. -/
theorem compositionCornerInverseLinear_btmul (x : (P).toSVec) (y : (Q).toSVec) :
    compositionCornerInverseLinear D Sc i j a ha n
      (compositionCornerLinear D Sc i j a ha n (btmul P Q x y)) = btmul P Q x y := by
  change btmul P Q ((P).ract y.1 x) (inductionCornerIdempotent D Sc j a ha n) = _
  rw [btmul_ract_lact]
  congr 1
  apply Subtype.ext
  exact y.2

/-- The even superbimodule comparison `C eᵢ ⊗_B B eⱼ ≅ C φᵢ(eⱼ)`. -/
def inductionCompositionIso : tensor P Q ≅ T where
  hom := compositionCornerHom D Sc i j a ha n
  inv := compositionCornerInv D Sc i j a ha n
  hom_inv_id := by
    apply SuperBimodule.hom_ext
    apply tensor_hom_ext P Q
    exact compositionCornerInverseLinear_btmul D Sc i j a ha n
  inv_hom_id := by
    apply SuperBimodule.hom_ext
    apply SVec.hom_ext
    exact compositionCornerLinear_inverse D Sc i j a ha n

/-- The comparison sends a pure tensor to the ordered product. -/
@[simp] theorem inductionCompositionIso_hom_btmul (x : (P).toSVec) (y : (Q).toSVec) :
    (((inductionCompositionIso D Sc i j a ha n).hom).1 (btmul P Q x y)).1 =
      x.1 * φ y.1 := rfl

/-- The inverse inserts the lower idempotent without a parity sign. -/
@[simp] theorem inductionCompositionIso_inv_apply (z : (T).toSVec) :
    ((inductionCompositionIso D Sc i j a ha n).inv).1 z =
      btmul P Q (compositionCornerInclusion D Sc i j a ha n z)
        (inductionCornerIdempotent D Sc j a ha n) := rfl

/-- The comparison is an even map. -/
theorem inductionCompositionIso_hom_mem :
    (inductionCompositionIso D Sc i j a ha n).hom ∈ Supercategory.parity (R := k) _ _ 0 :=
  mem_parity_iff.mpr (compositionCornerLinear_mem D Sc i j a ha n)

/-- The inverse comparison is an even map. -/
theorem inductionCompositionIso_inv_mem :
    (inductionCompositionIso D Sc i j a ha n).inv ∈ Supercategory.parity (R := k) _ _ 0 :=
  mem_parity_iff.mpr (compositionCornerInverseLinear_mem D Sc i j a ha n)

end OddMath.QuiverHecke
