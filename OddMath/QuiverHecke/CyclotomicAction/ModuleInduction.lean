import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import StringDiagrams.Super.SVec
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Module induction

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
end

end

section

/-!
# The two-induction functor comparison

Ports the comparison in `Categorification/KLR/CyclotomicAction/Comparison.lean`
and the induction functors in `CyclotomicAction/SuperQuotient.lean` to supermodules.
The balanced tensor associator identifies successive induction with tensoring
by the two-colour corner. This even natural isomorphism is the comparison
needed to transport the corner crossing to composed induction functors.
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i j : I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "P" => inductionCorner D Sc i a ha (n + 1)
local notation "Q" => inductionCorner D Sc j a ha n
local notation "T" => compositionCorner D Sc i j a ha n
local notation "F" => cyclotomicSuperInduction D Sc j a ha n ⋙
  cyclotomicSuperInduction D Sc i a ha (n + 1)

/-- Induction by the two-colour corner. -/
def compositionCornerFunctor :
    CyclotomicSupermodules D Sc a ha n ⥤ CyclotomicSupermodules D Sc a ha (n + 1 + 1) where
  obj M := tensor T M
  map f := whiskerLeft T f
  map_id M := whiskerLeft_id _ M
  map_comp f g := whiskerLeft_comp _ f g

instance compositionCornerFunctor_additive :
    (compositionCornerFunctor D Sc i j a ha n).Additive where
  map_add := by intros; apply whiskerLeft_add

instance compositionCornerFunctor_linear :
    (compositionCornerFunctor D Sc i j a ha n).Linear k where
  map_smul := by intros; apply whiskerLeft_smul

instance compositionCornerFunctor_super :
    Supercategory.IsSuperfunctor k (compositionCornerFunctor D Sc i j a ha n) where
  map_mem := fun hf => whiskerLeft_mem _ _ hf

/-- The corner isomorphism after tensoring with a supermodule. -/
def inductionCompositionTensorIso (M : CyclotomicSupermodules D Sc a ha n) :
    tensor (tensor P Q) M ≅ tensor T M where
  hom := whiskerRight (inductionCompositionIso D Sc i j a ha n).hom M
  inv := whiskerRight (inductionCompositionIso D Sc i j a ha n).inv M
  hom_inv_id := by rw [← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight]
  inv_hom_id := by rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]

/-- Reassociate, then multiply the two induction corners. -/
def inductionFunctorComparisonApp (M : CyclotomicSupermodules D Sc a ha n) :
    (F).obj M ≅ (compositionCornerFunctor D Sc i j a ha n).obj M :=
  (assoc P Q M).symm ≪≫ inductionCompositionTensorIso D Sc i j a ha n M

/-- The comparison has even parity. -/
theorem inductionFunctorComparisonApp_hom_mem (M : CyclotomicSupermodules D Sc a ha n) :
    (inductionFunctorComparisonApp D Sc i j a ha n M).hom ∈
      Supercategory.parity (R := k) _ _ 0 := by
  change ((assoc P Q M).inv ≫
    whiskerRight (inductionCompositionIso D Sc i j a ha n).hom M) ∈
      Supercategory.parity (R := k) (tensor P (tensor Q M)) (tensor T M) 0
  simpa only [add_zero] using Supercategory.comp_mem
    (assoc_inv_mem P Q M)
    (whiskerRight_mem _ (inductionCompositionIso_hom_mem D Sc i j a ha n) M)

/-- Its inverse is even as well. -/
theorem inductionFunctorComparisonApp_inv_mem (M : CyclotomicSupermodules D Sc a ha n) :
    (inductionFunctorComparisonApp D Sc i j a ha n M).inv ∈
      Supercategory.parity (R := k) _ _ 0 := by
  change (whiskerRight (inductionCompositionIso D Sc i j a ha n).inv M ≫
    (assoc P Q M).hom) ∈
      Supercategory.parity (R := k) (tensor T M) (tensor P (tensor Q M)) 0
  simpa only [add_zero] using Supercategory.comp_mem
    (whiskerRight_mem _ (inductionCompositionIso_inv_mem D Sc i j a ha n) M)
    (assoc_hom_mem P Q M)

/-- Naturality includes all homogeneous and inhomogeneous module maps. -/
theorem inductionFunctorComparisonApp_naturality
    {M N : CyclotomicSupermodules D Sc a ha n} (f : M ⟶ N) :
    (F).map f ≫ (inductionFunctorComparisonApp D Sc i j a ha n N).hom =
      (inductionFunctorComparisonApp D Sc i j a ha n M).hom ≫
        (compositionCornerFunctor D Sc i j a ha n).map f := by
  have hassoc : whiskerLeft P (whiskerLeft Q f) ≫ (assoc P Q N).inv =
      (assoc P Q M).inv ≫ whiskerLeft (tensor P Q) f := by
    apply (cancel_mono (assoc P Q N).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [assoc_naturality_right P Q M f, Iso.inv_hom_id_assoc]
  have hcorner : whiskerLeft (tensor P Q) f ≫
      whiskerRight (inductionCompositionIso D Sc i j a ha n).hom N =
      whiskerRight (inductionCompositionIso D Sc i j a ha n).hom M ≫ whiskerLeft T f := by
    refine Supercategory.induction_on (R := k) f ?_ (fun q g hg => ?_)
      (fun g h hg hh => ?_)
    · rw [whiskerLeft_zero, whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
    · have h := super_interchange (tensor P Q) g
        (inductionCompositionIso_hom_mem D Sc i j a ha n) hg
      rw [Supercategory.koszulSign_zero_left, one_smul] at h
      exact h.symm
    · rw [whiskerLeft_add, whiskerLeft_add, Preadditive.add_comp,
        Preadditive.comp_add, hg, hh]
  change whiskerLeft P (whiskerLeft Q f) ≫ ((assoc P Q N).inv ≫
    whiskerRight (inductionCompositionIso D Sc i j a ha n).hom N) =
    ((assoc P Q M).inv ≫ whiskerRight (inductionCompositionIso D Sc i j a ha n).hom M) ≫
      whiskerLeft T f
  rw [← Category.assoc, hassoc, Category.assoc, hcorner, Category.assoc]

/-- Successive cyclotomic induction is naturally isomorphic to two-colour corner induction. -/
def inductionFunctorComparison : F ≅ compositionCornerFunctor D Sc i j a ha n :=
  NatIso.ofComponents (inductionFunctorComparisonApp D Sc i j a ha n)
    (fun f => inductionFunctorComparisonApp_naturality D Sc i j a ha n f)

/-- On pure tensors the comparison multiplies the two corner factors in order. -/
@[simp] theorem inductionFunctorComparison_hom_btmul
    (M : CyclotomicSupermodules D Sc a ha n) (x : (P).toSVec) (y : (Q).toSVec)
    (m : M.toSVec) :
    ((inductionFunctorComparison D Sc i j a ha n).hom.app M).1
      (btmul P (tensor Q M) x (btmul Q M y m)) =
      btmul T M (compositionCornerBi D Sc i j a ha n x y) m := by
  change (whiskerRight (inductionCompositionIso D Sc i j a ha n).hom M).1
    ((assoc P Q M).inv.1 (btmul P (tensor Q M) x (btmul Q M y m))) = _
  rw [assoc_inv_btmul, whiskerRight_btmul]
  rfl

end OddMath.QuiverHecke
end

end

section

/-! # Restriction on ELV supermodules

The all-supermodule target is the superfunctor category from the truncated
ELV category to `SVec k`. Restriction along right append and evaluation of
its homogeneous transformations are constructed, including naturality
against odd module maps. This supplies the restriction side of
`DeformedActionAssembly.md` §5. Induction, its adjunction, integer grading,
and the normalized factor action remain separate constructions.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Parity-graded modules on the coefficient-truncated ELV category. -/
abbrev TruncatedModules :=
  Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec.{u} k)

/-- Restriction along right append, on all supernatural module maps. -/
def moduleRestriction (σ : List I) :
    TruncatedModules D Sc cutoff N ⥤ TruncatedModules D Sc cutoff N where
  obj M := (⟨truncatedAppend D Sc cutoff N σ⟩ :
    Superfunctor k (TruncatedCategory D Sc cutoff N) (TruncatedCategory D Sc cutoff N)).comp M
  map f := Superfunctor.whiskerLeft ⟨truncatedAppend D Sc cutoff N σ⟩ f
  map_id M := Superfunctor.whiskerLeft_id _ M
  map_comp f g := Superfunctor.whiskerLeft_comp _ f g

instance moduleRestriction_additive (σ : List I) :
    (moduleRestriction D Sc cutoff N σ).Additive where
  map_add := Superfunctor.whiskerLeft_add _ _ _

instance moduleRestriction_linear (σ : List I) :
    (moduleRestriction D Sc cutoff N σ).Linear k where
  map_smul f c := Superfunctor.whiskerLeft_smul _ c f

instance moduleRestriction_super (σ : List I) :
    IsSuperfunctor k (moduleRestriction D Sc cutoff N σ) where
  map_mem := Superfunctor.whiskerLeft_mem _

/-- A homogeneous appended morphism acts on every module by evaluation. -/
def moduleRestrictionComponent {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) (M : TruncatedModules D Sc cutoff N) :
    (moduleRestriction D Sc cutoff N σ).obj M ⟶
      (moduleRestriction D Sc cutoff N τ).obj M :=
  Superfunctor.whiskerRight
    (Superfunctor.homMk (truncatedAppendTransform D Sc cutoff N hh)) M

theorem moduleRestrictionComponent_mem {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) (M : TruncatedModules D Sc cutoff N) :
    moduleRestrictionComponent D Sc cutoff N hh M ∈ parity (R := k) _ _ p := by
  exact Superfunctor.whiskerRight_mem
    (F := ⟨truncatedAppend D Sc cutoff N σ⟩)
    (H := ⟨truncatedAppend D Sc cutoff N τ⟩)
    (Superfunctor.IsSupernatural.toSuperNatTrans_mem
      (F := ⟨truncatedAppend D Sc cutoff N σ⟩)
      (G := ⟨truncatedAppend D Sc cutoff N τ⟩)
      (truncatedAppendComponent_supernatural D Sc cutoff N hh)) M

theorem moduleRestrictionComponent_supernatural {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) :
    IsSupernatural k p (moduleRestrictionComponent D Sc cutoff N hh) where
  mem := moduleRestrictionComponent_mem D Sc cutoff N hh
  naturality := by
    intro M L q f hf
    have ht := Superfunctor.IsSupernatural.toSuperNatTrans_mem
      (F := ⟨truncatedAppend D Sc cutoff N σ⟩)
      (G := ⟨truncatedAppend D Sc cutoff N τ⟩)
      (truncatedAppendComponent_supernatural D Sc cutoff N hh)
    have he := Superfunctor.whisker_exchange ht hf
    have he' := congrArg (fun z => koszulSign p q • z) he
    rw [koszulSign_smul_smul] at he'
    simpa only [koszulSign_smul (R := k), moduleRestriction,
      moduleRestrictionComponent, truncatedAppendTransform] using he'.symm

/-- The transformation on restriction, including its exterior-coefficient signs. -/
def moduleRestrictionTransform {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) :
    SuperNatTrans k (moduleRestriction D Sc cutoff N σ)
      (moduleRestriction D Sc cutoff N τ) :=
  (moduleRestrictionComponent_supernatural D Sc cutoff N hh).toSuperNatTrans

/-- Evaluation of the homogeneous restriction transformation is the specified
quotient morphism, not a chosen module endomorphism. -/
@[simp] theorem moduleRestrictionTransform_app {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) (M : TruncatedModules D Sc cutoff N)
    (v : TruncatedCategory D Sc cutoff N) :
    ((moduleRestrictionTransform D Sc cutoff N hh).app p M).app p v =
      M.map (truncatedAppendComponent D Sc cutoff N h v) := by
  simp only [moduleRestrictionTransform, IsSupernatural.toSuperNatTrans,
    ↓reduceIte, moduleRestrictionComponent, Superfunctor.whiskerRight_app,
    Superfunctor.homMk, truncatedAppendTransform]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Underlying balanced induction tensors

The many-object balanced tensor quotient needed for the induction side of
`DeformedActionAssembly.md` §5. This file constructs underlying ground-ring modules,
not a graded induction superfunctor or an adjunction of supercategories.
-/
noncomputable section
open CategoryTheory StringDiagrams TensorProduct
open scoped DirectSum
attribute [local instance] Classical.propDecidable Classical.decEq
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D]
variable (J : C ⥤ D) (M : C ⥤ SVec k)

/-- The unbalanced direct sum over all source objects. -/
abbrev Raw (w : D) := ⨁ v : C, (J.obj v ⟶ w) ⊗[k] (M.obj v)

/-- A pure tensor in its specified summand. -/
def rawTensor {w : D} (v : C) (h : J.obj v ⟶ w) (m : M.obj v) : Raw J M w :=
  DirectSum.lof k C (fun v => (J.obj v ⟶ w) ⊗[k] (M.obj v)) v (h ⊗ₜ[k] m)

/-- Balancing by every source morphism; no parity restriction is imposed. -/
def relations (w : D) : Submodule k (Raw J M w) :=
  Submodule.span k {x | ∃ (v v' : C) (f : v ⟶ v') (h : J.obj v' ⟶ w)
    (m : M.obj v), x = rawTensor J M v (J.map f ≫ h) m -
      rawTensor J M v' h (M.map f m)}

/-- The concrete many-object balanced tensor quotient. -/
abbrev Obj (w : D) := Raw J M w ⧸ relations J M w

/-- The canonical map from a tensor summand to the quotient. -/
def inclusion (w : D) (v : C) :
    (J.obj v ⟶ w) ⊗[k] (M.obj v) →ₗ[k] Obj J M w :=
  (relations J M w).mkQ ∘ₗ DirectSum.lof k C (fun v => (J.obj v ⟶ w) ⊗[k] (M.obj v)) v

def tensor {w : D} (v : C) (h : J.obj v ⟶ w) (m : M.obj v) : Obj J M w :=
  inclusion J M w v (h ⊗ₜ[k] m)

theorem balance {w : D} {v v' : C} (f : v ⟶ v')
    (h : J.obj v' ⟶ w) (m : M.obj v) :
    tensor J M v (J.map f ≫ h) m = tensor J M v' h (M.map f m) := by
  apply sub_eq_zero.mp
  change (relations J M w).mkQ (rawTensor J M v (J.map f ≫ h) m) -
    (relations J M w).mkQ (rawTensor J M v' h (M.map f m)) = 0
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero (relations J M w)).mpr
  exact Submodule.subset_span ⟨v, v', f, h, m, rfl⟩

variable {V : Type u} [AddCommGroup V] [Module k V]

/-- Descend a family of linear maps out of the tensor summands. -/
def lift (w : D) (q : ∀ v : C, (J.obj v ⟶ w) ⊗[k] (M.obj v) →ₗ[k] V)
    (hq : ∀ (v v' : C) (f : v ⟶ v') (h : J.obj v' ⟶ w) (m : M.obj v),
      q v ((J.map f ≫ h) ⊗ₜ[k] m) = q v' (h ⊗ₜ[k] M.map f m)) :
    Obj J M w →ₗ[k] V :=
  (relations J M w).liftQ (DirectSum.toModule k C V q) (by
    apply Submodule.span_le.mpr
    rintro x ⟨v, v', f, h, m, rfl⟩
    change (DirectSum.toModule k C V q) _ = 0
    simp only [map_sub, rawTensor, DirectSum.toModule_lof]
    exact sub_eq_zero.mpr (hq v v' f h m))

@[simp] theorem lift_tensor (w : D)
    (q : ∀ v : C, (J.obj v ⟶ w) ⊗[k] (M.obj v) →ₗ[k] V) (hq)
    (v : C) (h : J.obj v ⟶ w) (m : M.obj v) :
    lift J M w q hq (tensor J M v h m) = q v (h ⊗ₜ[k] m) := by
  simp [lift, tensor, inclusion]

/-- Maps out of the quotient are determined by pure tensors. -/
@[ext] theorem hom_ext {w : D} {a b : Obj J M w →ₗ[k] V}
    (h : ∀ v (f : J.obj v ⟶ w) (m : M.obj v),
      a (tensor J M v f m) = b (tensor J M v f m)) : a = b := by
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro v
  apply TensorProduct.ext
  ext f m
  exact h v f m

/-- Covariance in the target object, on underlying modules. -/
def postcompose {w z : D} (a : w ⟶ z) : Obj J M w →ₗ[k] Obj J M z :=
  lift J M w (fun v => inclusion J M z v ∘ₗ TensorProduct.map
    ({ toFun := fun h => h ≫ a
       map_add' := fun _ _ => Preadditive.add_comp _ _ _ _ _ _
       map_smul' := fun _ _ => Linear.smul_comp _ _ _ _ _ _ } :
      (J.obj v ⟶ w) →ₗ[k] (J.obj v ⟶ z)) LinearMap.id) (by
    intro v v' f h m
    simpa only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.id_apply, Category.assoc, tensor] using
      balance J M f (h ≫ a) m)

@[simp] theorem postcompose_tensor {w z : D} (a : w ⟶ z)
    (v : C) (h : J.obj v ⟶ w) (m : M.obj v) :
    postcompose J M a (tensor J M v h m) = tensor J M v (h ≫ a) m := by
  rw [postcompose, lift_tensor]
  rfl

@[simp] theorem postcompose_id (w : D) :
    postcompose J M (𝟙 w) = LinearMap.id := by
  apply hom_ext
  intro v h m
  simp

theorem postcompose_comp {w z t : D} (a : w ⟶ z) (b : z ⟶ t) :
    postcompose J M (a ≫ b) = postcompose J M b ∘ₗ postcompose J M a := by
  apply hom_ext
  intro v h m
  simp [Category.assoc]

/-- The unit formula before packaging an induced functor. -/
def unit (v : C) : M.obj v →ₗ[k] Obj J M (J.obj v) :=
  inclusion J M (J.obj v) v ∘ₗ TensorProduct.mk k _ _ (𝟙 (J.obj v))

@[simp] theorem unit_apply (v : C) (m : M.obj v) :
    unit J M v m = tensor J M v (𝟙 _) m := rfl

/-- Reconstruction from the unit by target postcomposition. This is the
pure-tensor formula used in the induction-side triangle. -/
theorem postcompose_unit {v : C} {w : D} (h : J.obj v ⟶ w) (m : M.obj v) :
    postcompose J M h (unit J M v m) = tensor J M v h m := by
  rw [unit_apply, postcompose_tensor, Category.id_comp]

/-- Naturality of the unit for all source morphisms. -/
theorem unit_naturality {v v' : C} (f : v ⟶ v') :
    postcompose J M (J.map f) ∘ₗ unit J M v = unit J M v' ∘ₗ M.map f := by
  ext m
  change postcompose J M (J.map f) (unit J M v m) = unit J M v' (M.map f m)
  rw [postcompose_unit, unit_apply]
  simpa only [Category.comp_id] using balance J M f (𝟙 (J.obj v')) m

variable (N : D ⥤ SVec k) [N.Additive] [N.Linear k]

/-- Evaluation on each tensor summand. -/
def evaluationTensor (w : D) (v : C) :
    (J.obj v ⟶ w) ⊗[k] N.obj (J.obj v) →ₗ[k] N.obj w :=
  TensorProduct.lift (N.mapLinearMap (R := k))

/-- The underlying evaluation counit on the balanced quotient of a restriction. -/
def counit (w : D) : Obj J (J ⋙ N) w →ₗ[k] N.obj w :=
  lift J (J ⋙ N) w (evaluationTensor J N w) (by
    intro v v' f h m
    change N.map (J.map f ≫ h) m = N.map h (N.map (J.map f) m)
    rw [N.map_comp]
    rfl)

@[simp] theorem counit_tensor (w : D) (v : C) (h : J.obj v ⟶ w)
    (m : N.obj (J.obj v)) :
    counit J N w (tensor J (J ⋙ N) v h m) = N.map h m := by
  rw [counit, lift_tensor]
  rfl

/-- Naturality of the evaluation counit for all target morphisms. -/
theorem counit_naturality {w z : D} (a : w ⟶ z) :
    counit J N z ∘ₗ postcompose J (J ⋙ N) a = N.map a ∘ₗ counit J N w := by
  apply hom_ext
  intro v h m
  change counit J N z (postcompose J (J ⋙ N) a (tensor J (J ⋙ N) v h m)) =
    N.map a (counit J N w (tensor J (J ⋙ N) v h m))
  rw [postcompose_tensor, counit_tensor, counit_tensor, N.map_comp]
  rfl

/-- The restriction-side triangle, as an equality of underlying linear maps. -/
theorem counit_unit (v : C) :
    counit J N (J.obj v) ∘ₗ unit J (J ⋙ N) v = LinearMap.id := by
  ext m
  change counit J N (J.obj v) (tensor J (J ⋙ N) v (𝟙 _) m) = m
  rw [counit_tensor, N.map_id]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

end OddMath.QuiverHecke.ELVOld
end

end

section

noncomputable section
open CategoryTheory StringDiagrams TensorProduct Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D]
variable (J : C ⥤ D) (M : C ⥤ SVec k)

@[simp] theorem tensor_add_left {w : D} (v : C) (h h' : J.obj v ⟶ w) (m : M.obj v) :
    tensor J M v (h + h') m = tensor J M v h m + tensor J M v h' m := by
  simp [tensor, add_tmul]
@[simp] theorem tensor_add_right {w : D} (v : C) (h : J.obj v ⟶ w) (m m' : M.obj v) :
    tensor J M v h (m + m') = tensor J M v h m + tensor J M v h m' := by
  simp [tensor, tmul_add]
@[simp] theorem tensor_zero_left {w : D} (v : C) (m : M.obj v) :
    tensor J M v (0 : J.obj v ⟶ w) m = 0 := by simp [tensor]
@[simp] theorem tensor_zero_right {w : D} (v : C) (h : J.obj v ⟶ w) :
    tensor J M v h 0 = 0 := by simp [tensor]

variable [Supercategory k D]

def oddSummand (w : D) (v : C) :
    (J.obj v ⟶ w) ⊗[k] M.obj v →ₗ[k] Obj J M w :=
  inclusion J M w v ∘ₗ
    (TensorProduct.map (proj k 1) ((M.obj v).proj 0) +
      TensorProduct.map (proj k 0) ((M.obj v).proj 1))

@[simp] theorem oddSummand_tmul (w : D) (v : C) (h : J.obj v ⟶ w) (m : M.obj v) :
    oddSummand J M w v (h ⊗ₜ[k] m) =
      tensor J M v (proj k 1 h) ((M.obj v).proj 0 m) +
      tensor J M v (proj k 0 h) ((M.obj v).proj 1 m) := by
  simp [oddSummand, tensor]

variable [Preadditive C] [Linear k C] [Supercategory k C]
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [M.Additive] [M.Linear k] [IsSuperfunctor k M]

theorem oddSummand_balance (w : D) (v v' : C) (f : v ⟶ v')
    (h : J.obj v' ⟶ w) (m : M.obj v) :
    oddSummand J M w v ((J.map f ≫ h) ⊗ₜ[k] m) =
      oddSummand J M w v' (h ⊗ₜ[k] M.map f m) := by
  refine Supercategory.induction_on (R := k) f ?_ (fun p f hf => ?_) ?_
  · simp
  ·
    have hj := map_mem J hf
    have hm := map_mem M hf
    have h0 := proj_comp_of_mem_left (R := k) 0 hj h
    have h1 := proj_comp_of_mem_left (R := k) 1 hj h
    have m0 := SVec.apply_proj_of_mem hm 0 m
    have m1 := SVec.apply_proj_of_mem hm 1 m
    rcases parity_eq_zero_or_one p with rfl | rfl
    · simp only [zero_add, add_zero] at h0 h1 m0 m1
      simp only [oddSummand_tmul, h0, h1, ← m0, ← m1, balance]
    · simp only [add_zero, SVec.zmod2_one_add_one, zero_add] at h0 h1 m0 m1
      simp only [oddSummand_tmul, h0, h1, ← m0, ← m1, balance]
      exact add_comm _ _
  · intro f g hf hg
    simpa only [Functor.map_add, Preadditive.add_comp, add_tmul, tmul_add,
      SVec.add_apply, map_add] using congrArg₂ (· + ·) hf hg

def odd (w : D) : Obj J M w →ₗ[k] Obj J M w :=
  lift J M w (oddSummand J M w) (oddSummand_balance J M w)

@[simp] theorem odd_tensor (w : D) (v : C) (h : J.obj v ⟶ w) (m : M.obj v) :
    odd J M w (tensor J M v h m) =
      tensor J M v (proj k 1 h) ((M.obj v).proj 0 m) +
      tensor J M v (proj k 0 h) ((M.obj v).proj 1 m) := by
  simp [odd]

theorem odd_comp_odd (w : D) : odd J M w ∘ₗ odd J M w = odd J M w := by
  apply hom_ext
  intro v h m
  simp [proj_proj, proj_proj_of_ne (R := k) (show (0 : ZMod 2) ≠ 1 by decide),
    proj_proj_of_ne (R := k) (show (1 : ZMod 2) ≠ 0 by decide), SVec.proj_proj_apply]

/-- The sum parity grading on the many-object balanced induction quotient. -/
abbrev superspace (w : D) : SVec k where
  carrier := Obj J M w
  odd := odd J M w
  odd_comp_odd := odd_comp_odd J M w
theorem proj_tensor (w : D) (q : ZMod 2) (v : C)
    (h : J.obj v ⟶ w) (m : M.obj v) :
    (superspace J M w).proj q (tensor J M v h m) =
      tensor J M v (proj k q h) ((M.obj v).proj 0 m) +
      tensor J M v (proj k (q + 1) h) ((M.obj v).proj 1 m) := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · change tensor J M v h m - odd J M w (tensor J M v h m) = _
    rw [odd_tensor]
    have e : tensor J M v h m =
        tensor J M v (proj k 0 h + proj k 1 h)
          ((M.obj v).proj 0 m + (M.obj v).proj 1 m) := by
      rw [Supercategory.proj_add_proj, SVec.proj_apply_add]
    rw [e]
    simp only [tensor_add_left, tensor_add_right, zero_add]
    abel
  · simpa only [SVec.proj_one, SVec.zmod2_one_add_one] using odd_tensor J M w v h m

/-- Postcomposition by a homogeneous arrow has its original parity. -/
theorem postcompose_mem {w z : D} {p : ZMod 2} (a : w ⟶ z)
    (ha : a ∈ parity (R := k) w z p) :
    (postcompose J M a : superspace J M w ⟶ superspace J M z) ∈
      parity (R := k) (superspace J M w) (superspace J M z) p := by
  change ∀ q, postcompose J M a ∘ₗ (superspace J M w).proj q =
    (superspace J M z).proj (q + p) ∘ₗ postcompose J M a
  intro q
  apply hom_ext
  intro v h m
  simp only [LinearMap.comp_apply, proj_tensor J M, map_add, postcompose_tensor]
  rw [proj_comp_of_mem_right (R := k) q h ha]
  rw [show q + p + 1 = (q + 1) + p by abel,
    proj_comp_of_mem_right (R := k) (q + 1) h ha]

/-- Induction as a functor into superspaces, with the quotient grading. -/
def moduleFunctor : D ⥤ SVec k where
  obj := superspace J M
  map := postcompose J M
  map_id := postcompose_id J M
  map_comp := postcompose_comp J M

instance moduleFunctor_additive : (moduleFunctor J M).Additive where
  map_add := by
    intro w z a b
    change postcompose J M (a + b) = postcompose J M a + postcompose J M b
    apply hom_ext
    intro v h m
    simp [Preadditive.comp_add]

instance moduleFunctor_linear : (moduleFunctor J M).Linear k where
  map_smul := by
    intro w z a r
    change postcompose J M (r • a) = r • postcompose J M a
    apply hom_ext
    intro v h m
    rw [LinearMap.smul_apply, postcompose_tensor, Linear.comp_smul]
    change inclusion J M z v ((r • (h ≫ a)) ⊗ₜ[k] m) = _
    rw [← smul_tmul', map_smul, postcompose_tensor]
    rfl

instance moduleFunctor_super : IsSuperfunctor k (moduleFunctor J M) where
  map_mem := postcompose_mem J M _

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Signed maps on balanced induction

The signed tensor formula for induction on supernatural module maps.
-/
noncomputable section
open CategoryTheory StringDiagrams TensorProduct Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)

def mapSummand (p : ZMod 2) (w : D) (v : C) :
    (J.obj v ⟶ w) ⊗[k] M.obj v →ₗ[k] Obj J N.toFunctor w :=
  inclusion J N.toFunctor w v ∘ₗ TensorProduct.map (twist k p) (f.app p v)

omit [J.Additive] [J.Linear k] [IsSuperfunctor k J] in
@[simp] theorem mapSummand_tmul (p : ZMod 2) (w : D) (v : C)
    (h : J.obj v ⟶ w) (m : M.obj v) :
    mapSummand J f p w v (h ⊗ₜ[k] m) =
      tensor J N.toFunctor v (twist k p h) (f.app p v m) := rfl

theorem mapSummand_balance (p : ZMod 2) (w : D) (v v' : C)
    (a : v ⟶ v') (h : J.obj v' ⟶ w) (m : M.obj v) :
    mapSummand J f p w v ((J.map a ≫ h) ⊗ₜ[k] m) =
      mapSummand J f p w v' (h ⊗ₜ[k] M.map a m) := by
  rw [mapSummand_tmul, mapSummand_tmul, twist_comp, ← map_twist J, balance]
  have e := congrArg (fun t : M.obj v ⟶ N.obj v' => t m)
    ((f.isSupernatural p).naturality_twist a)
  exact congrArg (tensor J N.toFunctor v' (twist k p h)) e.symm

/-- The parity component of the signed action on the quotient. -/
def mapComponent (p : ZMod 2) (w : D) :
    Obj J M.toFunctor w →ₗ[k] Obj J N.toFunctor w :=
  lift J M.toFunctor w (mapSummand J f p w) (mapSummand_balance J f p w)

@[simp] theorem mapComponent_tensor (p : ZMod 2) (w : D) (v : C)
    (h : J.obj v ⟶ w) (m : M.obj v) :
    mapComponent J f p w (tensor J M.toFunctor v h m) =
      tensor J N.toFunctor v (twist k p h) (f.app p v m) := by
  rw [mapComponent, lift_tensor, mapSummand_tmul]

theorem mapComponent_mem (p : ZMod 2) (w : D) :
    (mapComponent J f p w : superspace J M.toFunctor w ⟶ superspace J N.toFunctor w) ∈
      parity (R := k) (superspace J M.toFunctor w) (superspace J N.toFunctor w) p := by
  change ∀ q, mapComponent J f p w ∘ₗ (superspace J M.toFunctor w).proj q =
    (superspace J N.toFunctor w).proj (q + p) ∘ₗ mapComponent J f p w
  intro q
  apply hom_ext
  intro v h m
  have m0 := SVec.apply_proj_of_mem (f.app_mem p v) 0 m
  have m1 := SVec.apply_proj_of_mem (f.app_mem p v) 1 m
  simp only [LinearMap.comp_apply, proj_tensor J M.toFunctor, proj_tensor J N.toFunctor,
    map_add, mapComponent_tensor]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp only [twist_zero, add_zero] at *
    rw [← m0, ← m1]
  · simp only [zero_add, SVec.zmod2_one_add_one] at m0 m1
    rw [← m1, ← m0]
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
      simp [twist_apply, proj_proj, proj_proj_of_ne (R := k)
        (show (0 : ZMod 2) ≠ 1 by decide), proj_proj_of_ne (R := k)
        (show (1 : ZMod 2) ≠ 0 by decide), tensor] <;> abel

theorem mapComponent_naturality (p : ZMod 2) {w z : D} (a : w ⟶ z) :
    mapComponent J f p z ∘ₗ postcompose J M.toFunctor a =
      postcompose J N.toFunctor (twist k p a) ∘ₗ mapComponent J f p w := by
  apply hom_ext
  intro v h m
  simp only [LinearMap.comp_apply, postcompose_tensor, mapComponent_tensor, twist_comp]

/-- Induction of all homogeneous components of a supernatural transformation. -/
def moduleMap : SuperNatTrans k (moduleFunctor J M.toFunctor)
    (moduleFunctor J N.toFunctor) where
  app := mapComponent J f
  app_mem := mapComponent_mem J f
  naturality p w z q a ha := by
    change mapComponent J f p z ∘ₗ postcompose J M.toFunctor a = _
    rw [mapComponent_naturality, twist_of_mem p ha]
    apply hom_ext
    intro v h m
    change postcompose J N.toFunctor (sign k (p * q) • a)
      (mapComponent J f p w (tensor J M.toFunctor v h m)) =
      koszulSign p q • postcompose J N.toFunctor a
        (mapComponent J f p w (tensor J M.toFunctor v h m))
    rw [mapComponent_tensor, postcompose_tensor, postcompose_tensor, Linear.comp_smul]
    simp only [tensor, ← smul_tmul', map_smul, koszulSign_smul (R := k)]

/-- The induced supermodule. -/
def induced (M : Superfunctor k C (SVec k)) : Superfunctor k D (SVec k) :=
  ⟨moduleFunctor J M.toFunctor⟩

@[simp] theorem moduleMap_id (M : Superfunctor k C (SVec k)) :
    moduleMap J (𝟙 M) = (𝟙 (induced J M) : induced J M ⟶ induced J M) := by
  apply SuperNatTrans.ext
  funext p w
  apply hom_ext
  intro v h m
  change mapComponent J (𝟙 M) p w (tensor J M.toFunctor v h m) = _
  rw [mapComponent_tensor]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · change tensor J M.toFunctor v (twist k 0 h) m = tensor J M.toFunctor v h m
    rw [twist_zero]
  · change tensor J M.toFunctor v (twist k 1 h) 0 = 0
    exact tensor_zero_right J M.toFunctor v _

@[simp] theorem moduleMap_comp {L : Superfunctor k C (SVec k)} (g : N ⟶ L) :
    moduleMap J (f ≫ g) = (moduleMap J f).vcomp (moduleMap J g) := by
  apply SuperNatTrans.ext
  funext p w
  apply hom_ext
  intro v h m
  change mapComponent J (f ≫ g) p w (tensor J M.toFunctor v h m) =
    mapComponent J g p w (mapComponent J f 0 w (tensor J M.toFunctor v h m)) +
      mapComponent J g (p + 1) w (mapComponent J f 1 w (tensor J M.toFunctor v h m))
  simp only [mapComponent_tensor, Superfunctor.comp_app, SVec.add_apply, SVec.comp_apply,
    tensor_add_right, twist_zero]
  rw [← twist_add]
  congr 2
  congr 1
  have e : p + 1 + 1 = p := by rw [add_assoc, SVec.zmod2_one_add_one, add_zero]
  rw [e]

/-- Balanced induction on the category of all supernatural module maps. -/
def induction : Superfunctor k C (SVec k) ⥤ Superfunctor k D (SVec k) where
  obj := induced J
  map := moduleMap J
  map_id := moduleMap_id J
  map_comp f g := moduleMap_comp J f g

instance induction_additive : (induction (k := k) J).Additive where
  map_add := by
    intro M N f g
    apply Superfunctor.hom_ext
    intro p w
    apply hom_ext
    intro v h m
    change mapComponent J (f + g) p w (tensor J M.toFunctor v h m) =
      mapComponent J f p w (tensor J M.toFunctor v h m) +
        mapComponent J g p w (tensor J M.toFunctor v h m)
    simp only [mapComponent_tensor, Superfunctor.add_app, SVec.add_apply, tensor_add_right]

instance induction_linear : (induction (k := k) J).Linear k where
  map_smul := by
    intro M N f r
    apply Superfunctor.hom_ext
    intro p w
    apply hom_ext
    intro v h m
    change mapComponent J (r • f) p w (tensor J M.toFunctor v h m) =
      r • mapComponent J f p w (tensor J M.toFunctor v h m)
    rw [mapComponent_tensor, mapComponent_tensor, Superfunctor.smul_app]
    change tensor J N.toFunctor v (twist k p h) (r • f.app p v m) = _
    simp only [tensor, tmul_smul, map_smul]

instance induction_super : IsSuperfunctor k (induction (k := k) J) where
  map_mem := by
    intro M N p f hf
    apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
    intro q hq
    funext w
    apply hom_ext
    intro v h m
    change mapComponent J f q w (tensor J M.toFunctor v h m) = 0
    rw [mapComponent_tensor, Superfunctor.app_eq_zero_of_mem hf hq]
    exact tensor_zero_right J N.toFunctor v _

/-- The total action includes both parity components, including odd module maps. -/
theorem moduleMap_total_tensor (w : D) (v : C) (h : J.obj v ⟶ w) (m : M.obj v) :
    (moduleMap J f).total w (tensor J M.toFunctor v h m) =
      tensor J N.toFunctor v h (f.app 0 v m) +
        tensor J N.toFunctor v (twist k 1 h) (f.app 1 v m) := by
  change mapComponent J f 0 w (tensor J M.toFunctor v h m) +
    mapComponent J f 1 w (tensor J M.toFunctor v h m) = _
  rw [mapComponent_tensor, mapComponent_tensor, twist_zero]

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Induction–restriction adjunction for ELV supermodules

`moduleAdjunction` specializes the concrete balanced-tensor construction to
right append on the full-coefficient truncated ELV category. Both functors
act on all supernatural module maps. The unit and counit are even and both
triangles are proved on quotient tensor generators. This is the adjunction
bridge for `DeformedActionAssembly.md` §5, not the completed factor action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]

def restriction : Superfunctor k D (SVec k) ⥤ Superfunctor k C (SVec k) where
  obj M := (⟨J⟩ : Superfunctor k C D).comp M
  map f := Superfunctor.whiskerLeft ⟨J⟩ f
  map_id M := Superfunctor.whiskerLeft_id _ M
  map_comp f g := Superfunctor.whiskerLeft_comp _ f g
instance restriction_additive : (restriction (k := k) J).Additive where
  map_add := Superfunctor.whiskerLeft_add _ _ _
instance restriction_linear : (restriction (k := k) J).Linear k where
  map_smul f c := Superfunctor.whiskerLeft_smul _ c f
instance restriction_super : IsSuperfunctor k (restriction (k := k) J) where
  map_mem := Superfunctor.whiskerLeft_mem _

variable (M : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
theorem unit_mem (v : C) :
    (unit J M.toFunctor v : M.obj v ⟶ superspace J M.toFunctor (J.obj v)) ∈
      parity (R := k) (M.obj v) (superspace J M.toFunctor (J.obj v)) 0 := by
  change ∀ q, unit J M.toFunctor v ∘ₗ (M.obj v).proj q =
    (superspace J M.toFunctor (J.obj v)).proj (q + 0) ∘ₗ unit J M.toFunctor v
  intro q
  ext m
  rw [LinearMap.comp_apply, LinearMap.comp_apply, unit_apply, unit_apply, proj_tensor]
  rcases parity_eq_zero_or_one q with rfl | rfl <;>
    simp [proj_id, proj_of_mem, id_mem, SVec.zmod2_one_add_one]

def unitTransform : SuperNatTrans k M.toFunctor
    ((restriction J).obj (induced J M)).toFunctor :=
  IsSupernatural.toSuperNatTrans (p := 0) (F := M.toFunctor) (G := ((restriction J).obj (induced J M)).toFunctor)
    (x := unit J M.toFunctor) {
    mem := unit_mem J M
    naturality := by
      intro v v' q f hf
      simp only [zero_mul, Supercategory.sign_zero, one_smul]
      change unit J M.toFunctor v' ∘ₗ M.map f =
        postcompose J M.toFunctor (J.map f) ∘ₗ unit J M.toFunctor v
      exact (unit_naturality J M.toFunctor f).symm }

theorem counit_mem (w : D) :
    (counit J N.toFunctor w : superspace J (J ⋙ N.toFunctor) w ⟶ N.obj w) ∈
      parity (R := k) (superspace J (J ⋙ N.toFunctor) w) (N.obj w) 0 := by
  change ∀ q, counit J N.toFunctor w ∘ₗ (superspace J (J ⋙ N.toFunctor) w).proj q =
    (N.obj w).proj (q + 0) ∘ₗ counit J N.toFunctor w
  intro q
  apply hom_ext
  intro v h m
  simp only [LinearMap.comp_apply, proj_tensor J (J ⋙ N.toFunctor), map_add,
    counit_tensor, add_zero]
  have h0 := SVec.apply_proj_of_mem (map_mem N.toFunctor (proj_mem (R := k) q h)) 0 m
  have h1 := SVec.apply_proj_of_mem (map_mem N.toFunctor (proj_mem (R := k) (q + 1) h)) 1 m
  simp only [zero_add, show (1 : ZMod 2) + (q + 1) = q by
    rw [add_left_comm, SVec.zmod2_one_add_one, add_zero]] at h0 h1
  change N.map (proj k q h) ((N.obj (J.obj v)).proj 0 m) +
    N.map (proj k (q + 1) h) ((N.obj (J.obj v)).proj 1 m) = _
  rw [h0, h1, ← map_add]
  rw [← SVec.add_apply, ← N.toFunctor.map_add]
  congr 2
  rcases parity_eq_zero_or_one q with rfl | rfl <;>
    simp [proj_add_proj, SVec.zmod2_one_add_one, add_comm]

def counitTransform : SuperNatTrans k
    (induced J ((restriction J).obj N)).toFunctor N.toFunctor :=
  IsSupernatural.toSuperNatTrans (p := 0) (F := (induced J ((restriction J).obj N)).toFunctor) (G := N.toFunctor)
    (x := counit J N.toFunctor) {
    mem := counit_mem J N
    naturality := by
      intro v v' q f hf
      simp only [zero_mul, Supercategory.sign_zero, one_smul]
      change counit J N.toFunctor v' ∘ₗ postcompose J (J ⋙ N.toFunctor) f =
        N.map f ∘ₗ counit J N.toFunctor v
      exact counit_naturality J N.toFunctor f }

@[simp] theorem unitTransform_app (p : ZMod 2) (v : C) :
    (unitTransform J M).app p v = if p = 0 then unit J M.toFunctor v else 0 := rfl
@[simp] theorem counitTransform_app (p : ZMod 2) (w : D) :
    (counitTransform J N).app p w = if p = 0 then counit J N.toFunctor w else 0 := rfl

/-- The even unit, natural against every supernatural module map. -/
def adjunctionUnit : 𝟭 (Superfunctor k C (SVec k)) ⟶ induction J ⋙ restriction J where
  app M := Superfunctor.homMk (unitTransform J M)
  naturality {M L} f := by
    apply Superfunctor.hom_ext
    intro p v
    ext m
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp [Superfunctor.comp_app, Superfunctor.whiskerLeft_app, induction, restriction,
        Superfunctor.homMk, unitTransform_app, moduleMap, SVec.comp_apply]
    all_goals
      change unit J L.toFunctor v (f.app _ v m) =
        mapComponent J f _ (J.obj v) (unit J M.toFunctor v m)
      rw [unit_apply, unit_apply, mapComponent_tensor, twist_id]

/-- The even counit, natural against every supernatural module map. -/
def adjunctionCounit : restriction J ⋙ induction J ⟶ 𝟭 (Superfunctor k D (SVec k)) where
  app N := Superfunctor.homMk (counitTransform J N)
  naturality {N L} f := by
    apply Superfunctor.hom_ext
    intro p w
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Functor.comp_map, Functor.id_map, Superfunctor.comp_app,
        Superfunctor.homMk, counitTransform_app, ↓reduceIte, zero_add,
        SVec.zmod2_one_add_one, one_ne_zero, CategoryTheory.Limits.comp_zero,
        CategoryTheory.Limits.zero_comp, add_zero, zero_add]
    all_goals
      apply hom_ext
      intro v h m
      dsimp only [restriction, Superfunctor.comp] at m ⊢
      change counit J L.toFunctor w
        (mapComponent J (Superfunctor.whiskerLeft (⟨J⟩ : Superfunctor k C D) f) _ w
          (tensor J (J ⋙ N.toFunctor) v h m)) =
        f.app _ w (counit J N.toFunctor w (tensor J (J ⋙ N.toFunctor) v h m))
      simp only [mapComponent, Superfunctor.comp, lift_tensor, counit_tensor]
      change counit J L.toFunctor w
        (tensor J (J ⋙ L.toFunctor) v (twist k _ h) (f.app _ (J.obj v) m)) = _
      rw [counit_tensor]
      exact congrArg (fun t : N.obj (J.obj v) ⟶ L.obj w => t m)
        ((f.isSupernatural _).naturality_twist h).symm

/-- Balanced induction is left adjoint to restriction on all supermodule maps. -/
def adjunction : induction (k := k) J ⊣ restriction J where
  unit := adjunctionUnit J
  counit := adjunctionCounit J
  left_triangle_components M := by
    apply Superfunctor.hom_ext
    intro p w
    rcases parity_eq_zero_or_one p with rfl | rfl
    · apply hom_ext
      intro v h m
      simp only [Superfunctor.comp_app, adjunctionUnit, adjunctionCounit,
        Superfunctor.homMk, counitTransform_app, ↓reduceIte, zero_add, one_ne_zero,
        CategoryTheory.Limits.comp_zero, add_zero]
      change counit J (induced J M).toFunctor w
        (mapComponent J (Superfunctor.homMk (unitTransform J M)) 0 w
          (tensor J M.toFunctor v h m)) = tensor J M.toFunctor v h m
      rw [mapComponent_tensor, twist_zero]
      change counit J (induced J M).toFunctor w
        (tensor J (J ⋙ (induced J M).toFunctor) v h (unit J M.toFunctor v m)) = _
      rw [counit_tensor]
      exact postcompose_unit J M.toFunctor h m
    · simp only [Superfunctor.comp_app, adjunctionUnit, adjunctionCounit,
        Superfunctor.homMk, counitTransform_app, ↓reduceIte,
        SVec.zmod2_one_add_one, one_ne_zero, CategoryTheory.Limits.comp_zero, zero_add]
      apply hom_ext
      intro v h m
      change counit J (induced J M).toFunctor w
        (mapComponent J (Superfunctor.homMk (unitTransform J M)) 1 w
          (tensor J M.toFunctor v h m)) = 0
      rw [mapComponent_tensor]
      change counit J (induced J M).toFunctor w
        (tensor J (J ⋙ (induced J M).toFunctor) v (twist k 1 h) 0) = 0
      rw [tensor_zero_right, map_zero]
  right_triangle_components N := by
    apply Superfunctor.hom_ext
    intro p v
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Superfunctor.comp_app, adjunctionUnit, adjunctionCounit,
        restriction, Superfunctor.whiskerLeft_app, Superfunctor.homMk,
        counitTransform_app, unitTransform_app, ↓reduceIte, zero_add,
        SVec.zmod2_one_add_one, one_ne_zero, CategoryTheory.Limits.comp_zero,
        CategoryTheory.Limits.zero_comp, add_zero, zero_add]
    change counit J N.toFunctor (J.obj v) ∘ₗ unit J (J ⋙ N.toFunctor) v = LinearMap.id
    exact counit_unit J N.toFunctor v
    rfl

theorem adjunctionUnit_mem (M : Superfunctor k C (SVec k)) :
    (adjunction J).unit.app M ∈ parity (R := k) M ((induction J ⋙ restriction J).obj M) 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext v
  simp only [adjunction, adjunctionUnit, Superfunctor.homMk, unitTransform_app,
    hq, ↓reduceIte, Pi.zero_apply]

theorem adjunctionCounit_mem (N : Superfunctor k D (SVec k)) :
    (adjunction J).counit.app N ∈ parity (R := k) ((restriction J ⋙ induction J).obj N) N 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext w
  simp only [adjunction, adjunctionCounit, Superfunctor.homMk, counitTransform_app,
    hq, ↓reduceIte, Pi.zero_apply]

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- The actual balanced induction functor for the full-coefficient ELV quotient. -/
abbrev moduleInduction (σ : List I) :
    TruncatedModules D Sc cutoff N ⥤ TruncatedModules D Sc cutoff N :=
  BalancedInduction.induction (truncatedAppend D Sc cutoff N σ)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Composition of balanced induction

The constructed induction–restriction adjunctions give a canonical comparison
`induction J ⋙ induction K ≅ induction (J ⋙ K)` on the category of all supernatural
module maps. Both directions are even. On balanced quotient generators the
comparison sends `[g ⊗ [h ⊗ m]]` to `[K.map h ≫ g ⊗ m]`; its inverse sends
`[a ⊗ m]` to `[a ⊗ [id ⊗ m]]`. No homogeneity restriction on `g`, `h`, or `m`
is required. The coefficient ring is an arbitrary commutative ring.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

def compAdjunction : induction (k := k) J ⋙ induction K ⊣ restriction (J ⋙ K) :=
  (adjunction J).comp (adjunction K)

def inductionComp : induction (k := k) J ⋙ induction K ≅ induction (J ⋙ K) :=
  (compAdjunction J K).leftAdjointUniq (adjunction (J ⋙ K))

private theorem uniq_hom {A B : Type*} [Category* A] [Category* B]
    {F F' : A ⥤ B} {G : B ⥤ A} (a : F ⊣ G) (b : F' ⊣ G) (x : A) :
    (a.leftAdjointUniq b).hom.app x = F.map (b.unit.app x) ≫ a.counit.app (F'.obj x) := by
  calc
    _ = (a.homEquiv _ _).symm (b.unit.app x) :=
      (Equiv.eq_symm_apply _).mpr (Adjunction.homEquiv_leftAdjointUniq_hom_app a b x)
    _ = _ := a.homEquiv_counit _ _ _

private theorem uniq_comp_hom {A B T : Type*} [Category* A] [Category* B] [Category* T]
    {F : A ⥤ B} {G : B ⥤ A} {H : B ⥤ T} {I : T ⥤ B} {L : A ⥤ T}
    (a : F ⊣ G) (b : H ⊣ I) (c : L ⊣ I ⋙ G) (x : A) :
    ((a.comp b).leftAdjointUniq c).hom.app x =
      H.map (F.map (c.unit.app x)) ≫ H.map (a.counit.app (I.obj (L.obj x))) ≫
        b.counit.app (L.obj x) := by
  rw [uniq_hom, Adjunction.comp_counit_app]
  rfl

theorem inductionComp_hom_eq (M : Superfunctor k C (SVec k)) :
    (inductionComp J K).hom.app M =
      (induction K).map ((induction J).map ((adjunction (J ⋙ K)).unit.app M)) ≫
      (induction K).map ((adjunction J).counit.app
        ((restriction K).obj ((induction (J ⋙ K)).obj M))) ≫
      (adjunction K).counit.app ((induction (J ⋙ K)).obj M) := by
  exact uniq_comp_hom (adjunction J) (adjunction K) (adjunction (J ⋙ K)) M

theorem inductionComp_inv_eq (M : Superfunctor k C (SVec k)) :
    (inductionComp J K).inv.app M =
      (induction (J ⋙ K)).map
        ((adjunction J).unit.app M ≫
          (restriction J).map ((adjunction K).unit.app ((induction J).obj M))) ≫
      (adjunction (J ⋙ K)).counit.app ((induction K).obj ((induction J).obj M)) := by
  rw [inductionComp, Adjunction.leftAdjointUniq_inv_app, uniq_hom]
  rw [show (compAdjunction J K).unit.app M = _ from
    Adjunction.comp_unit_app (adjunction J) (adjunction K) M]
  rfl

theorem inductionComp_hom_mem (M : Superfunctor k C (SVec k)) :
    (inductionComp J K).hom.app M ∈ parity (R := k) _ _ 0 := by
  rw [inductionComp_hom_eq]
  have hu := adjunctionUnit_mem (J ⋙ K) M
  have hju := map_mem (induction J) hu
  have hkju := map_mem (induction K) hju
  have hcj := adjunctionCounit_mem J ((restriction K).obj ((induction (J ⋙ K)).obj M))
  have hkcj := map_mem (induction K) hcj
  have hck := adjunctionCounit_mem K ((induction (J ⋙ K)).obj M)
  exact comp_mem hkju (comp_mem hkcj hck)

theorem inductionComp_inv_mem (M : Superfunctor k C (SVec k)) :
    (inductionComp J K).inv.app M ∈ parity (R := k) _ _ 0 := by
  rw [inductionComp_inv_eq]
  have huj := adjunctionUnit_mem J M
  have huk := adjunctionUnit_mem K ((induction J).obj M)
  have hru := map_mem (restriction J) huk
  have hu := comp_mem huj hru
  have hiu := map_mem (induction (J ⋙ K)) hu
  have hc := adjunctionCounit_mem (J ⋙ K) ((induction K).obj ((induction J).obj M))
  exact comp_mem hiu hc

private def transposeMap (M : Superfunctor k C (SVec k))
    (N : Superfunctor k D (SVec k)) (f : M ⟶ (restriction J).obj N) :
    (induction J).obj M ⟶ N :=
  (induction J).map f ≫ (adjunction J).counit.app N

private theorem transposeMap_tensor (M : Superfunctor k C (SVec k))
    (N : Superfunctor k D (SVec k)) (f : M ⟶ (restriction J).obj N)
    (v : C) (w : D) (h : J.obj v ⟶ w) (m : M.obj v) :
    (transposeMap J M N f).app 0 w (tensor J M.toFunctor v h m) =
      N.map h (f.app 0 v m) := by
  change counit J N.toFunctor w (mapComponent J f 0 w (tensor J M.toFunctor v h m)) + 0 = _
  rw [add_zero, mapComponent_tensor, twist_zero]
  exact counit_tensor J N.toFunctor w v h (f.app 0 v m)

private theorem transposeMap_comp_tensor (M : Superfunctor k C (SVec k))
    (N : Superfunctor k E (SVec k))
    (f : M ⟶ (restriction J).obj ((restriction K).obj N))
    (v : C) (w : D) (z : E) (g : K.obj w ⟶ z) (h : J.obj v ⟶ w) (m : M.obj v) :
    (transposeMap K (induced J M) N
      (transposeMap J M ((restriction K).obj N) f)).app 0 z
      (tensor K (induced J M).toFunctor w g (tensor J M.toFunctor v h m)) =
        N.map g (N.map (K.map h) (f.app 0 v m)) := by
  erw [transposeMap_tensor, transposeMap_tensor]
  rfl

@[simp] theorem inductionComp_hom_tensor (M : Superfunctor k C (SVec k))
    (v : C) (w : D) (z : E) (g : K.obj w ⟶ z) (h : J.obj v ⟶ w) (m : M.obj v) :
    ((inductionComp J K).hom.app M).app 0 z
      (tensor K (induced J M).toFunctor w g (tensor J M.toFunctor v h m)) =
      tensor (J ⋙ K) M.toFunctor v (K.map h ≫ g) m := by
  let N := (induction (J ⋙ K)).obj M
  let U := (restriction K).obj N
  let f : M ⟶ (restriction J).obj U := (adjunction (J ⋙ K)).unit.app M
  have heq : (inductionComp J K).hom.app M =
      transposeMap K (induced J M) N (transposeMap J M U f) := by
    dsimp only [transposeMap]
    erw [Functor.map_comp, Category.assoc]
    exact inductionComp_hom_eq J K M
  rw [heq]
  erw [transposeMap_comp_tensor J K M N f]
  change postcompose (J ⋙ K) M.toFunctor g
    (postcompose (J ⋙ K) M.toFunctor (K.map h) (unit (J ⋙ K) M.toFunctor v m)) = _
  rw [unit_apply, postcompose_tensor, postcompose_tensor, Category.id_comp]

private theorem compUnit_apply (M : Superfunctor k C (SVec k)) (v : C) (m : M.obj v) :
    (((adjunction J).unit.app M ≫
      (restriction J).map ((adjunction K).unit.app ((induction J).obj M))).app 0 v) m =
      tensor K (induced J M).toFunctor (J.obj v) (𝟙 _) (tensor J M.toFunctor v (𝟙 _) m) := by
  change unit K (induced J M).toFunctor (J.obj v) (unit J M.toFunctor v m) + 0 = _
  rw [add_zero]
  rfl

@[simp] theorem inductionComp_inv_tensor (M : Superfunctor k C (SVec k))
    (v : C) (z : E) (a : K.obj (J.obj v) ⟶ z) (m : M.obj v) :
    ((inductionComp J K).inv.app M).app 0 z (tensor (J ⋙ K) M.toFunctor v a m) =
      tensor K (induced J M).toFunctor (J.obj v) a (tensor J M.toFunctor v (𝟙 _) m) := by
  let N := (induction K).obj ((induction J).obj M)
  let f : M ⟶ (restriction (J ⋙ K)).obj N :=
    (adjunction J).unit.app M ≫
      (restriction J).map ((adjunction K).unit.app ((induction J).obj M))
  have heq : (inductionComp J K).inv.app M = transposeMap (J ⋙ K) M N f :=
    inductionComp_inv_eq J K M
  rw [heq]
  erw [transposeMap_tensor (J ⋙ K) M N f]
  have hf := compUnit_apply J K M v m
  change f.app 0 v m = _ at hf
  rw [hf]
  change postcompose K (induced J M).toFunctor a
    (tensor K (induced J M).toFunctor (J.obj v) (𝟙 _) (tensor J M.toFunctor v (𝟙 _) m)) = _
  erw [postcompose_tensor, Category.id_comp]

@[simp] theorem inductionComp_hom_app_one (M : Superfunctor k C (SVec k)) (z : E) :
    ((inductionComp J K).hom.app M).app 1 z = 0 :=
  Superfunctor.app_eq_zero_of_mem (inductionComp_hom_mem J K M) (by decide) z

@[simp] theorem inductionComp_inv_app_one (M : Superfunctor k C (SVec k)) (z : E) :
    ((inductionComp J K).inv.app M).app 1 z = 0 :=
  Superfunctor.app_eq_zero_of_mem (inductionComp_inv_mem J K M) (by decide) z

/-- The total map is the sign-free flattening map, since the comparison is even. -/
theorem inductionComp_hom_total_tensor (M : Superfunctor k C (SVec k))
    (v : C) (w : D) (z : E) (g : K.obj w ⟶ z) (h : J.obj v ⟶ w) (m : M.obj v) :
    ((inductionComp J K).hom.app M).total z
      (tensor K (induced J M).toFunctor w g (tensor J M.toFunctor v h m)) =
      tensor (J ⋙ K) M.toFunctor v (K.map h ≫ g) m := by
  rw [SuperNatTrans.total, inductionComp_hom_app_one, add_zero]
  exact inductionComp_hom_tensor J K M v w z g h m

/-- The inverse inserts the identity in the inner tensor factor. -/
theorem inductionComp_inv_total_tensor (M : Superfunctor k C (SVec k))
    (v : C) (z : E) (a : K.obj (J.obj v) ⟶ z) (m : M.obj v) :
    ((inductionComp J K).inv.app M).total z (tensor (J ⋙ K) M.toFunctor v a m) =
      tensor K (induced J M).toFunctor (J.obj v) a (tensor J M.toFunctor v (𝟙 _) m) := by
  rw [SuperNatTrans.total, inductionComp_inv_app_one, add_zero]
  exact inductionComp_inv_tensor J K M v z a m

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Unit tensors under composition of balanced induction
These formulas supply the unit-generator computation for the scalar and
weighted append comparisons in SwappedVacuumCoordinates §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (M : Superfunctor k C (SVec k))

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]

/-- An even input-module map acts on the literal tensor without a parity twist. -/
theorem moduleMap_total_tensor_even
    {M L : Superfunctor k C (SVec k)} (f : M ⟶ L)
    (hf : f ∈ parity (R := k) _ _ 0) (w : D) (v : C)
    (g : J.obj v ⟶ w) (b : M.obj v) :
    (moduleMap J f).total w (tensor J M.toFunctor v g b) =
      tensor J L.toFunctor v g (f.app 0 v b) := by
  rw [moduleMap_total_tensor, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide),
    LinearMap.zero_apply, tensor_zero_right, add_zero]

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Homogeneous transformations on balanced ELV induction

A parity-`p` supernatural transformation `α : J ⇒ K` induces `Ind K ⇒ Ind J`
by `[h ⊗ m] ↦ [α_v ≫ twist k p h ⊗ m]`. Balancing uses the full
supernaturality equation; the twist includes coefficient parity. Naturality
against module maps includes the outer Koszul sign. Unit compatibility and
counit compatibility are checked on vectors and balanced generators.

The concrete appended dot and crossing below are raw affine maps. This file
does not normalize equal-colour crossings, prove presentation relations on
iterated induction, assert a parameter twist, or construct the full action
of `DeformedActionAssembly.md` / `SwappedActionAssembly.md`.
-/

noncomputable section
open CategoryTheory StringDiagrams TensorProduct Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
variable {J K : C ⥤ D} [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
variable {p : ZMod 2} {α : ∀ v, J.obj v ⟶ K.obj v} (hα : IsSupernatural k p α)
variable (M : Superfunctor k C (SVec k))

def transformSummand (w : D) (v : C) :
    (K.obj v ⟶ w) ⊗[k] M.obj v →ₗ[k] Obj J M.toFunctor w :=
  inclusion J M.toFunctor w v ∘ₗ TensorProduct.map
    (({ toFun := fun h => α v ≫ h
        map_add' := fun _ _ => Preadditive.comp_add _ _ _ _ _ _
        map_smul' := fun _ _ => Linear.comp_smul _ _ _ _ _ _ } :
      (K.obj v ⟶ w) →ₗ[k] (J.obj v ⟶ w)) ∘ₗ twist k p) LinearMap.id

omit [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K] in
@[simp] theorem transformSummand_tmul (w : D) (v : C) (h : K.obj v ⟶ w) (m : M.obj v) :
    transformSummand (p := p) (α := α) M w v (h ⊗ₜ[k] m) =
      tensor J M.toFunctor v (α v ≫ twist k p h) m := rfl

omit [J.Linear k] [IsSuperfunctor k J] in
include hα in
theorem transformSummand_balance (w : D) (v v' : C) (a : v ⟶ v')
    (h : K.obj v' ⟶ w) (m : M.obj v) :
    transformSummand (p := p) (α := α) M w v ((K.map a ≫ h) ⊗ₜ[k] m) =
      transformSummand (p := p) (α := α) M w v' (h ⊗ₜ[k] M.map a m) := by
  rw [transformSummand_tmul, transformSummand_tmul, twist_comp, ← map_twist K,
    ← Category.assoc, ← hα.naturality_twist a, Category.assoc, balance]

def transformLinear (w : D) : Obj K M.toFunctor w →ₗ[k] Obj J M.toFunctor w :=
  lift K M.toFunctor w (transformSummand (p := p) (α := α) M w)
    (transformSummand_balance hα M w)

omit [J.Linear k] [IsSuperfunctor k J] in
@[simp] theorem transformLinear_tensor (w : D) (v : C) (h : K.obj v ⟶ w) (m : M.obj v) :
    transformLinear hα M w (tensor K M.toFunctor v h m) =
      tensor J M.toFunctor v (α v ≫ twist k p h) m := by
  rw [transformLinear, lift_tensor, transformSummand_tmul]

theorem transformLinear_mem (w : D) :
    (transformLinear hα M w : superspace K M.toFunctor w ⟶ superspace J M.toFunctor w) ∈
      parity (R := k) (superspace K M.toFunctor w) (superspace J M.toFunctor w) p := by
  change ∀ q, transformLinear hα M w ∘ₗ (superspace K M.toFunctor w).proj q =
    (superspace J M.toFunctor w).proj (q + p) ∘ₗ transformLinear hα M w
  intro q
  apply hom_ext
  intro v h m
  change transformLinear hα M w ((superspace K M.toFunctor w).proj q
    (tensor K M.toFunctor v h m)) = (superspace J M.toFunctor w).proj (q + p)
    (transformLinear hα M w (tensor K M.toFunctor v h m))
  rw [BalancedInduction.proj_tensor K M.toFunctor w q, map_add,
    transformLinear_tensor, transformLinear_tensor, transformLinear_tensor,
    BalancedInduction.proj_tensor J M.toFunctor w (q + p)]
  rw [show q + p = p + q by abel, proj_comp_of_mem_left (R := k) q (hα.mem v),
    show p + q + 1 = p + (q + 1) by abel,
    proj_comp_of_mem_left (R := k) (q + 1) (hα.mem v)]
  simp only [proj_twist, twist_of_mem p (proj_mem (R := k) _ _)]

omit [J.Linear k] [IsSuperfunctor k J] in
theorem transformLinear_naturality {w z : D} (a : w ⟶ z) :
    transformLinear hα M z ∘ₗ postcompose K M.toFunctor a =
      postcompose J M.toFunctor (twist k p a) ∘ₗ transformLinear hα M w := by
  apply hom_ext
  intro v h m
  simp only [LinearMap.comp_apply, postcompose_tensor, transformLinear_tensor,
    twist_comp, Category.assoc]

theorem transformLinear_supernatural :
    IsSupernatural k p (F := (induced K M).toFunctor) (G := (induced J M).toFunctor)
      (transformLinear hα M) :=
  IsSupernatural.of_twist (transformLinear_mem hα M)
    (fun a => transformLinear_naturality hα M a)

/-- The induced homogeneous map, contravariant in the append functor. -/
def transformComponent : induced K M ⟶ induced J M :=
  Superfunctor.homMk (transformLinear_supernatural hα M).toSuperNatTrans

@[simp] theorem transformComponent_app (q : ZMod 2) (w : D) :
    (transformComponent hα M).app q w = if q = p then transformLinear hα M w else 0 := rfl

@[simp] theorem transformComponent_apply (q : ZMod 2) (w : D)
    (x : Obj K M.toFunctor w) :
    (transformComponent hα M).app q w x = if q = p then transformLinear hα M w x else 0 := by
  simp only [transformComponent_app]
  split_ifs <;> rfl

theorem transformComponent_mem : transformComponent hα M ∈ parity (R := k) _ _ p :=
  Superfunctor.IsSupernatural.toSuperNatTrans_mem (transformLinear_supernatural hα M)

theorem transform_mapComponent {L : Superfunctor k C (SVec k)} (f : M ⟶ L)
    (q : ZMod 2) (w : D) :
    transformLinear hα L w ∘ₗ mapComponent K f q w =
      sign k (p * q) • (mapComponent J f q w ∘ₗ transformLinear hα M w) := by
  apply hom_ext
  intro v h m
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, transformLinear_tensor,
    mapComponent_tensor, twist_comp, twist_of_mem q (hα.mem v), Linear.smul_comp]
  rw [← twist_add, ← twist_add, add_comm q p]
  simp only [tensor, ← smul_tmul', map_smul, smul_smul, mul_comm q p,
    Supercategory.sign_mul_self, one_smul]

theorem transformComponent_supernatural :
    IsSupernatural k p (F := induction K) (G := induction J) (transformComponent hα) where
  mem := transformComponent_mem hα
  naturality := by
    intro M L q f hf
    apply Superfunctor.hom_ext
    intro r w
    apply hom_ext
    intro v h m
    change (transformComponent hα L).app r w
        (mapComponent K f 0 w (tensor K M.toFunctor v h m)) +
      (transformComponent hα L).app (r + 1) w
        (mapComponent K f 1 w (tensor K M.toFunctor v h m)) =
      sign k (p * q) • (mapComponent J f r w
        ((transformComponent hα M).app 0 w (tensor K M.toFunctor v h m)) +
      mapComponent J f (r + 1) w
        ((transformComponent hα M).app 1 w (tensor K M.toFunctor v h m)))
    have he := congrArg (fun l => l (tensor K M.toFunctor v h m))
      (transform_mapComponent hα M f q w)
    have hz (s : ZMod 2) (hs : s ≠ q) (v : C) := Superfunctor.app_eq_zero_of_mem hf hs v
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      rcases parity_eq_zero_or_one q with rfl | rfl <;>
      rcases parity_eq_zero_or_one r with rfl | rfl <;>
      simp only [transformComponent_apply] <;>
      simp_all [mapComponent_tensor, SVec.zmod2_one_add_one,
        LinearMap.comp_apply, LinearMap.smul_apply]

/-- Supernatural also in arbitrary homogeneous module maps, with the outer Koszul sign. -/
def transform : SuperNatTrans k (induction (k := k) K) (induction (k := k) J) :=
  (transformComponent_supernatural hα).toSuperNatTrans

omit [J.Linear k] [IsSuperfunctor k J] in
/-- Unit compatibility for the contravariant mate, on every module vector. -/
theorem transform_unit (v : C) (m : M.obj v) :
    transformLinear hα M (K.obj v) (unit K M.toFunctor v m) =
      postcompose J M.toFunctor (α v) (unit J M.toFunctor v m) := by
  rw [unit_apply, transformLinear_tensor, twist_id, Category.comp_id, postcompose_unit]

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- A homogeneous appended affine map induces a transformation in the reverse direction. -/
def moduleInductionTransform {σ τ : List I} {p : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (ha : a ∈ parity (R := k) _ _ p) :
    SuperNatTrans k (moduleInduction D Sc cutoff N τ) (moduleInduction D Sc cutoff N σ) :=
  BalancedInduction.transform (truncatedAppendComponent_supernatural D Sc cutoff N ha)

@[simp] theorem moduleInductionTransform_tensor {σ τ : List I} {p : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (ha : a ∈ parity (R := k) _ _ p) (M : TruncatedModules D Sc cutoff N)
    (w v : TruncatedCategory D Sc cutoff N)
    (h : (truncatedAppend D Sc cutoff N τ).obj v ⟶ w) (m : M.obj v) :
    ((moduleInductionTransform D Sc cutoff N ha).app p M).app p w
      (BalancedInduction.tensor (truncatedAppend D Sc cutoff N τ) M.toFunctor v h m) =
    BalancedInduction.tensor (truncatedAppend D Sc cutoff N σ) M.toFunctor v
      (truncatedAppendComponent D Sc cutoff N a v ≫ twist k p h) m := by
  simp only [moduleInductionTransform, BalancedInduction.transform,
    IsSupernatural.toSuperNatTrans, ↓reduceIte]
  change ((BalancedInduction.transformComponent
    (truncatedAppendComponent_supernatural D Sc cutoff N ha) M).app p w)
    (BalancedInduction.tensor (truncatedAppend D Sc cutoff N τ) M.toFunctor v h m) = _
  rw [BalancedInduction.transformComponent_apply]
  simp only [↓reduceIte, BalancedInduction.transformLinear_tensor]

/-- The raw appended dot. This does not assert a normalized SKM action. -/
def moduleInductionDot (i : I) :
    SuperNatTrans k (moduleInduction D Sc cutoff N [i]) (moduleInduction D Sc cutoff N [i]) :=
  moduleInductionTransform D Sc cutoff N (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

/-- The raw appended crossing reverses append-transformation direction.
No equal-colour normalization or parameter twist is asserted. -/
def moduleInductionCross (i j : I) :
    SuperNatTrans k (moduleInduction D Sc cutoff N [j, i])
      (moduleInduction D Sc cutoff N [i, j]) :=
  moduleInductionTransform D Sc cutoff N (crossTwo_mem D Sc i j)

@[simp] theorem moduleInductionDot_tensor (i : I) (M : TruncatedModules D Sc cutoff N)
    (w v : TruncatedCategory D Sc cutoff N)
    (h : (truncatedAppend D Sc cutoff N [i]).obj v ⟶ w) (m : M.obj v) :
    ((moduleInductionDot D Sc cutoff N i).app (D.parity i) M).app (D.parity i) w
      (BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i]) M.toFunctor v h m) =
    BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i]) M.toFunctor v
      (truncatedAppendComponent D Sc cutoff N (dotE D Sc [i] 0) v ≫
        twist k (D.parity i) h) m :=
  moduleInductionTransform_tensor D Sc cutoff N _ M w v h m

@[simp] theorem moduleInductionCross_tensor (i j : I) (M : TruncatedModules D Sc cutoff N)
    (w v : TruncatedCategory D Sc cutoff N)
    (h : (truncatedAppend D Sc cutoff N [j, i]).obj v ⟶ w) (m : M.obj v) :
    ((moduleInductionCross D Sc cutoff N i j).app (D.parity i * D.parity j) M).app
      (D.parity i * D.parity j) w
      (BalancedInduction.tensor (truncatedAppend D Sc cutoff N [j, i]) M.toFunctor v h m) =
    BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i, j]) M.toFunctor v
      (truncatedAppendComponent D Sc cutoff N (crossTwo D Sc i j) v ≫
        twist k (D.parity i * D.parity j) h) m :=
  moduleInductionTransform_tensor D Sc cutoff N _ M w v h m

end OddMath.QuiverHecke.ELVOld
end

end

section

noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
variable {J K L : C ⥤ D}
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [L.Additive] [L.Linear k] [IsSuperfunctor k L]
variable {p q : ZMod 2} {α : ∀ v, J.obj v ⟶ K.obj v}
  {β : ∀ v, K.obj v ⟶ L.obj v}
  (hα : IsSupernatural k p α) (hβ : IsSupernatural k q β)

omit [J.Linear k] [IsSuperfunctor k J] in
/-- Contravariance of homogeneous induction maps has the superopposite sign. -/
theorem transformLinear_comp (M : Superfunctor k C (SVec k)) (w : D) :
    transformLinear hα M w ∘ₗ transformLinear hβ M w =
      sign k (p * q) • transformLinear (hα.comp hβ) M w := by
  apply hom_ext
  intro v h m
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, transformLinear_tensor,
    twist_comp, twist_of_mem p (hβ.mem v), ← twist_add, Linear.comp_smul,
    Linear.smul_comp, Category.assoc]
  simp only [tensor, ← TensorProduct.smul_tmul', map_smul]

/-- Signed contravariant composition as an equality of module morphisms. -/
theorem transformComponent_comp (M : Superfunctor k C (SVec k)) :
    transformComponent hβ M ≫ transformComponent hα M =
      sign k (p * q) • transformComponent (hα.comp hβ) M := by
  apply Superfunctor.hom_ext
  intro r w
  have he := transformLinear_comp hα hβ M w
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp only [Superfunctor.comp_app, Superfunctor.smul_app, transformComponent_app,
      SVec.zmod2_one_add_one, zero_add, add_zero, ↓reduceIte, one_ne_zero, zero_ne_one,
      CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp, smul_zero,
      zero_add, add_zero] <;> exact he

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end
