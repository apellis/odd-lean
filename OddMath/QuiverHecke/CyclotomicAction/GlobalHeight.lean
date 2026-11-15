import OddMath.QuiverHecke.CyclotomicAction.GlobalInduction
import OddMath.QuiverHecke.CyclotomicAction.SuperAdjunction
import OddMath.QuiverHecke.Centre
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import OddMath.QuiverHecke.CyclotomicAction.LastStrand
import OddMath.SKM.Calculus
import OddMath.QuiverHecke.MixedRelations

/-!
# Global height

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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

/-- The component of parity `|i||j|` is precisely the transported corner crossing. -/
@[simp] theorem heightSuperInductionCrossing_app
    (M : HeightModules D Sc a ha n) :
    (heightSuperInductionCrossing D Sc i j a ha n).app d M =
      (e).hom.app M ≫ whiskerRight (heightCompositionSuperCrossing D Sc i j a ha n) M ≫
        (e').inv.app M := by
  simp [heightSuperInductionCrossing, heightInductionCrossingApp]

end CrossingTransformation

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The dot on induction at every height and on global content blocks

Supports the dot of `Categorification/KLR/CyclotomicAction/Global.lean`
(`globalDot`). `heightLastDot` is the last dot of the extended tower: at one
strand it is the image of `affineLastDot` in the height-one quotient, and at
positive height it is `cyclotomicLastDot`. The signed-left corner map
`x ↦ (-1)^{|i||x|} x c` of `SuperDot` is restated along `heightAppend`, giving
`heightSuperInductionDot`, homogeneous of parity `|i|` (odd colours get the
odd dot). It restricts to content blocks and transports to the global content
categories (`globalContentDot`).
-/

noncomputable section
open CategoryTheory StringDiagrams
open Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

section LastDot
variable (a : I → _root_.Polynomial k) (i : I)

/-- The last dot of the extended tower, in the algebra one strand up. -/
def heightLastDot : (n : ℕ) → heightAlgebra D Sc a (n + 1)
  | 0 => cyclotomicMk D Sc a 0 (affineLastDot D Sc i 0)
  | n + 1 => cyclotomicLastDot D Sc i a n

theorem heightLastDot_parity (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    heightLastDot D Sc a i n ∈ heightParity D Sc a ha (n + 1) (D.parity i) := by
  cases n with
  | zero => exact cyclotomicMk_parity D Sc a ha 0 (affineLastDot_parity D Sc i 0)
  | succ n => exact cyclotomicLastDot_parity D Sc i a ha n

theorem heightLastDot_comm (ha : CyclotomicPolynomialParity D a) (n : ℕ) {p : ZMod 2}
    {r : heightAlgebra D Sc a n} (hr : r ∈ heightParity D Sc a ha n p) :
    heightAppend D Sc a i n r * heightLastDot D Sc a i n =
      Supercategory.koszulSign p (D.parity i) •
        (heightLastDot D Sc a i n * heightAppend D Sc a i n r) := by
  cases n with
  | zero =>
    change cyclotomicMk D Sc a 0 (appendAlgebra D Sc i 0 r) *
      cyclotomicMk D Sc a 0 (affineLastDot D Sc i 0) =
      Supercategory.koszulSign p (D.parity i) •
        (cyclotomicMk D Sc a 0 (affineLastDot D Sc i 0) *
          cyclotomicMk D Sc a 0 (appendAlgebra D Sc i 0 r))
    rw [← map_mul, ← map_mul, ← map_zsmul]
    exact congrArg (cyclotomicMk D Sc a 0) (affineLastDot_comm D Sc i 0 hr)
  | succ n => exact cyclotomicLastDot_comm D Sc i a ha n hr

theorem heightLastDot_corner (n : ℕ) :
    heightAppend D Sc a i n 1 * heightLastDot D Sc a i n = heightLastDot D Sc a i n ∧
    heightLastDot D Sc a i n * heightAppend D Sc a i n 1 = heightLastDot D Sc a i n := by
  cases n with
  | zero =>
    change cyclotomicMk D Sc a 0 (appendAlgebra D Sc i 0 1) *
        cyclotomicMk D Sc a 0 (affineLastDot D Sc i 0) =
        cyclotomicMk D Sc a 0 (affineLastDot D Sc i 0) ∧
      cyclotomicMk D Sc a 0 (affineLastDot D Sc i 0) *
        cyclotomicMk D Sc a 0 (appendAlgebra D Sc i 0 1) =
        cyclotomicMk D Sc a 0 (affineLastDot D Sc i 0)
    rw [← map_mul, ← map_mul, append_one_mul_affineLastDot, affineLastDot_mul_append_one]
    exact ⟨rfl, rfl⟩
  | succ n => exact cyclotomicLastDot_corner D Sc i a n

end LastDot

variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => heightInductionCorner D Sc i a ha n
local notation "GB" => heightParity D Sc a ha (n + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "c" => heightLastDot D Sc a i n
local notation "d" => D.parity i

private theorem height_dot_mul_mem (x : heightAlgebra D Sc a (n + 1))
    (_hx : x ∈ heightInductionCornerSubmodule D Sc i a n) :
    x * c ∈ heightInductionCornerSubmodule D Sc i a n := by
  change (x * c) * heightAppend D Sc a i n 1 = x * c
  rw [mul_assoc, (heightLastDot_corner D Sc a i n).2]

/-- The parity sign followed by right multiplication by the last dot. -/
def heightInductionDotLinear : (P).toSVec ⟶ (P).toSVec :=
  SVec.ofHom ((P).toSVec.sgn d) ≫
    SVec.restrictHom ((SuperBimodule.regular GB).ract c) (height_dot_mul_mem D Sc i a n)

/-- The dot has the parity of the induction colour. -/
theorem heightInductionDotLinear_parity :
    heightInductionDotLinear D Sc i a ha n ∈ SVec.parityHom (P).toSVec (P).toSVec d := by
  change heightInductionDotLinear D Sc i a ha n ∈ parity (R := k) (P).toSVec (P).toSVec d
  unfold heightInductionDotLinear
  have hd := SVec.restrictHom_mem (hU := heightInductionCorner_odd_mem D Sc i a ha n)
    (hU' := heightInductionCorner_odd_mem D Sc i a ha n)
    ((SuperBimodule.regular GB).ract_mem d c
      (heightLastDot_parity D Sc a i ha n)) (height_dot_mul_mem D Sc i a n)
  simpa only [heightInductionCorner, heightInductionCornerSpace, SuperBimodule.regular, zero_add] using
    Supercategory.comp_mem (SVec.sgn_mem (P).toSVec d) hd

private theorem height_sgn_action {p : ZMod 2} {f : (P).toSVec ⟶ (P).toSVec}
    (hf : f ∈ SVec.parityHom (P).toSVec (P).toSVec p) (x : (P).toSVec) :
    (P).toSVec.sgn d (f x) = sign k (p * d) • f ((P).toSVec.sgn d x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf d) x

/-- Signed left linearity and ordinary right linearity use the concrete last-dot slide. -/
theorem heightInductionDotLinear_isHom :
    SuperBimodule.IsHom P P (heightInductionDotLinear D Sc i a ha n) := by
  apply (SuperBimodule.isHom_iff_of_mem (heightInductionDotLinear_parity D Sc i a ha n)).2
  constructor
  · intro p b hb
    apply SVec.hom_ext
    intro x
    have h := height_sgn_action D Sc i a ha n ((P).lact_mem p b hb) x
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
      have h := height_sgn_action D Sc i a ha n ((P).ract_mem p r hr) x
      apply Subtype.ext
      change ((P).toSVec.sgn d ((P).ract r x)).val * c =
        (((P).toSVec.sgn d x).val * c) * heightAppend D Sc a i n r
      rw [h]
      change (sign k (p * d) • (((P).toSVec.sgn d x).val *
        heightAppend D Sc a i n r)) * c = _
      rw [smul_mul_assoc, mul_assoc, heightLastDot_comm D Sc a i ha n hr,
        mul_smul_comm, Supercategory.sign_mul, Int.cast_smul_eq_zsmul, koszulSign_smul_smul, mul_assoc]

/-- The homogeneous dot endomorphism of the induction corner at every height. -/
def heightInductionSuperDot : P ⟶ P :=
  ⟨heightInductionDotLinear D Sc i a ha n, heightInductionDotLinear_isHom D Sc i a ha n⟩

theorem heightInductionSuperDot_parity :
    heightInductionSuperDot D Sc i a ha n ∈ parity (R := k) P P d :=
  SuperBimodule.mem_parity_iff.2 (heightInductionDotLinear_parity D Sc i a ha n)

/-- The last dot as a supernatural endomorphism of balanced-tensor induction. -/
def heightSuperInductionDot :
    SuperNatTrans k (heightSuperInduction D Sc i a ha n)
      (heightSuperInduction D Sc i a ha n) where
  app p M := if p = d then SuperBimodule.whiskerRight (heightInductionSuperDot D Sc i a ha n) M else 0
  app_mem p M := by
    split_ifs with h
    · subst p
      exact SuperBimodule.whiskerRight_mem P (heightInductionSuperDot_parity D Sc i a ha n) M
    · exact Submodule.zero_mem _
  naturality p M N q f hf := by
    change SuperBimodule.whiskerLeft P f ≫ (if p = d then
        SuperBimodule.whiskerRight (heightInductionSuperDot D Sc i a ha n) N else 0) =
      koszulSign p q • ((if p = d then
        SuperBimodule.whiskerRight (heightInductionSuperDot D Sc i a ha n) M else 0) ≫
          SuperBimodule.whiskerLeft P f)
    split_ifs with h
    · subst p
      rw [SuperBimodule.super_interchange P f (heightInductionSuperDot_parity D Sc i a ha n) hf,
        koszulSign_smul_smul]
    · simp

/-- The dot restricted to content blocks at every height. -/
def heightContentDot (β : Multiset I) :
    SuperNatTrans k (heightContentInduction D Sc i a ha n β).toFunctor
      (heightContentInduction D Sc i a ha n β).toFunctor :=
  fullLiftTrans _ _ (heightContentSupported_induction D Sc i a ha n β)
    (heightContentSupported_induction D Sc i a ha n β) (heightSuperInductionDot D Sc i a ha n)

/-- A supernatural endomorphism followed by an identity transport. -/
def heightContentCastTrans {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m') (hγ : γ = γ')
    {F : C ⥤ ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m γ)}
    [F.Additive] [F.Linear k] [IsSuperfunctor k F] (η : SuperNatTrans k F F) :
    SuperNatTrans k (F ⋙ (heightContentCast D Sc a ha hm hγ).toFunctor)
      (F ⋙ (heightContentCast D Sc a ha hm hγ).toFunctor) := by
  subst hm
  subst hγ
  exact η

/-- **The dot on global content induction**, `δ = {i} + β`. -/
def globalContentDot {β δ : Multiset I} (h : {i} + β = δ) :
    SuperNatTrans k (globalContentInduction D Sc i a ha h).toFunctor
      (globalContentInduction D Sc i a ha h).toFunctor :=
  heightContentCastTrans D Sc a ha (card_of_add i h) h (heightContentDot D Sc i a ha β.card β)

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The dot–crossing relations of the last pair of strands

The algebra half of the slide relations of `Categorification/KLR/CyclotomicAction/GlobalSlides.lean`.
For equal colours the defining relations (1.8) of the quiver Hecke supercategory
(Brundan–Ellis, arXiv:1701.04133v2) read, with `s = (-1)^{|i|}`,

  `x₁ τ - s τ x₂ = 1`,  `τ x₁ - s x₂ τ = 1`

(diagrams read bottom to top, `x₁` the dot on the left strand). Whiskering by an old word
(`induction_slide_left`, `induction_slide_right`) and summing over words gives the
corresponding identities between `affineLastCrossing`, the appended last dot and the new last
dot, with the image of one on the right (`affineLastCrossing_slide_left`,
`affineLastCrossing_slide_right`). Since matrix multiplication reverses diagram composition,
in the algebra the relations read `c y₁ - s y₂ c = θ(1)` and `y₁ c - s c y₂ = θ(1)`. They
descend to every height of the extended tower (`heightLastCrossing_slide_left`,
`heightLastCrossing_slide_right`).
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
namespace OddMath.QuiverHecke
open SKM (zsign)
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

section Local

theorem zsmul_koszulSign_eq_zsign_smul {A : Type*} [AddCommGroup A] [Module k A] (p q : ZMod 2)
    (f : A) : Supercategory.koszulSign p q • f = zsign k (p * q) • f := by
  rcases Supercategory.parity_eq_zero_or_one p with rfl | rfl <;>
    rcases Supercategory.parity_eq_zero_or_one q with rfl | rfl <;>
    simp [Supercategory.koszulSign, zsign]

theorem inductionStrandCrossing_comp_dot_whiskerRight (i : I) :
    inductionStrandCrossing D Sc i i ≫ inductionStrandDot D Sc i ▷ (pres D Sc).obj (ob D [i]) =
      cl D Sc [i, i] [i, i] [.cross 0, .dot 0] (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod]) := by
  rw [inductionStrandDot, inductionStrandCrossing, Presentation.diag_whiskerRight, cl]
  exact (Presentation.diag_comp _ _ _).symm.trans (Presentation.diag_eq_of_layers_eq _ rfl)

theorem whiskerLeft_dot_comp_inductionStrandCrossing (i : I) :
    (pres D Sc).obj (ob D [i]) ◁ inductionStrandDot D Sc i ≫ inductionStrandCrossing D Sc i i =
      cl D Sc [i, i] [i, i] [.dot 1, .cross 0] (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod]) := by
  rw [inductionStrandDot, inductionStrandCrossing, Presentation.diag_whiskerLeft, cl]
  exact (Presentation.diag_comp _ _ _).symm.trans (Presentation.diag_eq_of_layers_eq _ rfl)

/-- **The right dot slide on two strands of equal colour**, `τ x₁ - s x₂ τ = 1`. -/
theorem inductionStrand_slide_right (i : I) :
    (inductionStrandCrossing D Sc i i ≫ inductionStrandDot D Sc i ▷ (pres D Sc).obj (ob D [i]) :
        (pres D Sc).obj (ob D [i, i]) ⟶ (pres D Sc).obj (ob D [i, i])) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        ((pres D Sc).obj (ob D [i]) ◁ inductionStrandDot D Sc i ≫
          inductionStrandCrossing D Sc i i :
          (pres D Sc).obj (ob D [i, i]) ⟶ (pres D Sc).obj (ob D [i, i])) = 𝟙 _ := by
  erw [inductionStrandCrossing_comp_dot_whiskerRight, whiskerLeft_dot_comp_inductionStrandCrossing]
  rw [zsmul_koszulSign_eq_zsign_smul (k := k), ]
  refine sub_eq_of_eq_add' ?_
  have hs := slide_right_eq D Sc [] [] i (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod])
    (by simp [pl, PG.ld, PG.act, Shape.dom, Shape.cod])
  exact hs.trans (congrArg (_ + ·) (cl_nil D Sc _ _))

end Local

section Word

/-- The two-strand crossing with its source and target written as tensor products. -/
def strandCrossingTensor (i j : I) :
    (pres D Sc).obj (ob D [i]) ⊗ (pres D Sc).obj (ob D [j]) ⟶
      (pres D Sc).obj (ob D [j]) ⊗ (pres D Sc).obj (ob D [i]) :=
  inductionStrandCrossing D Sc i j

theorem strandCrossingTensor_slide_right (i : I) :
    strandCrossingTensor D Sc i i ≫ inductionStrandDot D Sc i ▷ (pres D Sc).obj (ob D [i]) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        ((pres D Sc).obj (ob D [i]) ◁ inductionStrandDot D Sc i ≫ strandCrossingTensor D Sc i i) =
      𝟙 _ :=
  inductionStrand_slide_right D Sc i

theorem whiskerLeft_sub_zsmul {Y Z : H D Sc} (W : H D Sc) (f g : Y ⟶ Z) (c : ℤ) :
    W ◁ (f - c • g) = W ◁ f - c • (W ◁ g) := by
  rw [sub_eq_add_neg, MonoidalSupercategory.whiskerLeft_add (R := k),
    MonoidalSupercategory.whiskerLeft_neg (R := k), MonoidalSupercategory.whiskerLeft_zsmul (R := k),
    ← sub_eq_add_neg]

theorem whiskerLeft_comp_comp (W : H D Sc) {Y₁ Y₂ Y₃ Z : H D Sc} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃)
    (h : W ⊗ Y₃ ⟶ Z) : W ◁ f ≫ W ◁ g ≫ h = W ◁ (f ≫ g) ≫ h := by
  rw [← Category.assoc, ← MonoidalSupercategory.whiskerLeft_comp (R := k)]

/-- Conjugating a two-strand identity by the associators. -/
theorem associator_conj_sub {W : H D Sc} {Y₁ Y₂ : H D Sc} (f g : Y₁ ⊗ Y₂ ⟶ Y₁ ⊗ Y₂) (c : ℤ)
    (h : f - c • g = 𝟙 _) :
    (α_ W Y₁ Y₂).hom ≫ W ◁ f ≫ (α_ W Y₁ Y₂).inv -
      c • ((α_ W Y₁ Y₂).hom ≫ W ◁ g ≫ (α_ W Y₁ Y₂).inv) = 𝟙 _ := by
  rw [← Preadditive.comp_zsmul, ← Preadditive.zsmul_comp, ← Preadditive.comp_sub,
    ← Preadditive.sub_comp, ← whiskerLeft_sub_zsmul, h,
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp, Iso.hom_inv_id]

theorem associator_inv_whiskerRight_tensor (W Y : H D Sc) {Z Z' : H D Sc} (f : Z ⟶ Z') :
    (α_ W Z Y).inv ≫ (W ◁ f) ▷ Y = W ◁ (f ▷ Y) ≫ (α_ W Z' Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← MonoidalSupercategory.associator_naturality_middle k,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The right dot slide on the last pair of an appended word.** -/
theorem induction_slide_right (i : I) {n : ℕ} (w : Word I n) :
    inductionLastCrossing D Sc i i w ≫ appendHom D Sc i _ _ (inductionLastDot D Sc i w) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (inductionLastDot D Sc i (appendWord i w) ≫ inductionLastCrossing D Sc i i w) = 𝟙 _ := by
  change ((α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [i]))).hom ≫
      wordObj D Sc w ◁ strandCrossingTensor D Sc i i ≫
      (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [i]))).inv) ≫
      (wordObj D Sc w ◁ inductionStrandDot D Sc i) ▷ (pres D Sc).obj (ob D [i]) -
    Supercategory.koszulSign (D.parity i) (D.parity i) •
      ((wordObj D Sc w ⊗ (pres D Sc).obj (ob D [i])) ◁ inductionStrandDot D Sc i ≫
        (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [i]))).hom ≫
        wordObj D Sc w ◁ strandCrossingTensor D Sc i i ≫
        (α_ (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D [i]))).inv) = 𝟙 _
  simp only [Category.assoc]
  rw [associator_inv_whiskerRight_tensor, ← Category.assoc ((wordObj D Sc w ⊗ _) ◁ _),
    MonoidalSupercategory.associator_naturality_right k, Category.assoc]
  simp only [whiskerLeft_comp_comp]
  exact associator_conj_sub D Sc _ _ _ (strandCrossingTensor_slide_right D Sc i)

end Word

section Affine
variable [Fintype I]

omit [Fintype I] in
private theorem single_sub_zsmul {n : ℕ} (s t : Word I n) (f g : wordObj D Sc s ⟶ wordObj D Sc t)
    (c : ℤ) :
    (FiniteHomMatrix.single t s f : Hn D Sc n) - c • FiniteHomMatrix.single t s g =
      FiniteHomMatrix.single t s (f - c • g) := by
  simp only [FiniteHomMatrix.single, DFinsupp.single_sub, DFinsupp.single_smul]

private theorem entry_mul_lastDot' (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (appendWord i t)) :
    FiniteHomMatrix.single (appendWord i t) (appendWord i s) f * affineLastDot D Sc i n =
      FiniteHomMatrix.single (appendWord i t) (appendWord i s)
        (inductionLastDot D Sc i s ≫ f) := by
  rw [affineLastDot, Finset.mul_sum, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n h.symm)) _ _
  · simp

private theorem entry_mul_crossing' (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (appendWord i (appendWord i s)) ⟶
      wordObj D Sc (appendWord i (appendWord i t))) :
    FiniteHomMatrix.single (appendWord i (appendWord i t)) (appendWord i (appendWord i s)) f *
      affineLastCrossing D Sc i i n =
    FiniteHomMatrix.single (appendWord i (appendWord i t)) (appendWord i (appendWord i s))
      (inductionLastCrossing D Sc i i s ≫ f) := by
  rw [affineLastCrossing, Finset.mul_sum, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n (appendWord_injective i (n + 1) h.symm))) _ _
  · simp

private theorem append_affineLastDot_eq_sum (i : I) (n : ℕ) :
    appendAlgebra D Sc i (n + 1) (affineLastDot D Sc i n) =
      ∑ w : Word I n, FiniteHomMatrix.single (appendWord i (appendWord i w))
        (appendWord i (appendWord i w)) (appendHom D Sc i _ _ (inductionLastDot D Sc i w)) := by
  change appendLinear D Sc i (n + 1) (affineLastDot D Sc i n) = _
  rw [affineLastDot, map_sum]
  exact Finset.sum_congr rfl fun w _ => appendLinear_single D Sc i _ _ _

private theorem append_append_one_eq_sum (i : I) (n : ℕ) :
    appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) =
      ∑ w : Word I n, FiniteHomMatrix.single (appendWord i (appendWord i w))
        (appendWord i (appendWord i w)) (𝟙 _) := by
  change appendLinear D Sc i (n + 1)
    (appendLinear D Sc i n (FiniteHomMatrix.localUnit Finset.univ)) = _
  rw [FiniteHomMatrix.localUnit, map_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  change appendLinear D Sc i (n + 1)
    (appendLinear D Sc i n (FiniteHomMatrix.single w w (𝟙 _))) = _
  rw [appendLinear_single, appendLinear_single]
  change FiniteHomMatrix.single _ _ (appendEnd D Sc i _ (appendEnd D Sc i w 1)) = _
  rw [map_one, map_one]
  rfl

private theorem affineLastCrossing_eq_sum (i : I) (n : ℕ) :
    affineLastCrossing D Sc i i n =
      ∑ w : Word I n, FiniteHomMatrix.single (appendWord i (appendWord i w))
        (appendWord i (appendWord i w)) (inductionLastCrossing D Sc i i w) := rfl

/-- **The right slide in the affine algebra**: `y₁ c - s c y₂ = θ(1)`. -/
theorem affineLastCrossing_slide_right (i : I) (n : ℕ) :
    appendAlgebra D Sc i (n + 1) (affineLastDot D Sc i n) * affineLastCrossing D Sc i i n -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (affineLastCrossing D Sc i i n * affineLastDot D Sc i (n + 1)) =
      appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) := by
  rw [append_affineLastDot_eq_sum, append_append_one_eq_sum, Finset.sum_mul]
  simp only [entry_mul_crossing']
  rw [affineLastCrossing_eq_sum, Finset.sum_mul]
  simp only [entry_mul_lastDot']
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [single_sub_zsmul, induction_slide_right]

end Affine

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.CyclotomicAction
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] (a : I → _root_.Polynomial k) (i : I)

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The dot slides on two inductions from every height

The functor half of `Categorification/KLR/CyclotomicAction/GlobalSlides.lean` at a fixed
height. On the same-colour composition corner `T = C θ(1)` of `GlobalHeightCrossing`, signed
right multiplication by the new last dot `y₂` and by the appended dot `y₁ = φ(y)` are
superbimodule endomorphisms of parity `|i|` (`heightCompositionRightMul`). Along the comparison
`F ≅ T ⊗ -` of the two inductions, the dot of the outer induction whiskered by the inner one
becomes `y₂`, the inner dot under the outer induction becomes `y₁`
(`heightComparison_dot_outer`, `heightComparison_dot_inner`). The algebra slides of
`GlobalSlideAlgebra` then give, with `s = (-1)^{|i|}` and `ψ` the crossing,

  `x₂ ψ - s ψ x₁ = -1`,  `ψ x₂ - s x₁ ψ = -1`

for the components on every module (`heightInduction_slide_left`,
`heightInduction_slide_right`); with the Rouquier crossing `t = -ψ` these are the slides of
`SuperRouquierLoc`.
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

section RightMul
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "C" => heightAlgebra D Sc a (n + 1 + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "GC" => heightParity D Sc a ha (n + 1 + 1)
local notation "θ" => fun r => heightAppend D Sc a i (n + 1) (heightAppend D Sc a i n r)
local notation "T" => heightCompositionCorner D Sc i i a ha n
local notation "d" => D.parity i

/-- Hypotheses on an element `u` for signed right multiplication to be an endomorphism of the
same-colour composition corner: parity `|i|`, the corner is preserved, and `u`
supercommutes with the image of the base algebra. -/
structure CornerMulData (u : C) : Prop where
  mem : u ∈ GC d
  corner : ∀ x : C, x * θ 1 = x → (x * u) * θ 1 = x * u
  comm : ∀ {p : ZMod 2} {r : heightAlgebra D Sc a n}, r ∈ GA p →
    θ r * u = koszulSign p d • (u * θ r)

variable {i a ha n} in
private theorem cornerMul_mem {u : C} (hu : CornerMulData D Sc i a ha n u) (x : C)
    (hx : x ∈ heightCompositionCornerSubmodule D Sc i i a n) :
    x * u ∈ heightCompositionCornerSubmodule D Sc i i a n :=
  hu.corner x hx

/-- Parity sign followed by right multiplication by `u`. -/
def heightCompositionRightMulLinear {u : C} (hu : CornerMulData D Sc i a ha n u) :
    (T).toSVec ⟶ (T).toSVec :=
  SVec.ofHom ((T).toSVec.sgn d) ≫
    SVec.restrictHom ((SuperBimodule.regular GC).ract u) (cornerMul_mem D Sc hu)

theorem heightCompositionRightMulLinear_parity {u : C} (hu : CornerMulData D Sc i a ha n u) :
    heightCompositionRightMulLinear D Sc i a ha n hu ∈ SVec.parityHom (T).toSVec (T).toSVec d := by
  change heightCompositionRightMulLinear D Sc i a ha n hu ∈ parity (R := k) (T).toSVec (T).toSVec d
  unfold heightCompositionRightMulLinear
  have hd := SVec.restrictHom_mem (hU := heightCompositionCorner_odd_mem D Sc i i a ha n)
    (hU' := heightCompositionCorner_odd_mem D Sc i i a ha n)
    ((SuperBimodule.regular GC).ract_mem d u hu.mem) (cornerMul_mem D Sc hu)
  have h2 := Supercategory.comp_mem (SVec.sgn_mem (T).toSVec d) hd
  rw [zero_add] at h2
  exact h2

private theorem rightMul_sgn_action {p : ZMod 2} {f : (T).toSVec ⟶ (T).toSVec}
    (hf : f ∈ SVec.parityHom (T).toSVec (T).toSVec p) (x : (T).toSVec) :
    (T).toSVec.sgn d (f x) = sign k (p * d) • f ((T).toSVec.sgn d x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf d) x

theorem heightCompositionRightMulLinear_isHom {u : C} (hu : CornerMulData D Sc i a ha n u) :
    SuperBimodule.IsHom T T (heightCompositionRightMulLinear D Sc i a ha n hu) := by
  apply (SuperBimodule.isHom_iff_of_mem (heightCompositionRightMulLinear_parity D Sc i a ha n hu)).2
  constructor
  · intro p b hb
    apply SVec.hom_ext
    intro x
    have h := rightMul_sgn_action D Sc i a ha n ((T).lact_mem p b hb) x
    apply Subtype.ext
    change ((T).toSVec.sgn d ((T).lact b x)).val * u =
      sign k (p * d) • (b * (((T).toSVec.sgn d x).val * u))
    rw [h]
    change (sign k (p * d) • (b * ((T).toSVec.sgn d x).val)) * u = _
    rw [smul_mul_assoc, mul_assoc]
  · intro r
    induction r using SuperBimodule.alg_induction_on GA with
    | zero => simp
    | add r s hr hs => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hr, hs]
    | hom p r hr =>
      apply SVec.hom_ext
      intro x
      have h := rightMul_sgn_action D Sc i a ha n ((T).ract_mem p r hr) x
      apply Subtype.ext
      change ((T).toSVec.sgn d ((T).ract r x)).val * u =
        (((T).toSVec.sgn d x).val * u) *
          heightAppend D Sc a i (n + 1) (heightAppend D Sc a i n r)
      rw [h]
      change (sign k (p * d) • (((T).toSVec.sgn d x).val *
        heightAppend D Sc a i (n + 1) (heightAppend D Sc a i n r))) * u = _
      rw [smul_mul_assoc, mul_assoc, hu.comm hr,
        mul_smul_comm, Supercategory.sign_mul, Int.cast_smul_eq_zsmul, koszulSign_smul_smul,
        mul_assoc]

/-- **Signed right multiplication** as a homogeneous endomorphism of the corner. -/
def heightCompositionRightMul {u : C} (hu : CornerMulData D Sc i a ha n u) : T ⟶ T :=
  ⟨heightCompositionRightMulLinear D Sc i a ha n hu,
    heightCompositionRightMulLinear_isHom D Sc i a ha n hu⟩

/-- The new last dot `y₂` satisfies the corner hypotheses. -/
theorem cornerMulData_lastDot :
    CornerMulData D Sc i a ha n (heightLastDot D Sc a i (n + 1)) where
  mem := heightLastDot_parity D Sc a i ha (n + 1)
  corner x hx := by
    have h := heightLastDot_comm D Sc a i ha (n + 1)
      (heightAppend_parity D Sc a ha i n (SetLike.one_mem_graded GA))
    rw [koszulSign_zero_left, one_smul] at h
    rw [mul_assoc, ← h, ← mul_assoc, hx]
  comm hr := heightLastDot_comm D Sc a i ha (n + 1) (heightAppend_parity D Sc a ha i n hr)

/-- The appended dot `y₁ = φ(y)` satisfies the corner hypotheses. -/
theorem cornerMulData_appendDot :
    CornerMulData D Sc i a ha n (heightAppend D Sc a i (n + 1) (heightLastDot D Sc a i n)) where
  mem := heightAppend_parity D Sc a ha i (n + 1) (heightLastDot_parity D Sc a i ha n)
  corner x _ := by
    rw [mul_assoc, ← map_mul, (heightLastDot_corner D Sc a i n).2]
  comm {p} {r} hr := by
    rw [← map_mul, heightLastDot_comm D Sc a i ha n hr, map_zsmul, map_mul]

end RightMul

/-! ### Signs and additivity -/

section Additive
variable {a : I → _root_.Polynomial k} {ha : CyclotomicPolynomialParity D a} {m n : ℕ}

end Additive

/-! ### The slides on the corner -/

section CornerSlides
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "T" => heightCompositionCorner D Sc i i a ha n
local notation "d" => D.parity i
local notation "Dr" => heightCompositionRightMul D Sc i a ha n (cornerMulData_lastDot D Sc i a ha n)
local notation "Dl" => heightCompositionRightMul D Sc i a ha n (cornerMulData_appendDot D Sc i a ha n)
local notation "Cr" => heightCompositionSuperCrossing D Sc i i a ha n

end CornerSlides

/-! ### Transport along the comparison -/

section Transport
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "T" => heightCompositionCorner D Sc i i a ha n
local notation "Pc" => heightInductionCorner D Sc i a ha (n + 1)
local notation "Qc" => heightInductionCorner D Sc i a ha n
local notation "d" => D.parity i
local notation "Dr" => heightCompositionRightMul D Sc i a ha n (cornerMulData_lastDot D Sc i a ha n)
local notation "Dl" => heightCompositionRightMul D Sc i a ha n (cornerMulData_appendDot D Sc i a ha n)
local notation "Cr" => heightCompositionSuperCrossing D Sc i i a ha n
local notation "iso" => heightInductionCompositionIso D Sc i i a ha n
local notation "e" => heightInductionFunctorComparison D Sc i i a ha n

end Transport

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The distinct-colour dot–crossing relations of the last pair of strands

The algebra half of the distinct-colour slides (1.8) of Brundan–Ellis, arXiv:1701.04133v2,
Definition 1.5. For distinct colours `i ≠ j` the quiver Hecke supercategory has, with
`ε = (-1)^{|i||j|}` and diagrams read bottom to top,

  `x_i τ = ε τ x_i`,  `τ x_j = ε x_j τ`,

the dot staying on the strand of its colour (`slide_left_ne`, `slide_right_ne`). Whiskering by
an old word gives the corresponding identities between the last-pair crossing, the appended
dot and the new last dot (`induction_slide_left_ne`, `induction_slide_right_ne`). Since matrix
multiplication reverses diagram composition, in the affine algebra and at every height of the
extended tower they read

  `c φⱼ(y_i) = ε y_i c`,  `φᵢ(y_j) c = ε c y_j`

with `c` the last-pair crossing of `heightLastCrossing D Sc a i j n`, `y` the new last dot and
`φ` the append map (`heightLastCrossing_slide_left_ne`, `heightLastCrossing_slide_right_ne`).
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
namespace OddMath.QuiverHecke
open SKM (zsign)
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

section Local
variable (i j : I)

variable {i j}

end Local

section Word
variable {i j : I}

end Word

section Affine
variable [Fintype I] {i j : I}

private theorem affineLastDot_mul_single (c : I) {m : ℕ} (t : Word I m)
    (s : Word I (m + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc (appendWord c t)) :
    affineLastDot D Sc c m * FiniteHomMatrix.single (appendWord c t) s f =
      FiniteHomMatrix.single (appendWord c t) s (f ≫ inductionLastDot D Sc c t) := by
  rw [affineLastDot, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective c m h)) _ _
  · simp

private theorem single_mul_affineLastCrossing {n : ℕ} (s : Word I n)
    (r : Word I (n + 1 + 1))
    (f : wordObj D Sc (appendWord i (appendWord j s)) ⟶ wordObj D Sc r) :
    FiniteHomMatrix.single r (appendWord i (appendWord j s)) f * affineLastCrossing D Sc i j n =
    FiniteHomMatrix.single r (appendWord j (appendWord i s))
      (inductionLastCrossing D Sc i j s ≫ f) := by
  rw [affineLastCrossing, Finset.mul_sum, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective j n (appendWord_injective i (n + 1) h.symm))) _ _
  · simp

end Affine

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.CyclotomicAction
open SKM (zsign)
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] (a : I → _root_.Polynomial k) {i j : I}

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The distinct-colour dot slides on two inductions from every height

The functor half of the distinct-colour slides (1.8) of Brundan–Ellis, arXiv:1701.04133v2,
Definition 1.5, at a fixed height. On the two-colour composition corner `T_{ij} = C θ(1)`,
`θ = φᵢ ∘ φⱼ`, of `GlobalHeightCrossing`, signed right multiplication by the new last dot
`y_i` and by the appended dot `φᵢ(y_j)` are superbimodule endomorphisms of parities `|i|` and
`|j|` (`heightTwoColourRightMul`). Along the comparison of `Ind_j ⋙ Ind_i` with `T_{ij} ⊗ -`
the outer dot becomes `y_i` and the inner dot becomes `φᵢ(y_j)`
(`heightTwoColourComparison_dot_outer_app`, `heightTwoColourComparison_dot_inner_app`). The
algebra slides of `GlobalMixedSlideAlgebra` then give, with `ε = (-1)^{|i||j|}` and `ψ` the
crossing, in diagrammatic order,

  `x_i^{out} ψ = ε ψ x_i^{in}`,  `ψ x_j^{out} = ε x_j^{in} ψ`

for the components on every module (`heightInduction_slide_left_ne`,
`heightInduction_slide_right_ne`).
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

section RightMul
variable (i j c : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "C" => heightAlgebra D Sc a (n + 1 + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "GC" => heightParity D Sc a ha (n + 1 + 1)
local notation "θ" => fun r => heightAppend D Sc a i (n + 1) (heightAppend D Sc a j n r)
local notation "T" => heightCompositionCorner D Sc i j a ha n
local notation "d" => D.parity c

/-- Hypotheses on an element `u` for signed right multiplication to be an endomorphism of the
two-colour composition corner: parity `|c|`, the corner is preserved, and `u` supercommutes
with the image of the base algebra. -/
structure TwoColourCornerMulData (u : C) : Prop where
  mem : u ∈ GC d
  corner : ∀ x : C, x * θ 1 = x → (x * u) * θ 1 = x * u
  comm : ∀ {p : ZMod 2} {r : heightAlgebra D Sc a n}, r ∈ GA p →
    θ r * u = koszulSign p d • (u * θ r)

variable {i j c a ha n} in
private theorem twoColourCornerMul_mem {u : C} (hu : TwoColourCornerMulData D Sc i j c a ha n u)
    (x : C) (hx : x ∈ heightCompositionCornerSubmodule D Sc i j a n) :
    x * u ∈ heightCompositionCornerSubmodule D Sc i j a n :=
  hu.corner x hx

/-- Parity sign followed by right multiplication by `u`. -/
def heightTwoColourRightMulLinear {u : C} (hu : TwoColourCornerMulData D Sc i j c a ha n u) :
    (T).toSVec ⟶ (T).toSVec :=
  SVec.ofHom ((T).toSVec.sgn d) ≫
    SVec.restrictHom ((SuperBimodule.regular GC).ract u) (twoColourCornerMul_mem D Sc hu)

theorem heightTwoColourRightMulLinear_parity {u : C}
    (hu : TwoColourCornerMulData D Sc i j c a ha n u) :
    heightTwoColourRightMulLinear D Sc i j c a ha n hu ∈
      SVec.parityHom (T).toSVec (T).toSVec d := by
  change heightTwoColourRightMulLinear D Sc i j c a ha n hu ∈
    parity (R := k) (T).toSVec (T).toSVec d
  unfold heightTwoColourRightMulLinear
  have hd := SVec.restrictHom_mem (hU := heightCompositionCorner_odd_mem D Sc i j a ha n)
    (hU' := heightCompositionCorner_odd_mem D Sc i j a ha n)
    ((SuperBimodule.regular GC).ract_mem d u hu.mem) (twoColourCornerMul_mem D Sc hu)
  have h2 := Supercategory.comp_mem (SVec.sgn_mem (T).toSVec d) hd
  rw [zero_add] at h2
  exact h2

private theorem twoColourRightMul_sgn_action {p : ZMod 2} {f : (T).toSVec ⟶ (T).toSVec}
    (hf : f ∈ SVec.parityHom (T).toSVec (T).toSVec p) (x : (T).toSVec) :
    (T).toSVec.sgn d (f x) = sign k (p * d) • f ((T).toSVec.sgn d x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf d) x

theorem heightTwoColourRightMulLinear_isHom {u : C}
    (hu : TwoColourCornerMulData D Sc i j c a ha n u) :
    SuperBimodule.IsHom T T (heightTwoColourRightMulLinear D Sc i j c a ha n hu) := by
  apply (SuperBimodule.isHom_iff_of_mem
    (heightTwoColourRightMulLinear_parity D Sc i j c a ha n hu)).2
  constructor
  · intro p b hb
    apply SVec.hom_ext
    intro x
    have h := twoColourRightMul_sgn_action D Sc i j c a ha n ((T).lact_mem p b hb) x
    apply Subtype.ext
    change ((T).toSVec.sgn d ((T).lact b x)).val * u =
      sign k (p * d) • (b * (((T).toSVec.sgn d x).val * u))
    rw [h]
    change (sign k (p * d) • (b * ((T).toSVec.sgn d x).val)) * u = _
    rw [smul_mul_assoc, mul_assoc]
  · intro r
    induction r using SuperBimodule.alg_induction_on GA with
    | zero => simp
    | add r s hr hs => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hr, hs]
    | hom p r hr =>
      apply SVec.hom_ext
      intro x
      have h := twoColourRightMul_sgn_action D Sc i j c a ha n ((T).ract_mem p r hr) x
      apply Subtype.ext
      change ((T).toSVec.sgn d ((T).ract r x)).val * u =
        (((T).toSVec.sgn d x).val * u) *
          heightAppend D Sc a i (n + 1) (heightAppend D Sc a j n r)
      rw [h]
      change (sign k (p * d) • (((T).toSVec.sgn d x).val *
        heightAppend D Sc a i (n + 1) (heightAppend D Sc a j n r))) * u = _
      rw [smul_mul_assoc, mul_assoc, hu.comm hr,
        mul_smul_comm, Supercategory.sign_mul, Int.cast_smul_eq_zsmul, koszulSign_smul_smul,
        mul_assoc]

/-- **Signed right multiplication** as a homogeneous endomorphism of the two-colour corner. -/
def heightTwoColourRightMul {u : C} (hu : TwoColourCornerMulData D Sc i j c a ha n u) : T ⟶ T :=
  ⟨heightTwoColourRightMulLinear D Sc i j c a ha n hu,
    heightTwoColourRightMulLinear_isHom D Sc i j c a ha n hu⟩

/-- The new last dot `y_i` satisfies the corner hypotheses. -/
theorem twoColourCornerMulData_lastDot :
    TwoColourCornerMulData D Sc i j i a ha n (heightLastDot D Sc a i (n + 1)) where
  mem := heightLastDot_parity D Sc a i ha (n + 1)
  corner x hx := by
    have h := heightLastDot_comm D Sc a i ha (n + 1)
      (heightAppend_parity D Sc a ha j n (SetLike.one_mem_graded GA))
    rw [koszulSign_zero_left, one_smul] at h
    rw [mul_assoc, ← h, ← mul_assoc, hx]
  comm hr := heightLastDot_comm D Sc a i ha (n + 1) (heightAppend_parity D Sc a ha j n hr)

/-- The appended dot `φᵢ(y_j)` satisfies the corner hypotheses. -/
theorem twoColourCornerMulData_appendDot :
    TwoColourCornerMulData D Sc i j j a ha n
      (heightAppend D Sc a i (n + 1) (heightLastDot D Sc a j n)) where
  mem := heightAppend_parity D Sc a ha i (n + 1) (heightLastDot_parity D Sc a j ha n)
  corner x _ := by
    rw [mul_assoc, ← map_mul, (heightLastDot_corner D Sc a j n).2]
  comm {p} {r} hr := by
    rw [← map_mul, heightLastDot_comm D Sc a j ha n hr, map_zsmul, map_mul]

end RightMul

/-! ### The slides on the corners -/

section CornerSlides
variable {i j : I} (hij : i ≠ j) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)
include hij

local notation "d" => D.parity i * D.parity j
local notation "ε" => koszulSign (D.parity i) (D.parity j)
local notation "Cr" => heightCompositionSuperCrossing D Sc i j a ha n
local notation "Dr" => heightTwoColourRightMul D Sc i j i a ha n
  (twoColourCornerMulData_lastDot D Sc i j a ha n)
local notation "Dl" => heightTwoColourRightMul D Sc j i i a ha n
  (twoColourCornerMulData_appendDot D Sc j i a ha n)
local notation "Er" => heightTwoColourRightMul D Sc j i j a ha n
  (twoColourCornerMulData_lastDot D Sc j i a ha n)
local notation "El" => heightTwoColourRightMul D Sc i j j a ha n
  (twoColourCornerMulData_appendDot D Sc i j a ha n)

end CornerSlides

/-! ### Transport along the comparison -/

section Transport
variable (i j : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "T" => heightCompositionCorner D Sc i j a ha n
local notation "Pc" => heightInductionCorner D Sc i a ha (n + 1)
local notation "Qc" => heightInductionCorner D Sc j a ha n
local notation "iso" => heightInductionCompositionIso D Sc i j a ha n
local notation "Dr" => heightTwoColourRightMul D Sc i j i a ha n
  (twoColourCornerMulData_lastDot D Sc i j a ha n)
local notation "Dl" => heightTwoColourRightMul D Sc i j j a ha n
  (twoColourCornerMulData_appendDot D Sc i j a ha n)

/-- The comparison component of `Ind_j ⋙ Ind_i`, written on tensor products. -/
def heightTwoColourComparisonHom (M : HeightModules D Sc a ha n) :
    tensor Pc (tensor Qc M) ⟶ tensor T M :=
  (assoc Pc Qc M).inv ≫ whiskerRight (iso).hom M

/-- Its inverse, written on tensor products. -/
def heightTwoColourComparisonInv (M : HeightModules D Sc a ha n) :
    tensor T M ⟶ tensor Pc (tensor Qc M) :=
  whiskerRight (iso).inv M ≫ (assoc Pc Qc M).hom

end Transport

/-! ### The slides on the induction functors -/

section InductionSlides
variable {i j : I} (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "Hij" => heightTwoColourComparisonHom D Sc i j a ha n
local notation "Hji" => heightTwoColourComparisonHom D Sc j i a ha n
local notation "Iji" => heightTwoColourComparisonInv D Sc j i a ha n
local notation "Tij" => heightCompositionCorner D Sc i j a ha n
local notation "Tji" => heightCompositionCorner D Sc j i a ha n

end InductionSlides

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The distinct-colour quadratic relation on two inductions from every height

The algebra half of the quadratic relations (1.7) of Brundan–Ellis, arXiv:1701.04133v2,
Definition 1.5, for distinct colours, at every height of the extended tower. On the words
`w j i`, the square of the last-pair crossing is the explicit two-colour polynomial
`Q_{ji}` (`affineLastCrossing_mixed`). Writing `A = φᵢ(y_j)` for the appended dot,
`B = y_i` for the new last dot and `e = φᵢφⱼ(1)` for the two-colour idempotent,

  `c_{ij} c_{ji} = e · Q_{ji}(A, B)`

in the affine algebra (`affineLastCrossing_mul_mixed`) and at every height
(`heightLastCrossing_mul_mixed`), where `Q_{ji}(A, B) = t_{ji} 1` if `d_{ji} = 0` and otherwise

  `Q_{ji}(A, B) = ∑_{0<p<d_{ji}, 0<q<d_{ij}} s_{ji}^{pq} A^p B^q + t_{ji} A^{d_{ji}} + t_{ij} B^{d_{ij}}`.

This is an identity of algebra elements; no parameter change is made here.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- The explicit two-colour quadratic polynomial in two elements of a `k`-algebra. -/
def pairQuadPoly {R : Type*} [Ring R] [Algebra k R] (i j : I) (A B : R) : R :=
  if D.d i j = 0 then (Sc.t i j : k) • 1 else
    ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
      Sc.s i j p q • (A ^ p * B ^ q) +
      ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i)

variable [Fintype I]

section PairDiag
variable (i j : I) (n : ℕ)

variable {i j n}

variable (i j n)

private abbrev pairB (w : Word I n) : End (wordObj D Sc (appendWord i (appendWord j w))) :=
  dotE D Sc (appendWord i (appendWord j w)).1 (w.1.length + 1)

variable {i j}

end PairDiag

section Height
open CyclotomicAction
variable (a : I → _root_.Polynomial k) {i j : I}

end Height

end OddMath.QuiverHecke
end

end

section

/-!
# The distinct-colour quadratic relation on the two-colour composition corners

The corner half of the quadratic relations (1.7) of Brundan–Ellis, arXiv:1701.04133v2,
Definition 1.5, for distinct colours, at a fixed height of the extended tower. On the corner
`T_{ij} = C θ(1)`, `θ = φᵢ ∘ φⱼ`, write `x_out` for signed right multiplication by the new last
dot `y_i` and `x_in` for signed right multiplication by the appended dot `φᵢ(y_j)`
(`heightTwoColourRightMul`). An `m`-fold power of signed right multiplication by a dot of
parity `c` acts on an element of parity `p` by the sign `(-1)^{c(mp + ⌊m/2⌋)}`
(`heightTwoColourRightMul_pow_apply`). With the algebra identity
`heightLastCrossing_mul_mixed`, the composite of the two corner crossings is, in diagrammatic
order,

  `ψ_{ij} ψ_{ji} = t'_{ij} x_out^{d_{ij}} + t'_{ji} x_in^{d_{ji}}
      + ∑_{0<p<d_{ij}, 0<q<d_{ji}} s'^{pq}_{ij} x_in^q x_out^p`

(`heightCompositionCorner_square_ne`), and `ψ_{ij} ψ_{ji} = t'_{ij}` if `d_{ij} = 0`
(`heightCompositionCorner_square_zero`), where `t'`, `s'` are the parameters of
`parameterTwist`. The signs of the odd powers of the crossing parities and of the dots are
exactly the signs recorded by `parameterTwist`: every surviving monomial has `p|i|` and `q|j|`
even (`Sc.s_eq_zero`, `Datum.even_d_of_odd`).
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-! ### Sign bookkeeping -/

theorem parameterSignUnit_coe (p : ZMod 2) :
    ((parameterSignUnit (k := k) p : kˣ) : k) = SKM.zsign k p := by
  unfold parameterSignUnit SKM.zsign
  split_ifs <;> simp

private theorem zmod_two_eq_zero_or_one (p : ZMod 2) : p = 0 ∨ p = 1 := by
  revert p; decide

private theorem zmod_two_mul_self (p : ZMod 2) : p * p = p := by
  rcases zmod_two_eq_zero_or_one p with rfl | rfl <;> decide

omit [Fintype I] in
/-- The twisted distinct-colour leading parameter. -/
theorem parameterTwist_t_of_ne {i j : I} (hij : i ≠ j) :
    (((parameterTwist D Sc).t i j : kˣ) : k) =
      SKM.zsign k (parameterSignExponent D i j (D.dn i j) 0) * (Sc.t i j : k) := by
  simp [parameterTwist, hij, parameterSignUnit_coe]

omit [Fintype I] in
/-- The twisted mixed parameters. -/
theorem parameterTwist_s (i j : I) (p q : ℕ) :
    (parameterTwist D Sc).s i j p q =
      SKM.zsign k (parameterSignExponent D i j p q) * Sc.s i j p q := rfl

omit [Fintype I] in
/-- An odd colour has an even number of dots on every connected strand. -/
theorem dn_cast_mul_parity {i j : I} (hij : i ≠ j) :
    (D.dn i j : ZMod 2) * D.parity i = 0 := by
  rcases zmod_two_eq_zero_or_one (D.parity i) with h | h
  · rw [h, mul_zero]
  · rw [h, mul_one]
    have he : Even (D.dn i j : ℤ) := by
      rw [D.dn_cast hij]
      exact D.even_d_of_odd h j
    exact (ZMod.natCast_eq_zero_iff_even).2 (Int.even_coe_nat _ |>.1 he)

/-! ### Powers of signed right multiplication -/

/-- Vertical powers of an endomorphism, `f^{m+1} = f^m ≫ f` (the recursion of
`SKM.rouquierPower`). -/
def endoPower {𝒞 : Type*} [Category 𝒞] {Y : 𝒞} (f : Y ⟶ Y) : ℕ → (Y ⟶ Y)
  | 0 => 𝟙 Y
  | m + 1 => endoPower f m ≫ f

@[simp] theorem endoPower_zero {𝒞 : Type*} [Category 𝒞] {Y : 𝒞} (f : Y ⟶ Y) :
    endoPower f 0 = 𝟙 Y := rfl

section Power
variable {i j c : I} {a : I → _root_.Polynomial k} {ha : CyclotomicPolynomialParity D a}
  {n : ℕ}

local notation "C" => heightAlgebra D Sc a (n + 1 + 1)
local notation "T" => heightCompositionCorner D Sc i j a ha n

end Power

/-! ### The corner square -/

section CornerSquare
variable {i j : I} (hij : i ≠ j) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)
include hij

local notation "T" => heightCompositionCorner D Sc i j a ha n
local notation "Cr" => heightCompositionSuperCrossing D Sc i j a ha n
local notation "Cr'" => heightCompositionSuperCrossing D Sc j i a ha n
local notation "Dr" => heightTwoColourRightMul D Sc i j i a ha n
  (twoColourCornerMulData_lastDot D Sc i j a ha n)
local notation "Dl" => heightTwoColourRightMul D Sc i j j a ha n
  (twoColourCornerMulData_appendDot D Sc i j a ha n)
local notation "A" => heightAppend D Sc a i (n + 1) (heightLastDot D Sc a j n)
local notation "B" => heightLastDot D Sc a i (n + 1)

end CornerSquare

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The crossing on cyclotomic content blocks

Ports the blockwise crossing of
`Categorification/KLR/CyclotomicAction/GlobalCross.lean`. The target content
is supplied explicitly, so the two strand orders land in the same full
supercategory. The underlying crossing is the restriction of
`cyclotomicSuperInductionCrossing`, which is the signed `SuperCrossing`
corner map transported along `inductionFunctorComparison`; no second
crossing is constructed. As in the even file, the Rouquier crossing is
`-ψ` for equal colours and `ψ` otherwise (`globalBlockSignedCross`).
The product over weight blocks and its height-zero boundary are separate.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)
  (i j : I) (n : ℕ) (β δ : Multiset I)

/-- Two inductions land in the sum content, with the displayed strand order. -/
theorem contentSupported_induction₂ (h : {i} + ({j} + β) = δ)
    (M : CyclotomicSupermodules D Sc a ha n) (hM : ContentSupported D Sc a ha n β M) :
    ContentSupported D Sc a ha (n + 1 + 1) δ
      ((cyclotomicSuperInduction D Sc i a ha (n + 1)).obj
        ((cyclotomicSuperInduction D Sc j a ha n).obj M)) := by
  subst h
  exact contentSupported_induction D Sc a ha i (n + 1) _ _
    (contentSupported_induction D Sc a ha j n β M hM)

/-- Two successive inductions with an explicitly chosen common target content. -/
def globalBlockInduction₂ (h : {i} + ({j} + β) = δ) :
    Superfunctor k (CyclotomicContentModules D Sc a ha n β)
      (CyclotomicContentModules D Sc a ha (n + 1 + 1) δ) :=
  fullLiftSuperfunctor _ _
    ⟨cyclotomicSuperInduction D Sc j a ha n ⋙ cyclotomicSuperInduction D Sc i a ha (n + 1)⟩
    (contentSupported_induction₂ D Sc a ha i j n β δ h)

omit [Fintype I] in
/-- The two orders have the same target content. -/
theorem swapped_content (h : {i} + ({j} + β) = δ) : {j} + ({i} + β) = δ :=
  (add_left_comm _ _ _).trans h

/-- The constructed homogeneous crossing `ψ`, restricted to content blocks. -/
def globalBlockCross (h : {i} + ({j} + β) = δ) :
    globalBlockInduction₂ D Sc a ha i j n β δ h ⟶
      globalBlockInduction₂ D Sc a ha j i n β δ (swapped_content i j β δ h) :=
  fullLiftTrans _ _
    (contentSupported_induction₂ D Sc a ha i j n β δ h)
    (contentSupported_induction₂ D Sc a ha j i n β δ (swapped_content i j β δ h))
    (cyclotomicSuperInductionCrossing D Sc i j a ha n)

/-- Forgetting content gives the existing crossing component, with no extra sign. -/
@[simp] theorem globalBlockCross_app (h : {i} + ({j} + β) = δ) (p : ZMod 2)
    (M : CyclotomicContentModules D Sc a ha n β) :
    ((globalBlockCross D Sc a ha i j n β δ h).app p M).hom =
      (cyclotomicSuperInductionCrossing D Sc i j a ha n).app p M.obj := rfl

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The crossing on content blocks at every height

Ports the block crossing of `Categorification/KLR/CyclotomicAction/GlobalCross.lean`
(`globalCross`, `globalCross_sq`) to every height of the extended tower,
including two inductions from the empty word. The square-zero relation of
`Square` holds for `heightLastCrossing` (at two strands it is the image of
`affineLastCrossing_square`), hence for the corner crossing and for
`heightSuperInductionCrossing`. On content blocks with an explicit common
target content, the restricted crossing `heightBlockCross` has parity
`|i||j|` and the same-colour crossing squares to zero.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)
  (i j : I) (n : ℕ)

variable (β δ : Multiset I)

/-- Two inductions land in the sum content at every height. -/
theorem heightContentSupported_induction₂ (h : {i} + ({j} + β) = δ)
    (M : HeightModules D Sc a ha n) (hM : heightContentSupported D Sc a ha n β M) :
    heightContentSupported D Sc a ha (n + 1 + 1) δ
      ((heightSuperInduction D Sc i a ha (n + 1)).obj
        ((heightSuperInduction D Sc j a ha n).obj M)) := by
  subst h
  exact heightContentSupported_induction D Sc i a ha (n + 1) _ _
    (heightContentSupported_induction D Sc j a ha n β M hM)

/-- Two successive inductions with an explicit common target content, at every height. -/
def heightBlockInduction₂ (h : {i} + ({j} + β) = δ) :
    Superfunctor k (ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β))
      (ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha (n + 1 + 1) δ)) :=
  fullLiftSuperfunctor _ _
    ⟨heightSuperInduction D Sc j a ha n ⋙ heightSuperInduction D Sc i a ha (n + 1)⟩
    (heightContentSupported_induction₂ D Sc a ha i j n β δ h)

/-- The homogeneous crossing restricted to content blocks, at every height. -/
def heightBlockCross (h : {i} + ({j} + β) = δ) :
    heightBlockInduction₂ D Sc a ha i j n β δ h ⟶
      heightBlockInduction₂ D Sc a ha j i n β δ (swapped_content i j β δ h) :=
  fullLiftTrans _ _
    (heightContentSupported_induction₂ D Sc a ha i j n β δ h)
    (heightContentSupported_induction₂ D Sc a ha j i n β δ (swapped_content i j β δ h))
    (heightSuperInductionCrossing D Sc i j a ha n)

@[simp] theorem heightBlockCross_app (h : {i} + ({j} + β) = δ) (p : ZMod 2)
    (M : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β)) :
    ((heightBlockCross D Sc a ha i j n β δ h).app p M).hom =
      (heightSuperInductionCrossing D Sc i j a ha n).app p M.obj := rfl

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The equal-colour braid on three inductions at every height

The module half of the same-colour braid relation of
`Categorification/KLR/CyclotomicAction/GlobalBraid.lean` (`globalCross_sameBraid`), at a fixed
height of the extended tower. With `t₁` the crossing of the two inner inductions under the
outer induction and `t₂` the crossing of the two outer inductions,

  `t₂ ≫ t₁ ≫ t₂ = t₁ ≫ t₂ ≫ t₁`

on every module (`heightSuperInduction_braid_same`).

Every element of a balanced tensor `P ⊗ N` with `P` an induction corner is the action of
an algebra element on `e ⊗ N`, with `e` the colour-cut idempotent
(`heightInductionCorner_btmul_eq_lact`), and the idempotent can be moved past the action
of the lower algebra (`heightInductionCorner_btmul_lact`). On `e ⊗ e ⊗ N` the crossing acts
by left multiplication by the last-pair crossing (`heightSuperInductionCrossing_idempotent`);
the braid then follows from `heightLastCrossing_braid_same`, the signs on the two sides
agreeing term by term.
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

section Corner
variable (n : ℕ)

local notation "P" => heightInductionCorner D Sc i a ha n
local notation "e" => heightInductionCornerIdempotent D Sc i a ha n
local notation "φ" => heightAppend D Sc a i n

end Corner

section Crossing
variable (n : ℕ)

local notation "P₀" => heightInductionCorner D Sc i a ha n
local notation "P₁" => heightInductionCorner D Sc i a ha (n + 1)
local notation "e₀" => heightInductionCornerIdempotent D Sc i a ha n
local notation "e₁" => heightInductionCornerIdempotent D Sc i a ha (n + 1)
local notation "d" => D.parity i * D.parity i

end Crossing

section Braid
variable (n : ℕ)

local notation "P₀" => heightInductionCorner D Sc i a ha n
local notation "P₁" => heightInductionCorner D Sc i a ha (n + 1)
local notation "P₂" => heightInductionCorner D Sc i a ha (n + 1 + 1)
local notation "e₀" => heightInductionCornerIdempotent D Sc i a ha n
local notation "e₁" => heightInductionCornerIdempotent D Sc i a ha (n + 1)
local notation "e₂" => heightInductionCornerIdempotent D Sc i a ha (n + 1 + 1)
local notation "d" => D.parity i * D.parity i
local notation "φ₁" => heightAppend D Sc a i (n + 1)
local notation "φ₂" => heightAppend D Sc a i (n + 1 + 1)

end Braid

end OddMath.QuiverHecke.CyclotomicAction
end

end
