/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.SuperAdjunctionUnit

/-!
# The counit of cyclotomic super induction and restriction

Ports the counit construction of
`Categorification/TwoRep/CyclotomicRouqAdjunction.lean`. Evaluation is the
actual action `(x ⊗ (y ⊗ m)) ↦ (xy)m` on the balanced super tensor products.
-/

noncomputable section
open CategoryTheory StringDiagrams
open SuperBimodule
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "A" => CyclotomicAlgebra D Sc a n
local notation "B" => CyclotomicAlgebra D Sc a (n + 1)
local notation "φ" => cyclotomicAppend D Sc i a n
local notation "P" => inductionCorner D Sc i a ha n
local notation "Q" => restrictionCorner D Sc i a ha n
variable (M : CyclotomicSupermodules D Sc a ha (n + 1))

/-- The inner bilinear action of a fixed induction element. -/
def superCounitInnerBi (x : (P).toSVec) :
    (Q).toSVec →ₗ[k] M.toSVec →ₗ[k] M.toSVec :=
  M.lact.comp (cornerPairingBi D Sc i a ha n x)

theorem superCounitInner_balance (x : (P).toSVec) (y : (Q).toSVec) (b : B) (m : M.toSVec) :
    superCounitInnerBi D Sc i a ha n M x ((Q).ract b y) m =
      superCounitInnerBi D Sc i a ha n M x y (M.lact b m) := by
  change M.lact (x.1 * (y.1 * b)) m = M.lact (x.1 * y.1) (M.lact b m)
  rw [← mul_assoc, M.lact_mul]
  rfl

/-- Balanced evaluation in the inner tensor factor. -/
def superCounitInner (x : (P).toSVec) : (tensor Q M).toSVec →ₗ[k] M.toSVec :=
  tensorLift (superCounitInnerBi D Sc i a ha n M x) (superCounitInner_balance D Sc i a ha n M x)

@[simp] theorem superCounitInner_btmul (x : (P).toSVec) (y : (Q).toSVec) (m : M.toSVec) :
    superCounitInner D Sc i a ha n M x (btmul Q M y m) = M.lact (x.1 * y.1) m :=
  tensorLift_btmul _ _ y m

/-- The bilinear outer evaluation. -/
def superCounitBi : (P).toSVec →ₗ[k] (tensor Q M).toSVec →ₗ[k] M.toSVec where
  toFun := superCounitInner D Sc i a ha n M
  map_add' x y := by
    apply tensor_hom_ext Q M
    intro z m
    change M.lact ((x.1 + y.1) * z.1) m = M.lact (x.1 * z.1) m + M.lact (y.1 * z.1) m
    rw [add_mul, map_add]
    rfl
  map_smul' c x := by
    apply tensor_hom_ext Q M
    intro y m
    change M.lact ((c • x.1) * y.1) m = c • M.lact (x.1 * y.1) m
    rw [smul_mul_assoc, map_smul]
    rfl

theorem superCounit_balance (x : (P).toSVec) (r : A) (z : (tensor Q M).toSVec) :
    superCounitBi D Sc i a ha n M ((P).ract r x) z =
      superCounitBi D Sc i a ha n M x ((tensor Q M).lact r z) := by
  refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
    superCounitBi D Sc i a ha n M ((P).ract r x) z =
      superCounitBi D Sc i a ha n M x ((tensor Q M).lact r z)) z ?_ ?_ ?_
  · simp only [map_zero]
  · intro y m
    change superCounitInner D Sc i a ha n M ((P).ract r x) (btmul Q M y m) =
      superCounitInner D Sc i a ha n M x ((tensor Q M).lact r (btmul Q M y m))
    rw [lact_btmul, superCounitInner_btmul, superCounitInner_btmul]
    change M.lact ((x.1 * φ r) * y.1) m = M.lact (x.1 * (φ r * y.1)) m
    rw [mul_assoc]
  · intro z w hz hw
    simp only [map_add, hz, hw]

/-- The actual linear counit on the doubly balanced tensor. -/
def superCounitLinear : (tensor P (tensor Q M)).toSVec →ₗ[k] M.toSVec :=
  tensorLift (superCounitBi D Sc i a ha n M) (superCounit_balance D Sc i a ha n M)

@[simp] theorem superCounitLinear_btmul (x : (P).toSVec) (z : (tensor Q M).toSVec) :
    superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z) =
      superCounitInner D Sc i a ha n M x z := tensorLift_btmul _ _ x z

@[simp] theorem superCounitLinear_btmul_btmul (x : (P).toSVec) (y : (Q).toSVec) (m : M.toSVec) :
    superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x (btmul Q M y m)) =
      M.lact (x.1 * y.1) m := by rw [superCounitLinear_btmul, superCounitInner_btmul]

theorem superCounitInner_mem {p : ZMod 2} {x : (P).toSVec} (hx : x ∈ (P).toSVec.part p) :
    SVec.ofHom (superCounitInner D Sc i a ha n M x) ∈
      SVec.parityHom (tensor Q M).toSVec M.toSVec p := by
  apply tensor_mem_parity_of_btmul
  intro q r y m hy hm
  change M.lact (x.1 * y.1) m ∈ M.toSVec.part (q + r + p)
  have hxy := SetLike.GradedMul.mul_mem
    ((inductionCorner_mem_part_iff D Sc i a ha n).mp hx)
    ((restrictionCorner_mem_part_iff D Sc i a ha n).mp hy)
  simpa only [add_comm, add_left_comm, add_assoc] using
    SVec.apply_mem_part (M.lact_mem (p + q) (x.1 * y.1) hxy) hm

theorem superCounitLinear_mem :
    SVec.ofHom (superCounitLinear D Sc i a ha n M) ∈
      SVec.parityHom (tensor P (tensor Q M)).toSVec M.toSVec 0 := by
  apply tensor_mem_parity_of_btmul
  intro p q x z hx hz
  change (SVec.ofHom (superCounitInner D Sc i a ha n M x)) z ∈ M.toSVec.part (p + q + 0)
  simpa only [add_zero, add_comm] using
    SVec.apply_mem_part (superCounitInner_mem D Sc i a ha n M hx) hz

theorem superCounitLinear_lact (b : B) (t : (tensor P (tensor Q M)).toSVec) :
    superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b t) =
      M.lact b (superCounitLinear D Sc i a ha n M t) := by
  refine tensor_induction_on (M := P) (N := tensor Q M) («P» := fun t =>
    superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b t) =
      M.lact b (superCounitLinear D Sc i a ha n M t)) t ?_ ?_ ?_
  · simp only [map_zero]
  · intro x z
    refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
      superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b (btmul P (tensor Q M) x z)) =
        M.lact b (superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
    · simp only [btmul_zero_right, map_zero]
    · intro y m
      rw [lact_btmul, superCounitLinear_btmul_btmul, superCounitLinear_btmul_btmul]
      change M.lact ((b * x.1) * y.1) m = M.lact b (M.lact (x.1 * y.1) m)
      rw [mul_assoc, M.lact_mul]
      rfl
    · intro z w hz hw
      simp only [btmul_add_right, map_add, hz, hw]
  · intro z w hz hw
    simp only [map_add, hz, hw]

theorem superCounitLinear_ract (c : k) (t : (tensor P (tensor Q M)).toSVec) :
    superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c t) =
      M.ract c (superCounitLinear D Sc i a ha n M t) := by
  refine tensor_induction_on (M := P) (N := tensor Q M) («P» := fun t =>
    superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c t) =
      M.ract c (superCounitLinear D Sc i a ha n M t)) t ?_ ?_ ?_
  · simp only [map_zero]
  · intro x z
    refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
      superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c (btmul P (tensor Q M) x z)) =
        M.ract c (superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
    · simp only [btmul_zero_right, map_zero]
    · intro y m
      rw [ract_btmul, ract_btmul, superCounitLinear_btmul_btmul, superCounitLinear_btmul_btmul]
      exact (congrArg (fun f : M.toSVec ⟶ M.toSVec => f m) (M.lact_ract (x.1 * y.1) c)).symm
    · intro z w hz hw
      simp only [btmul_add_right, map_add, hz, hw]
  · intro z w hz hw
    simp only [map_add, hz, hw]

/-- The even component of the restriction-induction counit. -/
def superCounitComponent : tensor P (tensor Q M) ⟶ M :=
  ⟨SVec.ofHom (superCounitLinear D Sc i a ha n M), by
    apply (isHom_iff_of_mem (superCounitLinear_mem D Sc i a ha n M)).mpr
    constructor
    · intro p b _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply SVec.hom_ext
      intro t
      exact superCounitLinear_lact D Sc i a ha n M b t
    · intro c
      apply SVec.hom_ext
      intro t
      exact superCounitLinear_ract D Sc i a ha n M c t⟩

theorem superCounitComponent_mem :
    superCounitComponent D Sc i a ha n M ∈ Supercategory.parity (R := k) _ _ 0 :=
  mem_parity_iff.mpr (superCounitLinear_mem D Sc i a ha n M)

/-- Signed naturality of evaluation for a homogeneous module map. -/
theorem superCounitComponent_naturality_of_mem
    {M N : CyclotomicSupermodules D Sc a ha (n + 1)} {s : ZMod 2} (f : M ⟶ N)
    (hf : f ∈ Supercategory.parity (R := k) M N s) :
    whiskerLeft P (whiskerLeft Q f) ≫ superCounitComponent D Sc i a ha n N =
      superCounitComponent D Sc i a ha n M ≫ f := by
  apply SuperBimodule.hom_ext
  apply tensor_hom_ext_homogeneous P (tensor Q M)
  intro p _ x z hx _
  change superCounitLinear D Sc i a ha n N
    ((whiskerLeft P (whiskerLeft Q f)).1 (btmul P (tensor Q M) x z)) =
      f.1 (superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))
  refine tensor_induction_on_homogeneous (M := Q) (N := M) («P» := fun z =>
    superCounitLinear D Sc i a ha n N
      ((whiskerLeft P (whiskerLeft Q f)).1 (btmul P (tensor Q M) x z)) =
        f.1 (superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
  · simp only [btmul_zero_right, map_zero]
  · intro q r y m hy _
    rw [whiskerLeft_btmul P _ (whiskerLeft_mem Q f hf) hx,
      whiskerLeft_btmul Q f hf hy, btmul_smul_right, map_smul, map_smul,
      superCounitLinear_btmul_btmul, superCounitLinear_btmul_btmul]
    have hxy := SetLike.GradedMul.mul_mem
      ((inductionCorner_mem_part_iff D Sc i a ha n).mp hx)
      ((restrictionCorner_mem_part_iff D Sc i a ha n).mp hy)
    have h := congrArg (fun g : M.toSVec ⟶ N.toSVec => g m)
      (((isHom_iff_of_mem (mem_parity_iff.mp hf)).mp f.2).1 (p + q) (x.1 * y.1) hxy)
    change f.1 (M.lact (x.1 * y.1) m) =
      Supercategory.sign k ((p + q) * s) • N.lact (x.1 * y.1) (f.1 m) at h
    rw [h, smul_smul, ← Supercategory.sign_add, ← add_mul]
  · intro z w hz hw
    simp only [btmul_add_right, map_add, hz, hw]

/-- The actual even counit as a natural transformation between superfunctors. -/
def cyclotomicSuperCounit :
    cyclotomicSuperRestriction D Sc i a ha n ⋙ cyclotomicSuperInduction D Sc i a ha n ⟶
      𝟭 (CyclotomicSupermodules D Sc a ha (n + 1)) where
  app M := superCounitComponent D Sc i a ha n M
  naturality {M N} f := by
    change whiskerLeft P (whiskerLeft Q f) ≫ superCounitComponent D Sc i a ha n N =
      superCounitComponent D Sc i a ha n M ≫ f
    refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
    · simp only [whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
    · intro p g hg
      exact superCounitComponent_naturality_of_mem D Sc i a ha n g hg
    · intro f g hf hg
      simp only [whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]

end OddMath.QuiverHecke
