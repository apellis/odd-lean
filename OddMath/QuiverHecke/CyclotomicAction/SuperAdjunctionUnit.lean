/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.CornerPairing

/-!
# The unit of cyclotomic super induction and restriction

Ports the unit construction of
`Categorification/TwoRep/CyclotomicRouqAdjunction.lean` using genuine balanced
super tensor products. Both inserted colour idempotents are even.
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
local notation "ep" => inductionCornerIdempotent D Sc i a ha n
local notation "eq" => restrictionCornerOf D Sc i a ha n 1

/-- The two even colour idempotents give the linear unit. -/
def superUnitLinear (M : CyclotomicSupermodules D Sc a ha n) :
    M.toSVec →ₗ[k] (tensor Q (tensor P M)).toSVec where
  toFun m := btmul Q (tensor P M) eq (btmul P M ep m)
  map_add' x y := by rw [btmul_add_right, btmul_add_right]
  map_smul' c x := by rw [btmul_smul_right, btmul_smul_right]; rfl

@[simp] theorem superUnitLinear_apply (M : CyclotomicSupermodules D Sc a ha n) (m : M.toSVec) :
    superUnitLinear D Sc i a ha n M m = btmul Q (tensor P M) eq (btmul P M ep m) := rfl

theorem restrictionCornerOf_one_mem : eq ∈ (Q).toSVec.part 0 :=
  (restrictionCorner_mem_part_iff D Sc i a ha n).mpr
    (cyclotomicAppend_parity D Sc i a ha n (SetLike.one_mem_graded _))

theorem superUnitLinear_mem (M : CyclotomicSupermodules D Sc a ha n) :
    SVec.ofHom (superUnitLinear D Sc i a ha n M) ∈
      SVec.parityHom M.toSVec (tensor Q (tensor P M)).toSVec 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro p m hm
  change btmul Q (tensor P M) eq (btmul P M ep m) ∈
    (tensor Q (tensor P M)).toSVec.part (p + 0)
  simpa only [zero_add, add_zero] using
    btmul_mem_part Q (tensor P M) (restrictionCornerOf_one_mem D Sc i a ha n)
      (btmul_mem_part P M (inductionCornerIdempotent_mem D Sc i a ha n) hm)

theorem superUnitLinear_lact (M : CyclotomicSupermodules D Sc a ha n) (r : A) (m : M.toSVec) :
    superUnitLinear D Sc i a ha n M (M.lact r m) =
      (tensor Q (tensor P M)).lact r (superUnitLinear D Sc i a ha n M m) := by
  rw [superUnitLinear_apply, superUnitLinear_apply, lact_btmul, ← btmul_ract_lact]
  have he : (P).ract r ep = (P).lact (φ r) ep := by
    apply Subtype.ext
    change φ 1 * φ r = φ r * φ 1
    rw [← map_mul, ← map_mul, one_mul, mul_one]
  rw [he, ← lact_btmul, ← btmul_ract_lact]
  congr 1
  apply Subtype.ext
  change φ 1 * φ r = φ r * φ 1
  rw [← map_mul, ← map_mul, one_mul, mul_one]

/-- The even component of the induction-restriction unit. -/
def superUnitComponent (M : CyclotomicSupermodules D Sc a ha n) : M ⟶ tensor Q (tensor P M) :=
  ⟨SVec.ofHom (superUnitLinear D Sc i a ha n M), by
    apply (isHom_iff_of_mem (superUnitLinear_mem D Sc i a ha n M)).mpr
    constructor
    · intro p r _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply SVec.hom_ext
      intro m
      exact superUnitLinear_lact D Sc i a ha n M r m
    · intro c
      apply SVec.hom_ext
      intro m
      rfl⟩

theorem superUnitComponent_mem (M : CyclotomicSupermodules D Sc a ha n) :
    superUnitComponent D Sc i a ha n M ∈ Supercategory.parity (R := k) _ _ 0 :=
  mem_parity_iff.mpr (superUnitLinear_mem D Sc i a ha n M)

/-- Naturality includes homogeneous odd module maps. -/
theorem superUnitComponent_naturality_of_mem
    {M N : CyclotomicSupermodules D Sc a ha n} {p : ZMod 2} (f : M ⟶ N)
    (hf : f ∈ Supercategory.parity (R := k) M N p) :
    f ≫ superUnitComponent D Sc i a ha n N =
      superUnitComponent D Sc i a ha n M ≫ whiskerLeft Q (whiskerLeft P f) := by
  apply SuperBimodule.hom_ext
  apply SVec.hom_ext
  intro m
  change superUnitLinear D Sc i a ha n N (f.1 m) =
    (whiskerLeft Q (whiskerLeft P f)).1 (superUnitLinear D Sc i a ha n M m)
  rw [superUnitLinear_apply, superUnitLinear_apply,
    whiskerLeft_btmul Q _ (whiskerLeft_mem P f hf) (restrictionCornerOf_one_mem D Sc i a ha n),
    whiskerLeft_btmul P f hf (inductionCornerIdempotent_mem D Sc i a ha n)]
  simp only [zero_mul, Supercategory.sign_zero, one_smul]

/-- The actual even unit as a natural transformation between superfunctors. -/
def cyclotomicSuperUnit : 𝟭 (CyclotomicSupermodules D Sc a ha n) ⟶
    cyclotomicSuperInduction D Sc i a ha n ⋙ cyclotomicSuperRestriction D Sc i a ha n where
  app M := superUnitComponent D Sc i a ha n M
  naturality {M N} f := by
    change f ≫ superUnitComponent D Sc i a ha n N =
      superUnitComponent D Sc i a ha n M ≫ whiskerLeft Q (whiskerLeft P f)
    refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
    · simp only [whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
    · intro p g hg
      exact superUnitComponent_naturality_of_mem D Sc i a ha n g hg
    · intro f g hf hg
      simp only [whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]

end OddMath.QuiverHecke
