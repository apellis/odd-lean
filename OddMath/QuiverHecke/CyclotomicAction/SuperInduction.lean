/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient

/-!
# Cyclotomic induction on supermodules

Ports the induction-functor construction of
`Categorification/KLR/CyclotomicAction/Induction.lean` using the balanced
super tensor product and the actual colour-cut superbimodule.
-/

noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "A" => CyclotomicAlgebra D Sc a n
local notation "B" => CyclotomicAlgebra D Sc a (n + 1)
local notation "GA" => cyclotomicParity D Sc a ha n
local notation "GB" => cyclotomicParity D Sc a ha (n + 1)
local notation "φ" => cyclotomicAppend D Sc i a n
local notation "V" => SuperBimodule.regularSVec GB
local notation "reg" => SuperBimodule.regular GB

/-- The colour-cut left ideal `B φ(1)`. -/
def inductionCornerSubmodule : Submodule k B where
  carrier := {x | x * φ 1 = x}
  zero_mem' := zero_mul _
  add_mem' hx hy := by dsimp at *; rw [add_mul, hx, hy]
  smul_mem' c x hx := by dsimp at *; rw [smul_mul_assoc, hx]

theorem inductionCorner_odd_mem (x : B) (hx : x ∈ inductionCornerSubmodule D Sc i a n) :
    (V).odd x ∈ inductionCornerSubmodule D Sc i a n := by
  have he := (reg).ract_mem 0 (φ 1)
    (cyclotomicAppend_parity D Sc i a ha n (SetLike.one_mem_graded GA))
  have h := SVec.apply_proj_of_mem he 1 x
  change (V).proj 1 x * φ 1 = (V).proj (1 + 0) (x * φ 1) at h
  change x * φ 1 = x at hx
  change SuperBimodule.algProj GB 1 x * φ 1 = SuperBimodule.algProj GB 1 x
  simpa only [add_zero, SuperBimodule.regularSVec_proj, hx] using h

/-- The colour-cut ideal with the inherited parity. -/
def inductionCornerSpace : SVec k :=
  SVec.sub V (inductionCornerSubmodule D Sc i a n) (inductionCorner_odd_mem D Sc i a ha n)

theorem inductionCorner_left_mem (b x : B) (hx : x ∈ inductionCornerSubmodule D Sc i a n) :
    b * x ∈ inductionCornerSubmodule D Sc i a n := by
  change (b * x) * φ 1 = b * x
  rw [mul_assoc, hx]

theorem inductionCorner_right_mem (r : A) (x : B) :
    x * φ r ∈ inductionCornerSubmodule D Sc i a n := by
  change (x * φ r) * φ 1 = x * φ r
  rw [mul_assoc, ← map_mul, mul_one]

/-- The actual `(B,A)`-superbimodule used by cyclotomic induction. -/
def inductionCorner : SuperBimodule GB GA where
  toSVec := inductionCornerSpace D Sc i a ha n
  lact :=
    { toFun := fun b => SVec.restrictHom ((reg).lact b) (inductionCorner_left_mem D Sc i a n b)
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
    { toFun := fun r => SVec.restrictHom ((reg).ract (φ r))
        (fun x _ => inductionCorner_right_mem D Sc i a n r x)
      map_add' := by
        intro r s
        apply SVec.hom_ext
        intro x
        apply Subtype.ext
        change x.1 * φ (r + s) = x.1 * φ r + x.1 * φ s
        rw [map_add, mul_add]
      map_smul' := by
        intro c r
        apply SVec.hom_ext
        intro x
        apply Subtype.ext
        change x.1 * φ (c • r) = c • (x.1 * φ r)
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
    change x.1 * φ (r * s) = (x.1 * φ r) * φ s
    rw [map_mul, mul_assoc]
  lact_ract b r := by
    apply SVec.hom_ext
    intro x
    apply Subtype.ext
    exact mul_assoc b x.1 (φ r)
  lact_mem p b hb := SVec.restrictHom_mem ((reg).lact_mem p b hb) _
  ract_mem p r hr := SVec.restrictHom_mem
    ((reg).ract_mem p (φ r) (cyclotomicAppend_parity D Sc i a ha n hr)) _

/-- Balanced-tensor induction on the genuine module supercategories. -/
def cyclotomicSuperInduction :
    CyclotomicSupermodules D Sc a ha n ⥤ CyclotomicSupermodules D Sc a ha (n + 1) where
  obj M := SuperBimodule.tensor (inductionCorner D Sc i a ha n) M
  map f := SuperBimodule.whiskerLeft (inductionCorner D Sc i a ha n) f
  map_id M := SuperBimodule.whiskerLeft_id _ M
  map_comp f g := SuperBimodule.whiskerLeft_comp _ f g

instance cyclotomicSuperInduction_additive : (cyclotomicSuperInduction D Sc i a ha n).Additive where
  map_add := by intros; apply SuperBimodule.whiskerLeft_add

instance cyclotomicSuperInduction_linear : (cyclotomicSuperInduction D Sc i a ha n).Linear k where
  map_smul := by intros; apply SuperBimodule.whiskerLeft_smul

instance cyclotomicSuperInduction_super :
    Supercategory.IsSuperfunctor k (cyclotomicSuperInduction D Sc i a ha n) where
  map_mem := fun hf => SuperBimodule.whiskerLeft_mem _ _ hf

end OddMath.QuiverHecke
