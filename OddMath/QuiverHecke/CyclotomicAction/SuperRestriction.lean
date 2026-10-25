/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.SuperInduction

/-!
# Cyclotomic restriction on supermodules

Ports the restriction-functor construction of
`Categorification/KLR/CyclotomicAction/Restriction.lean`. Restriction is
represented by the colour-cut `(A,B)`-superbimodule `φ(1) B`, using the
balanced super tensor product. No unsigned odd naturality is assumed.
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

/-- The colour-cut right ideal `φ(1) B`. -/
def restrictionCornerSubmodule : Submodule k B where
  carrier := {x | φ 1 * x = x}
  zero_mem' := mul_zero _
  add_mem' hx hy := by dsimp at *; rw [mul_add, hx, hy]
  smul_mem' c x hx := by dsimp at *; rw [mul_smul_comm, hx]

theorem restrictionCorner_odd_mem (x : B) (hx : x ∈ restrictionCornerSubmodule D Sc i a n) :
    (V).odd x ∈ restrictionCornerSubmodule D Sc i a n := by
  have he := (reg).lact_mem 0 (φ 1)
    (cyclotomicAppend_parity D Sc i a ha n (SetLike.one_mem_graded GA))
  have h := SVec.apply_proj_of_mem he 1 x
  change φ 1 * (V).proj 1 x = (V).proj (1 + 0) (φ 1 * x) at h
  change φ 1 * x = x at hx
  change φ 1 * SuperBimodule.algProj GB 1 x = SuperBimodule.algProj GB 1 x
  simpa only [add_zero, SuperBimodule.regularSVec_proj, hx] using h

/-- The inherited parity on the restriction corner. -/
def restrictionCornerSpace : SVec k :=
  SVec.sub V (restrictionCornerSubmodule D Sc i a n) (restrictionCorner_odd_mem D Sc i a ha n)

theorem restrictionCorner_left_mem (r : A) (x : B) :
    φ r * x ∈ restrictionCornerSubmodule D Sc i a n := by
  change φ 1 * (φ r * x) = φ r * x
  rw [← mul_assoc, ← map_mul, one_mul]

theorem restrictionCorner_right_mem (b x : B)
    (hx : x ∈ restrictionCornerSubmodule D Sc i a n) :
    x * b ∈ restrictionCornerSubmodule D Sc i a n := by
  change φ 1 * (x * b) = x * b
  rw [← mul_assoc, hx]

/-- The actual `(A,B)`-superbimodule representing cyclotomic restriction. -/
def restrictionCorner : SuperBimodule GA GB where
  toSVec := restrictionCornerSpace D Sc i a ha n
  lact :=
    { toFun := fun r => SVec.restrictHom ((reg).lact (φ r))
        (fun x _ => restrictionCorner_left_mem D Sc i a n r x)
      map_add' := by
        intro r s
        apply SVec.hom_ext
        intro x
        apply Subtype.ext
        change φ (r + s) * x.1 = φ r * x.1 + φ s * x.1
        rw [map_add, add_mul]
      map_smul' := by
        intro c r
        apply SVec.hom_ext
        intro x
        apply Subtype.ext
        change φ (c • r) * x.1 = c • (φ r * x.1)
        rw [map_smul, smul_mul_assoc] }
  ract :=
    { toFun := fun b => SVec.restrictHom ((reg).ract b)
        (restrictionCorner_right_mem D Sc i a n b)
      map_add' := by
        intro b c
        apply SVec.hom_ext
        intro x
        apply Subtype.ext
        exact mul_add x.1 b c
      map_smul' := by
        intro c b
        apply SVec.hom_ext
        intro x
        apply Subtype.ext
        exact mul_smul_comm c x.1 b }
  lact_one := by
    apply SVec.hom_ext
    intro x
    apply Subtype.ext
    exact x.2
  lact_mul r s := by
    apply SVec.hom_ext
    intro x
    apply Subtype.ext
    change φ (r * s) * x.1 = φ r * (φ s * x.1)
    rw [map_mul, mul_assoc]
  ract_one := by
    apply SVec.hom_ext
    intro x
    apply Subtype.ext
    exact mul_one x.1
  ract_mul b c := by
    apply SVec.hom_ext
    intro x
    apply Subtype.ext
    exact (mul_assoc x.1 b c).symm
  lact_ract r b := by
    apply SVec.hom_ext
    intro x
    apply Subtype.ext
    exact mul_assoc (φ r) x.1 b
  lact_mem p r hr := SVec.restrictHom_mem
    ((reg).lact_mem p (φ r) (cyclotomicAppend_parity D Sc i a ha n hr))
    (fun x _ => restrictionCorner_left_mem D Sc i a n r x)
  ract_mem p b hb := SVec.restrictHom_mem ((reg).ract_mem p b hb)
    (restrictionCorner_right_mem D Sc i a n b)

/-- Balanced-tensor restriction on the genuine module supercategories. -/
def cyclotomicSuperRestriction :
    CyclotomicSupermodules D Sc a ha (n + 1) ⥤ CyclotomicSupermodules D Sc a ha n where
  obj M := SuperBimodule.tensor (restrictionCorner D Sc i a ha n) M
  map f := SuperBimodule.whiskerLeft (restrictionCorner D Sc i a ha n) f
  map_id M := SuperBimodule.whiskerLeft_id _ M
  map_comp f g := SuperBimodule.whiskerLeft_comp _ f g

instance cyclotomicSuperRestriction_additive : (cyclotomicSuperRestriction D Sc i a ha n).Additive where
  map_add := by intros; apply SuperBimodule.whiskerLeft_add

instance cyclotomicSuperRestriction_linear : (cyclotomicSuperRestriction D Sc i a ha n).Linear k where
  map_smul := by intros; apply SuperBimodule.whiskerLeft_smul

instance cyclotomicSuperRestriction_super :
    Supercategory.IsSuperfunctor k (cyclotomicSuperRestriction D Sc i a ha n) where
  map_mem := fun hf => SuperBimodule.whiskerLeft_mem _ _ hf

end OddMath.QuiverHecke
