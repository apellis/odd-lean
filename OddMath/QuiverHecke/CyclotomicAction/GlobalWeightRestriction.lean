/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalInduction
import OddMath.QuiverHecke.CyclotomicAction.GlobalProduct
import OddMath.QuiverHecke.CyclotomicAction.GlobalRestriction

/-!
# Restriction on the cyclotomic weight spaces

Ports `globalF` of `Categorification/KLR/CyclotomicAction/Global.lean`.
The colour-cut `(A,B)`-superbimodule `φ(1) B` of `SuperRestriction` is formed
for every strand map of the extended tower, so that restriction from one
strand to the empty word uses `vacuumAppend`. At positive height it is
literally the existing construction (`heightSuperRestriction_succ`).
Restriction removes one colour from the content; at height zero the content
condition is the vacuum condition `β = 0`. The weight-space functor is the
product of these blockwise superfunctors along `blockSucc`, so it keeps odd
module morphisms. Its left adjoint is assembled only at positive height
(`GlobalRestriction`); the vacuum unit and counit are not constructed here.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "A" => heightAlgebra D Sc a n
local notation "B" => heightAlgebra D Sc a (n + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "GB" => heightParity D Sc a ha (n + 1)
local notation "φ" => heightAppend D Sc a i n
local notation "V" => SuperBimodule.regularSVec GB
local notation "reg" => SuperBimodule.regular GB

/-- The colour-cut right ideal `φ(1) B`. -/
def heightRestrictionCornerSubmodule : Submodule k B where
  carrier := {x | φ 1 * x = x}
  zero_mem' := mul_zero _
  add_mem' hx hy := by dsimp at *; rw [mul_add, hx, hy]
  smul_mem' c x hx := by dsimp at *; rw [mul_smul_comm, hx]

theorem heightRestrictionCorner_odd_mem (x : B) (hx : x ∈ heightRestrictionCornerSubmodule D Sc i a n) :
    (V).odd x ∈ heightRestrictionCornerSubmodule D Sc i a n := by
  have he := (reg).lact_mem 0 (φ 1)
    (heightAppend_parity D Sc a ha i n (SetLike.one_mem_graded GA))
  have h := SVec.apply_proj_of_mem he 1 x
  change φ 1 * (V).proj 1 x = (V).proj (1 + 0) (φ 1 * x) at h
  change φ 1 * x = x at hx
  change φ 1 * SuperBimodule.algProj GB 1 x = SuperBimodule.algProj GB 1 x
  simpa only [add_zero, SuperBimodule.regularSVec_proj, hx] using h

/-- The inherited parity on the restriction corner. -/
def heightRestrictionCornerSpace : SVec k :=
  SVec.sub V (heightRestrictionCornerSubmodule D Sc i a n) (heightRestrictionCorner_odd_mem D Sc i a ha n)

theorem heightRestrictionCorner_left_mem (r : A) (x : B) :
    φ r * x ∈ heightRestrictionCornerSubmodule D Sc i a n := by
  change φ 1 * (φ r * x) = φ r * x
  rw [← mul_assoc, ← map_mul, one_mul]

theorem heightRestrictionCorner_right_mem (b x : B)
    (hx : x ∈ heightRestrictionCornerSubmodule D Sc i a n) :
    x * b ∈ heightRestrictionCornerSubmodule D Sc i a n := by
  change φ 1 * (x * b) = x * b
  rw [← mul_assoc, hx]

/-- The actual `(A,B)`-superbimodule representing cyclotomic restriction. -/
def heightRestrictionCorner : SuperBimodule GA GB where
  toSVec := heightRestrictionCornerSpace D Sc i a ha n
  lact :=
    { toFun := fun r => SVec.restrictHom ((reg).lact (φ r))
        (fun x _ => heightRestrictionCorner_left_mem D Sc i a n r x)
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
        (heightRestrictionCorner_right_mem D Sc i a n b)
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
    ((reg).lact_mem p (φ r) (heightAppend_parity D Sc a ha i n hr))
    (fun x _ => heightRestrictionCorner_left_mem D Sc i a n r x)
  ract_mem p b hb := SVec.restrictHom_mem ((reg).ract_mem p b hb)
    (heightRestrictionCorner_right_mem D Sc i a n b)

/-- Balanced-tensor restriction at every height, including onto the empty word. -/
def heightSuperRestriction :
    HeightModules D Sc a ha (n + 1) ⥤ HeightModules D Sc a ha n where
  obj M := SuperBimodule.tensor (heightRestrictionCorner D Sc i a ha n) M
  map f := SuperBimodule.whiskerLeft (heightRestrictionCorner D Sc i a ha n) f
  map_id M := SuperBimodule.whiskerLeft_id _ M
  map_comp f g := SuperBimodule.whiskerLeft_comp _ f g

instance heightSuperRestriction_additive : (heightSuperRestriction D Sc i a ha n).Additive where
  map_add := by intros; apply SuperBimodule.whiskerLeft_add

instance heightSuperRestriction_linear : (heightSuperRestriction D Sc i a ha n).Linear k where
  map_smul := by intros; apply SuperBimodule.whiskerLeft_smul

instance heightSuperRestriction_super :
    Supercategory.IsSuperfunctor k (heightSuperRestriction D Sc i a ha n) where
  map_mem := fun hf => SuperBimodule.whiskerLeft_mem _ _ hf

/-- The extended restriction bimodule is the existing one at positive height. -/
theorem heightRestrictionCorner_succ :
    heightRestrictionCorner D Sc i a ha (n + 1) = restrictionCorner D Sc i a ha n := by
  rfl

/-- At positive height this is the previously defined restriction superfunctor. -/
theorem heightSuperRestriction_succ :
    heightSuperRestriction D Sc i a ha (n + 1) = cyclotomicSuperRestriction D Sc i a ha n := by
  let L (P : SuperBimodule (cyclotomicParity D Sc a ha n)
      (cyclotomicParity D Sc a ha (n + 1))) :
      CyclotomicSupermodules D Sc a ha (n + 1) ⥤ CyclotomicSupermodules D Sc a ha n :=
    { obj M := SuperBimodule.tensor P M
      map f := SuperBimodule.whiskerLeft P f
      map_id M := SuperBimodule.whiskerLeft_id P M
      map_comp f g := SuperBimodule.whiskerLeft_comp P f g }
  exact congrArg L (heightRestrictionCorner_succ D Sc i a ha n)

/-- Restriction removes the colour from the content; at height zero only the empty content
remains. The height hypothesis records that `β` has exactly `n` strands. -/
theorem heightContentSupported_restriction (β : Multiset I) (hβ : β.card = n)
    (M : HeightModules D Sc a ha (n + 1))
    (hM : heightContentSupported D Sc a ha (n + 1) (({i} : Multiset I) + β) M) :
    heightContentSupported D Sc a ha n β ((heightSuperRestriction D Sc i a ha n).obj M) := by
  cases n with
  | zero => exact Multiset.card_eq_zero.mp hβ
  | succ n => exact contentSupported_restriction D Sc a ha i n β M hM

/-- Restriction on full support categories, at arbitrary height. -/
def heightContentRestriction (β : Multiset I) (hβ : β.card = n) :
    Superfunctor k
      (ObjectProperty.FullSubcategory
        (heightContentSupported D Sc a ha (n + 1) (({i} : Multiset I) + β)))
      (ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β)) :=
  fullLiftSuperfunctor _ _ ⟨heightSuperRestriction D Sc i a ha n⟩
    (heightContentSupported_restriction D Sc i a ha n β hβ)

/-- Restriction between the content categories of the global weight spaces, `δ = {i} + β`. -/
def globalContentRestriction {β δ : Multiset I} (h : {i} + β = δ) :
    Superfunctor k (GlobalContentModules D Sc a ha δ) (GlobalContentModules D Sc a ha β) :=
  (heightContentCast D Sc a ha (card_of_add i h).symm h.symm).comp
    (heightContentRestriction D Sc i a ha β.card β rfl)

section Weight
variable (Λ : X)

/-- **Restriction on weight spaces** `y ⟶ x` for `x + α_i = y`: on the content `β` of weight
`x` it restricts the `{i} + β` component. -/
def globalF {x y : X} (h : x + D.α i = y) :
    globalWeightSpace D Sc a ha Λ y ⟶ globalWeightSpace D Sc a ha Λ x :=
  ⟨productFunctor (fun δ : WeightBlocks D Λ y => GlobalContentModules D Sc a ha δ.1)
    (blockSucc D Λ i h) (fun β : WeightBlocks D Λ x => GlobalContentModules D Sc a ha β.1)
    fun β => (globalContentRestriction D Sc i a ha (blockSucc_val D Λ i h β).symm).toFunctor⟩

@[simp] theorem globalF_obj {x y : X} (h : x + D.α i = y)
    (M : ∀ δ : WeightBlocks D Λ y, GlobalContentModules D Sc a ha δ.1)
    (β : WeightBlocks D Λ x) :
    (globalF D Sc i a ha Λ h).obj M β =
      (globalContentRestriction D Sc i a ha (blockSucc_val D Λ i h β).symm).obj
        (M (blockSucc D Λ i h β)) := rfl

end Weight

end OddMath.QuiverHecke.CyclotomicAction
