/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeight

/-!
# Induction including the empty-content boundary

Ports the all-height induction used by
`Categorification/KLR/CyclotomicAction/Global.lean`. The construction uses the
same balanced colour-cut superbimodule as `SuperInduction`, with
`heightAppend` in place of its positive-height specialization. The equality
`heightSuperInduction_succ` identifies the two constructions, while height
zero uses the vacuum map without changing the signed tensor product.
-/

noncomputable section
open CategoryTheory StringDiagrams
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

/-- The colour-cut left ideal `B φ(1)`. -/
def heightInductionCornerSubmodule : Submodule k B where
  carrier := {x | x * φ 1 = x}
  zero_mem' := zero_mul _
  add_mem' hx hy := by dsimp at *; rw [add_mul, hx, hy]
  smul_mem' c x hx := by dsimp at *; rw [smul_mul_assoc, hx]

theorem heightInductionCorner_odd_mem (x : B) (hx : x ∈ heightInductionCornerSubmodule D Sc i a n) :
    (V).odd x ∈ heightInductionCornerSubmodule D Sc i a n := by
  have he := (reg).ract_mem 0 (φ 1)
    (heightAppend_parity D Sc a ha i n (SetLike.one_mem_graded GA))
  have h := SVec.apply_proj_of_mem he 1 x
  change (V).proj 1 x * φ 1 = (V).proj (1 + 0) (x * φ 1) at h
  change x * φ 1 = x at hx
  change SuperBimodule.algProj GB 1 x * φ 1 = SuperBimodule.algProj GB 1 x
  simpa only [add_zero, SuperBimodule.regularSVec_proj, hx] using h

/-- The colour-cut ideal with the inherited parity. -/
def heightInductionCornerSpace : SVec k :=
  SVec.sub V (heightInductionCornerSubmodule D Sc i a n) (heightInductionCorner_odd_mem D Sc i a ha n)

theorem heightInductionCorner_left_mem (b x : B) (hx : x ∈ heightInductionCornerSubmodule D Sc i a n) :
    b * x ∈ heightInductionCornerSubmodule D Sc i a n := by
  change (b * x) * φ 1 = b * x
  rw [mul_assoc, hx]

theorem heightInductionCorner_right_mem (r : A) (x : B) :
    x * φ r ∈ heightInductionCornerSubmodule D Sc i a n := by
  change (x * φ r) * φ 1 = x * φ r
  rw [mul_assoc, ← map_mul, mul_one]

/-- The actual `(B,A)`-superbimodule used by cyclotomic induction. -/
def heightInductionCorner : SuperBimodule GB GA where
  toSVec := heightInductionCornerSpace D Sc i a ha n
  lact :=
    { toFun := fun b => SVec.restrictHom ((reg).lact b) (heightInductionCorner_left_mem D Sc i a n b)
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
        (fun x _ => heightInductionCorner_right_mem D Sc i a n r x)
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
  lact_mem p b hb := SVec.restrictHom_mem ((reg).lact_mem p b hb)
    (heightInductionCorner_left_mem D Sc i a n b)
  ract_mem p r hr := SVec.restrictHom_mem
    ((reg).ract_mem p (φ r) (heightAppend_parity D Sc a ha i n hr))
    (fun x _ => heightInductionCorner_right_mem D Sc i a n r x)

/-- Balanced-tensor induction on the genuine module supercategories. -/
def heightSuperInduction :
    HeightModules D Sc a ha n ⥤ HeightModules D Sc a ha (n + 1) where
  obj M := SuperBimodule.tensor (heightInductionCorner D Sc i a ha n) M
  map f := SuperBimodule.whiskerLeft (heightInductionCorner D Sc i a ha n) f
  map_id M := SuperBimodule.whiskerLeft_id _ M
  map_comp f g := SuperBimodule.whiskerLeft_comp _ f g

instance heightSuperInduction_additive : (heightSuperInduction D Sc i a ha n).Additive where
  map_add := by intros; apply SuperBimodule.whiskerLeft_add

instance heightSuperInduction_linear : (heightSuperInduction D Sc i a ha n).Linear k where
  map_smul := by intros; apply SuperBimodule.whiskerLeft_smul

instance heightSuperInduction_super :
    Supercategory.IsSuperfunctor k (heightSuperInduction D Sc i a ha n) where
  map_mem := fun hf => SuperBimodule.whiskerLeft_mem _ _ hf

/-- At positive height this is the previously defined superinduction functor. -/
theorem heightSuperInduction_succ :
    heightSuperInduction D Sc i a ha (n + 1) =
      cyclotomicSuperInduction D Sc i a ha n := rfl

/-- The empty content projector is the whole empty-word algebra. -/
theorem contentIdempotent_zero : contentIdempotent D Sc 0 0 = 1 := by
  classical
  have h : (Finset.univ : Finset (Word I 0)).filter (fun s => wordContent s = 0) =
      Finset.univ := by
    apply Finset.filter_true_of_mem
    intro s _
    change (s.1 : Multiset I) = 0
    rw [List.length_eq_zero_iff.mp s.2]
    rfl
  unfold contentIdempotent
  rw [h]
  rfl

/-- The first-strand image belongs to the singleton content. -/
theorem vacuumAppend_content :
    cyclotomicContentIdempotent D Sc a 0 {i} * vacuumAppend D Sc i a 1 =
      vacuumAppend D Sc i a 1 := by
  have h := congrArg (cyclotomicMk D Sc a 0)
    (contentIdempotent_appendAlgebra D Sc i 0 0 1)
  simpa only [add_zero, contentIdempotent_zero, one_mul, map_mul] using h

/-- The induction corner at the vacuum is supported on its single colour. -/
theorem heightInductionCorner_vacuum_content
    (x : (heightInductionCorner D Sc i a ha 0).toSVec) :
    (heightInductionCorner D Sc i a ha 0).lact
      (cyclotomicContentIdempotent D Sc a 0 {i}) x = x := by
  apply Subtype.ext
  change cyclotomicContentIdempotent D Sc a 0 {i} * x.1 = x.1
  have hx : x.1 * vacuumAppend D Sc i a 1 = x.1 := x.2
  rw [cyclotomicContentIdempotent_central, ← hx, mul_assoc,
    ← cyclotomicContentIdempotent_central, vacuumAppend_content, hx]

/-- Colour induction preserves content at every height, including the vacuum. -/
theorem heightContentSupported_induction (β : Multiset I)
    (M : HeightModules D Sc a ha n) (hM : heightContentSupported D Sc a ha n β M) :
    heightContentSupported D Sc a ha (n + 1) ({i} + β)
      ((heightSuperInduction D Sc i a ha n).obj M) := by
  cases n with
  | zero =>
    change β = 0 at hM
    subst β
    intro z
    change (SuperBimodule.tensor (heightInductionCorner D Sc i a ha 0) M).lact
      (cyclotomicContentIdempotent D Sc a 0 ({i} + 0)) z = z
    rw [add_zero]
    induction z using SuperBimodule.tensor_induction_on with
    | zero => exact map_zero _
    | add x y hx hy => rw [map_add, hx, hy]
    | btmul x m => rw [SuperBimodule.lact_btmul, heightInductionCorner_vacuum_content]
  | succ n =>
    exact contentSupported_induction D Sc a ha i n β M hM

/-- Superinduction on full support categories, at arbitrary height. -/
def heightContentInduction (β : Multiset I) :
    Superfunctor k
      (ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β))
      (ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha (n + 1) ({i} + β))) :=
  ⟨fullLift (heightContentSupported D Sc a ha n β)
    (heightContentSupported D Sc a ha (n + 1) ({i} + β))
    (heightSuperInduction D Sc i a ha n) (heightContentSupported_induction D Sc i a ha n β)⟩

/-- The induction between the content categories used in global weight spaces. -/
def globalContentInduction (β : Multiset I) :
    Superfunctor k (GlobalContentModules D Sc a ha β)
      (GlobalContentModules D Sc a ha ({i} + β)) := by
  simpa only [GlobalContentModules, Multiset.card_add, Multiset.card_singleton, Nat.add_comm 1]
    using heightContentInduction D Sc i a ha β.card β

end OddMath.QuiverHecke.CyclotomicAction
