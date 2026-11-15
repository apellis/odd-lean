import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import OddMath.QuiverHecke.CyclotomicAction.SuperAdjunction
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.SKM.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Categorification.TwoRep.BlockSum

/-!
# Global induction

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Supercategories on cyclotomic content blocks

Ports the block-category part of
`Categorification/KLR/CyclotomicAction/Global.lean`. Full content subcategories
retain the entire even/odd decomposition of morphisms. Their induction is the
restriction of the genuine balanced-tensor superfunctor, not its even shadow.
The odd dot restricts as a supernatural transformation with the same parity.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v w

section Full
variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
  [Preadditive C] [Linear k C] [Supercategory k C] (P : ObjectProperty C)

/-- The full-subcategory wrapper does not change the morphism superspace. -/
def fullHomEquiv (M N : P.FullSubcategory) : (M ⟶ N) ≃ₗ[k] (M.obj ⟶ N.obj) where
  toFun f := f.hom
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Full subcategories inherit the supercategory structure. -/
instance fullSupercategory : Supercategory k P.FullSubcategory where
  parity M N p := (parity (R := k) M.obj N.obj p).comap (fullHomEquiv P M N).toLinearMap
  isInternal M N := by
    have hu : (Set.univ : Set (ZMod 2)) = {0, 1} := by ext p; fin_cases p <;> simp
    apply (DirectSum.isInternal_submodule_iff_isCompl _ (by decide : (0 : ZMod 2) ≠ 1) hu).mpr
    have hc := (isInternal (R := k) M.obj N.obj).isCompl
      (by decide : (0 : ZMod 2) ≠ 1) hu
    simpa only [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm] using
      Submodule.isCompl_map (fullHomEquiv P M N).symm hc
  id_mem M := id_mem M.obj
  comp_mem hf hg := comp_mem hf hg

@[simp] theorem full_mem {M N : P.FullSubcategory} (f : M ⟶ N) (p : ZMod 2) :
    f ∈ parity (R := k) M N p ↔ f.hom ∈ parity (R := k) M.obj N.obj p := Iff.rfl

variable {C' : Type*} [Category C'] [Preadditive C'] [Linear k C'] [Supercategory k C']
  (Q : ObjectProperty C')

/-- A superfunctor preserving an object property restricts to full supercategories. -/
def fullLift (F : C ⥤ C') (hF : ∀ M, P M → Q (F.obj M)) :
    P.FullSubcategory ⥤ Q.FullSubcategory where
  obj M := ⟨F.obj M.obj, hF M.obj M.property⟩
  map f := ⟨F.map f.hom⟩
  map_id M := InducedCategory.hom_ext (F.map_id M.obj)
  map_comp f g := InducedCategory.hom_ext (F.map_comp f.hom g.hom)

instance (F : C ⥤ C') (hF : ∀ M, P M → Q (F.obj M)) [F.Additive] :
    (fullLift P Q F hF).Additive where
  map_add := by intros; apply InducedCategory.hom_ext; exact F.map_add

instance (F : C ⥤ C') (hF : ∀ M, P M → Q (F.obj M)) [F.Additive] [F.Linear k] :
    (fullLift P Q F hF).Linear k where
  map_smul f r := InducedCategory.hom_ext (F.map_smul r f.hom)

instance (F : C ⥤ C') (hF : ∀ M, P M → Q (F.obj M))
    [F.Additive] [F.Linear k] [IsSuperfunctor k F] : IsSuperfunctor k (fullLift P Q F hF) where
  map_mem hf := IsSuperfunctor.map_mem (F := F) hf

/-- Restriction of a bundled superfunctor to full supercategories. -/
def fullLiftSuperfunctor (F : Superfunctor k C C') (hF : ∀ M, P M → Q (F.obj M)) :
    Superfunctor k P.FullSubcategory Q.FullSubcategory :=
  ⟨fullLift P Q F.toFunctor hF⟩

/-- Restriction preserves both homogeneous components and their Koszul naturality. -/
def fullLiftTrans {F G : C ⥤ C'} (hF : ∀ M, P M → Q (F.obj M))
    (hG : ∀ M, P M → Q (G.obj M)) (η : SuperNatTrans k F G) :
    SuperNatTrans k (fullLift P Q F hF) (fullLift P Q G hG) where
  app p M := ⟨η.app p M.obj⟩
  app_mem p M := η.app_mem p M.obj
  naturality p _ _ _ f hf := InducedCategory.hom_ext (η.naturality p f.hom hf)

theorem fullLiftTrans_homogeneous {F G : C ⥤ C'} (hF : ∀ M, P M → Q (F.obj M))
    (hG : ∀ M, P M → Q (G.obj M)) (η : SuperNatTrans k F G) {p : ZMod 2}
    (hη : η.IsHomogeneous p) : (fullLiftTrans P Q hF hG η).IsHomogeneous p := by
  intro q hq
  funext M
  exact InducedCategory.hom_ext (congrFun (hη q hq) M.obj)

end Full

universe x
variable {I k : Type u} {X : Type x} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)
  (i : I) (n : ℕ) (β : Multiset I)

instance contentInduction_additive :
    (cyclotomicContentInduction D Sc a ha i n β).Additive where
  map_add := by
    intros
    apply InducedCategory.hom_ext
    exact (cyclotomicSuperInduction D Sc i a ha n).map_add

instance contentInduction_linear :
    (cyclotomicContentInduction D Sc a ha i n β).Linear k where
  map_smul f r := InducedCategory.hom_ext
    ((cyclotomicSuperInduction D Sc i a ha n).map_smul r f.hom)

instance contentInduction_super :
    IsSuperfunctor k (cyclotomicContentInduction D Sc a ha i n β) where
  map_mem := by
    intro M N p f hf
    change f.hom ∈ parity (R := k) M.obj N.obj p at hf
    change (cyclotomicSuperInduction D Sc i a ha n).map f.hom ∈
      parity (R := k) _ _ p
    exact IsSuperfunctor.map_mem (F := cyclotomicSuperInduction D Sc i a ha n) hf

/-- Balanced-tensor induction restricted to its content superspaces. -/
def globalBlockInduction :
    Superfunctor k (CyclotomicContentModules D Sc a ha n β)
      (CyclotomicContentModules D Sc a ha (n + 1) ({i} + β)) :=
  ⟨cyclotomicContentInduction D Sc a ha i n β⟩

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The height-zero boundary of cyclotomic content categories

Ports the all-content indexing used in
`Categorification/KLR/CyclotomicAction/Global.lean`. At positive height the
algebra, parity and module categories are the existing cyclotomic quotients;
at height zero they are the affine empty-word algebra and its supermodules.
The first strand map is `vacuumAppend`; all later maps are `cyclotomicAppend`.
No quotient presentation or crossing is replaced by a parallel construction.
-/

noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k)

/-- The cyclotomic tower including its empty-word algebra. -/
def heightAlgebra : ℕ → Type u
  | 0 => Hn D Sc 0
  | n + 1 => CyclotomicAlgebra D Sc a n

instance (n : ℕ) : Ring (heightAlgebra D Sc a n) := by
  cases n with
  | zero => exact inferInstanceAs (Ring (Hn D Sc 0))
  | succ n => exact inferInstanceAs (Ring (CyclotomicAlgebra D Sc a n))

instance (n : ℕ) : Algebra k (heightAlgebra D Sc a n) := by
  cases n with
  | zero => exact inferInstanceAs (Algebra k (Hn D Sc 0))
  | succ n => exact inferInstanceAs (Algebra k (CyclotomicAlgebra D Sc a n))

variable (ha : CyclotomicPolynomialParity D a)

/-- The grading is the existing affine or quotient grading at each height. -/
def heightParity : (n : ℕ) → ZMod 2 → Submodule k (heightAlgebra D Sc a n)
  | 0 => affineParity D Sc 0
  | n + 1 => cyclotomicParity D Sc a ha n

instance (n : ℕ) : GradedAlgebra (heightParity D Sc a ha n) := by
  cases n with
  | zero => exact inferInstanceAs (GradedAlgebra (affineParity D Sc 0))
  | succ n => exact inferInstanceAs (GradedAlgebra (cyclotomicParity D Sc a ha n))

/-- The module supercategory at an arbitrary height, including zero. -/
abbrev HeightModules (n : ℕ) :=
  SuperBimodule (heightParity D Sc a ha n) (trivialGrading k)

/-- The first strand uses the vacuum inclusion, subsequent strands the quotient inclusion. -/
def heightAppend (i : I) : (n : ℕ) →
    heightAlgebra D Sc a n →ₙₐ[k] heightAlgebra D Sc a (n + 1)
  | 0 => vacuumAppend D Sc i a
  | n + 1 => cyclotomicAppend D Sc i a n

@[simp] theorem heightAppend_zero (i : I) :
    heightAppend D Sc a i 0 = vacuumAppend D Sc i a := rfl

@[simp] theorem heightAppend_succ (i : I) (n : ℕ) :
    heightAppend D Sc a i (n + 1) = cyclotomicAppend D Sc i a n := rfl

/-- Every strand map in the extended tower is even. -/
theorem heightAppend_parity (i : I) (n : ℕ) {p : ZMod 2}
    {x : heightAlgebra D Sc a n} (hx : x ∈ heightParity D Sc a ha n p) :
    heightAppend D Sc a i n x ∈ heightParity D Sc a ha (n + 1) p := by
  cases n with
  | zero => exact vacuumAppend_parity D Sc i a ha hx
  | succ n => exact cyclotomicAppend_parity D Sc i a ha n hx

/-- Content support at positive height, and all empty-word modules at height zero. -/
def heightContentSupported : (n : ℕ) → Multiset I → HeightModules D Sc a ha n → Prop
  | 0, β, _ => β = 0
  | n + 1, β, M => ContentSupported D Sc a ha n β M

/-- The supercategory of a content, now with its correct height including the vacuum. -/
abbrev GlobalContentModules (β : Multiset I) :=
  ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha β.card β)

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

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
  simpa only [add_zero, contentIdempotent_zero, one_mul, map_mul,
    cyclotomicContentIdempotent, vacuumAppend_apply] using h

/-- The induction corner at the vacuum is supported on its single colour. -/
theorem heightInductionCorner_vacuum_content
    (x : (heightInductionCorner D Sc i a ha 0).toSVec) :
    (heightInductionCorner D Sc i a ha 0).lact
      (cyclotomicContentIdempotent D Sc a 0 ({i} + 0)) x = x := by
  rw [add_zero]
  apply Subtype.ext
  let z : CyclotomicAlgebra D Sc a 0 := x.1
  change cyclotomicContentIdempotent D Sc a 0 {i} * z = z
  have hz : z * vacuumAppend D Sc i a 1 = z := x.2
  calc
    _ = z * cyclotomicContentIdempotent D Sc a 0 {i} :=
      cyclotomicContentIdempotent_central D Sc a 0 {i} z
    _ = (z * vacuumAppend D Sc i a 1) * cyclotomicContentIdempotent D Sc a 0 {i} := by
      rw [hz]
    _ = z := by
      rw [mul_assoc, ← cyclotomicContentIdempotent_central, vacuumAppend_content, hz]

/-- Colour induction preserves content at every height, including the vacuum. -/
theorem heightContentSupported_induction (β : Multiset I)
    (M : HeightModules D Sc a ha n) (hM : heightContentSupported D Sc a ha n β M) :
    heightContentSupported D Sc a ha (n + 1) ({i} + β)
      ((heightSuperInduction D Sc i a ha n).obj M) := by
  cases n with
  | zero =>
    change β = 0 at hM
    subst hM
    intro z
    change (SuperBimodule.tensor (heightInductionCorner D Sc i a ha 0) M).lact
      (cyclotomicContentIdempotent D Sc a 0 ({i} + 0)) z = z
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
  fullLiftSuperfunctor _ _ ⟨heightSuperInduction D Sc i a ha n⟩
    (heightContentSupported_induction D Sc i a ha n β)

/-- Identification of full content supercategories along equal heights and contents. -/
def heightContentCast {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m') (hγ : γ = γ') :
    Superfunctor k
      (ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m γ))
      (ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m' γ')) := by
  subst hm
  subst hγ
  exact Superfunctor.id k _

@[simp] theorem heightContentCast_rfl (m : ℕ) (γ : Multiset I) :
    heightContentCast D Sc a ha (rfl : m = m) (rfl : γ = γ) = Superfunctor.id k _ := rfl

omit [Fintype I] in
/-- Adding one colour raises the height by one. -/
theorem card_of_add {β δ : Multiset I} (h : {i} + β = δ) : β.card + 1 = δ.card := by
  subst h
  rw [Multiset.card_add, Multiset.card_singleton, add_comm]

/-- Induction between the content categories of the global weight spaces, `δ = {i} + β`.
At height zero this is the vacuum induction; afterwards it is `cyclotomicSuperInduction`. -/
def globalContentInduction {β δ : Multiset I} (h : {i} + β = δ) :
    Superfunctor k (GlobalContentModules D Sc a ha β) (GlobalContentModules D Sc a ha δ) :=
  (heightContentInduction D Sc i a ha β.card β).comp
    (heightContentCast D Sc a ha (card_of_add i h) h)

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# Content indices for global cyclotomic super actions

Ports the weight and block-successor part of
`Categorification/KLR/CyclotomicAction/Global.lean` and the absent-colour
index lemmas of `Categorification/KLR/CyclotomicAction/GlobalLoc.lean`.
The weight convention is `sum β - Λ`, with induction raising the weight.
These indices include the empty content. They are not yet weight-space
supercategories: the existing cyclotomic supermodule categories are indexed
by positive height, rather than by content. No global functor or local
inversion is asserted in this module.
-/

namespace OddMath.QuiverHecke.CyclotomicAction

universe u v
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) (Λ : X)

/-- The weight of the cyclotomic block with content `β`. -/
def blockWeight (β : Multiset I) : X := (β.map D.α).sum - Λ

@[simp] theorem blockWeight_zero : blockWeight D Λ 0 = -Λ := by
  simp [blockWeight]

@[simp] theorem blockWeight_singleton (i : I) :
    blockWeight D Λ {i} = D.α i - Λ := by
  simp [blockWeight]

theorem blockWeight_cons (i : I) (β : Multiset I) :
    blockWeight D Λ ({i} + β) = blockWeight D Λ β + D.α i := by
  simp only [blockWeight, Multiset.map_add, Multiset.map_singleton,
    Multiset.sum_add, Multiset.sum_singleton]
  abel

/-- Contents contributing to a weight space; distinct contents are retained. -/
abbrev WeightBlocks (x : X) := {β : Multiset I // blockWeight D Λ β = x}

/-- Appending one strand on the set of content blocks. -/
def blockSucc (i : I) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) : WeightBlocks D Λ y :=
  ⟨{i} + β.1, by rw [blockWeight_cons, β.2, h]⟩

@[simp] theorem blockSucc_val (i : I) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) : (blockSucc D Λ i h β).1 = {i} + β.1 := rfl

theorem blockSucc_eq (i : I) {x y : X} {h : x + D.α i = y}
    {β : WeightBlocks D Λ x} {δ : WeightBlocks D Λ y}
    (hβ : blockSucc D Λ i h β = δ) : {i} + β.1 = δ.1 :=
  congrArg Subtype.val hβ

theorem blockSucc_injective (i : I) {x y : X} (h : x + D.α i = y) :
    Function.Injective (blockSucc D Λ i h) := by
  intro β γ e
  exact Subtype.ext (add_left_cancel (congrArg Subtype.val e))

instance (i : I) {x y : X} (h : x + D.α i = y) (δ : WeightBlocks D Λ y) :
    Subsingleton {β : WeightBlocks D Λ x // blockSucc D Λ i h β = δ} :=
  ⟨fun β γ => Subtype.ext (blockSucc_injective D Λ i h (β.2.trans γ.2.symm))⟩

/-- The two orders of adding colours have the same content. -/
theorem blockSucc_comm (i j : I) {x y z t : X}
    (h₁ : x + D.α j = y) (h₂ : y + D.α i = t)
    (h₃ : x + D.α i = z) (h₄ : z + D.α j = t) (β : WeightBlocks D Λ x) :
    blockSucc D Λ i h₂ (blockSucc D Λ j h₁ β) =
      blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β) :=
  Subtype.ext (add_left_comm _ _ _)

/-- Precisely the blocks containing `i` have a predecessor of colour `i`. -/
theorem exists_blockSucc_iff (i : I) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ y) :
    (∃ γ, blockSucc D Λ i h γ = β) ↔ i ∈ β.1 := by
  classical
  constructor
  · rintro ⟨γ, rfl⟩
    simp
  · intro hi
    have hw : blockWeight D Λ (β.1.erase i) + D.α i = x + D.α i := by
      rw [← blockWeight_cons, Multiset.singleton_add, Multiset.cons_erase hi, β.2, h]
    exact ⟨⟨β.1.erase i, add_right_cancel hw⟩,
      Subtype.ext (by simp only [blockSucc_val, Multiset.singleton_add,
        Multiset.cons_erase hi])⟩

end OddMath.QuiverHecke.CyclotomicAction

end

section

/-!
# Products of supercategories for cyclotomic weight spaces

Ports the product-category layer of
`Categorification/KLR/CyclotomicAction/Global.lean`. The product has all
homogeneous components, not just even morphisms. Parity decomposition is
pointwise, with the same two parity indices at every component; no finiteness
of the set of blocks is needed. The construction below does not assert the
uniform nilpotence of a family of dots with unbounded nilpotence exponents.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v w t
variable {k : Type u} [CommRing k] {A : Type t}
  (C : A → Type v) [∀ a, Category.{w} (C a)] [∀ a, Preadditive (C a)]
  [∀ a, Linear k (C a)] [∀ a, Supercategory k (C a)]

/-- A family is homogeneous when all its components have the same parity. -/
def productParity (M N : ∀ a, C a) (p : ZMod 2) : Submodule k (M ⟶ N) where
  carrier := {f | ∀ a, f a ∈ parity (R := k) (M a) (N a) p}
  zero_mem' _ := Submodule.zero_mem _
  add_mem' hf hg a := Submodule.add_mem _ (hf a) (hg a)
  smul_mem' r _ hf a := Submodule.smul_mem _ r (hf a)

/-- Arbitrary products of supercategories have pointwise parity decomposition. -/
instance productSupercategory : Supercategory k (∀ a, C a) where
  parity := productParity C
  isInternal M N := by
    classical
    have hu : (Set.univ : Set (ZMod 2)) = {0, 1} := by ext p; fin_cases p <;> simp
    have hc (a : A) := (isInternal (R := k) (M a) (N a)).isCompl
      (by decide : (0 : ZMod 2) ≠ 1) hu
    apply (DirectSum.isInternal_submodule_iff_isCompl _ (by decide : (0 : ZMod 2) ≠ 1) hu).mpr
    constructor
    · apply Submodule.disjoint_def.mpr
      intro f hf hg
      funext a
      exact Submodule.disjoint_def.mp (hc a).disjoint (f a) (hf a) (hg a)
    · apply Submodule.codisjoint_iff_exists_add_eq.mpr
      intro f
      have hx (a : A) := Submodule.codisjoint_iff_exists_add_eq.mp (hc a).codisjoint (f a)
      choose x hx y hy hxy using hx
      exact ⟨x, hx, y, hy, funext hxy⟩
  id_mem M a := id_mem (M a)
  comp_mem hf hg a := comp_mem (hf a) (hg a)

@[simp] theorem product_mem (M N : ∀ a, C a) (f : M ⟶ N) (p : ZMod 2) :
    f ∈ parity (R := k) M N p ↔ ∀ a, f a ∈ parity (R := k) (M a) (N a) p := Iff.rfl

instance productEval_super (a : A) : IsSuperfunctor k (CategoryTheory.Pi.eval C a) where
  map_mem hf := hf a

/-- Componentwise superfunctors between two products. -/
def productFunctor {B : Type*} (s : B → A) (E : B → Type*) [∀ b, Category (E b)]
    (F : ∀ b, C (s b) ⥤ E b) : (∀ a, C a) ⥤ (∀ b, E b) where
  obj M b := (F b).obj (M (s b))
  map f b := (F b).map (f (s b))
  map_id M := funext fun b => (F b).map_id (M (s b))
  map_comp f g := funext fun b => (F b).map_comp (f (s b)) (g (s b))

section Functor
variable {B : Type*} (s : B → A) (E : B → Type*) [∀ b, Category (E b)]
  [∀ b, Preadditive (E b)] [∀ b, Linear k (E b)] [∀ b, Supercategory k (E b)]
  (F : ∀ b, C (s b) ⥤ E b) [∀ b, (F b).Additive] [∀ b, (F b).Linear k]
  [∀ b, IsSuperfunctor k (F b)]

instance : (productFunctor C s E F).Additive where
  map_add := by intros; exact funext fun b => (F b).map_add

instance : (productFunctor C s E F).Linear k where
  map_smul f r := funext fun b => (F b).map_smul r (f (s b))

instance : IsSuperfunctor k (productFunctor C s E F) where
  map_mem hf b := IsSuperfunctor.map_mem (F := F b) (hf (s b))

end Functor

section Weight
variable {I : Type u} {X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  (Sc : SKM.Scalars D k) [Fintype I] (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (Λ x : X)

/-- The weight space is the product of all content supercategories of this weight,
including the empty content at weight `-Λ`. -/
abbrev globalWeightSpace : SCat.{u, u, u + 1} k :=
  SCat.of k (∀ β : WeightBlocks D Λ x, GlobalContentModules D Sc a ha β.1)

end Weight
end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# Restriction and adjunction on content supercategories

Ports the block restriction and adjunction (`resBlock`, `globalAdj` on one
block) of `Categorification/KLR/CyclotomicAction/Global.lean`. These are the
balanced-tensor functors on full content supercategories, including odd
module morphisms. The restriction corner intertwines the two central content
projectors, so the even unit and counit of `cyclotomicSuperIndResAdjunction`
restrict without modification. Only positive heights are treated here: the
restriction from one strand to the empty word is not constructed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)
  (i : I) (n : ℕ) (β : Multiset I)

/-- On the restriction corner the lower projector equals the upper projector. -/
theorem restrictionCorner_content (x : (restrictionCorner D Sc i a ha n).toSVec) :
    (restrictionCorner D Sc i a ha n).lact
        (cyclotomicContentIdempotent D Sc a n β) x =
      (restrictionCorner D Sc i a ha n).ract
        (cyclotomicContentIdempotent D Sc a (n + 1) (({i} : Multiset I) + β)) x := by
  apply Subtype.ext
  change cyclotomicAppend D Sc i a n (cyclotomicContentIdempotent D Sc a n β) * x.1 =
    x.1 * cyclotomicContentIdempotent D Sc a (n + 1) (({i} : Multiset I) + β)
  have he := cyclotomicContentIdempotent_append D Sc i a n β 1
  rw [mul_one] at he
  rw [← he, mul_assoc, x.2, cyclotomicContentIdempotent_central]

/-- Balanced-tensor restriction removes the selected colour from content. -/
theorem contentSupported_restriction (M : CyclotomicSupermodules D Sc a ha (n + 1))
    (hM : ContentSupported D Sc a ha (n + 1) (({i} : Multiset I) + β) M) :
    ContentSupported D Sc a ha n β ((cyclotomicSuperRestriction D Sc i a ha n).obj M) := by
  intro z
  change (SuperBimodule.tensor (restrictionCorner D Sc i a ha n) M).lact _ z = z
  induction z using SuperBimodule.tensor_induction_on with
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | btmul x m =>
    rw [SuperBimodule.lact_btmul, restrictionCorner_content,
      SuperBimodule.btmul_ract_lact, hM m]

/-- The restriction superfunctor on the two content blocks. -/
def globalBlockRestriction :
    Superfunctor k (CyclotomicContentModules D Sc a ha (n + 1) (({i} : Multiset I) + β))
      (CyclotomicContentModules D Sc a ha n β) :=
  fullLiftSuperfunctor _ _ ⟨cyclotomicSuperRestriction D Sc i a ha n⟩
    (contentSupported_restriction D Sc a ha i n β)

@[simp] theorem globalBlockRestriction_obj
    (M : CyclotomicContentModules D Sc a ha (n + 1) (({i} : Multiset I) + β)) :
    ((globalBlockRestriction D Sc a ha i n β).obj M).obj =
      (cyclotomicSuperRestriction D Sc i a ha n).obj M.obj := rfl

@[simp] theorem globalBlockRestriction_map
    {M N : CyclotomicContentModules D Sc a ha (n + 1) (({i} : Multiset I) + β)} (f : M ⟶ N) :
    ((globalBlockRestriction D Sc a ha i n β).map f).hom =
      (cyclotomicSuperRestriction D Sc i a ha n).map f.hom := rfl

/-- The original even unit, restricted to the source content. -/
def globalBlockUnit : 𝟭 (CyclotomicContentModules D Sc a ha n β) ⟶
    (globalBlockInduction D Sc a ha i n β).toFunctor ⋙
      (globalBlockRestriction D Sc a ha i n β).toFunctor where
  app M := ⟨(cyclotomicSuperUnit D Sc i a ha n).app M.obj⟩
  naturality _ _ f := InducedCategory.hom_ext ((cyclotomicSuperUnit D Sc i a ha n).naturality f.hom)

/-- The original even counit, restricted to the target content. -/
def globalBlockCounit : (globalBlockRestriction D Sc a ha i n β).toFunctor ⋙
    (globalBlockInduction D Sc a ha i n β).toFunctor ⟶
      𝟭 (CyclotomicContentModules D Sc a ha (n + 1) (({i} : Multiset I) + β)) where
  app M := ⟨(cyclotomicSuperCounit D Sc i a ha n).app M.obj⟩
  naturality _ _ f :=
    InducedCategory.hom_ext ((cyclotomicSuperCounit D Sc i a ha n).naturality f.hom)

@[simp] theorem globalBlockUnit_app (M : CyclotomicContentModules D Sc a ha n β) :
    ((globalBlockUnit D Sc a ha i n β).app M).hom =
      (cyclotomicSuperUnit D Sc i a ha n).app M.obj := rfl

@[simp] theorem globalBlockCounit_app
    (M : CyclotomicContentModules D Sc a ha (n + 1) (({i} : Multiset I) + β)) :
    ((globalBlockCounit D Sc a ha i n β).app M).hom =
      (cyclotomicSuperCounit D Sc i a ha n).app M.obj := rfl

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

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
end

end

section

/-!
# The induction-restriction adjunction at every height

Supports the adjunction `globalE ⊣ globalF` of
`Categorification/KLR/CyclotomicAction/Global.lean`. The corner pairing, the
even unit and counit, and the triangle identities of `CornerPairing`,
`SuperAdjunctionUnit`, `SuperAdjunctionCounit` and `SuperAdjunction` use only
that the strand map is a unital, even, multiplicative map of graded algebras.
They are restated here for the strand maps `heightAppend` of the extended
tower, which include `vacuumAppend` from the empty word to one strand. At
positive height the bimodules, and hence all constructions here, are
definitionally the original ones (`heightInductionCorner_succ`,
`heightRestrictionCorner_succ`).
-/

noncomputable section
open CategoryTheory StringDiagrams
open SuperBimodule
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
local notation "P" => heightInductionCorner D Sc i a ha n
local notation "Q" => heightRestrictionCorner D Sc i a ha n

/-! ### From `CornerPairing` -/

/-- Homogeneity in the induction corner is inherited from the algebra. -/
theorem heightInductionCorner_mem_part_iff {p : ZMod 2} {x : (P).toSVec} :
    x ∈ (P).toSVec.part p ↔ x.1 ∈ GB p := by
  change x ∈ (SVec.sub _ _ _).part p ↔ _
  rw [SVec.mem_sub_part_iff, mem_regularSVec_part_iff]

/-- Homogeneity in the restriction corner is inherited from the algebra. -/
theorem heightRestrictionCorner_mem_part_iff {p : ZMod 2} {x : (Q).toSVec} :
    x ∈ (Q).toSVec.part p ↔ x.1 ∈ GB p := by
  change x ∈ (SVec.sub _ _ _).part p ↔ _
  rw [SVec.mem_sub_part_iff, mem_regularSVec_part_iff]

/-- Multiplication of an induction element with a restriction element. -/
def heightCornerPairingBi : (P).toSVec →ₗ[k] (Q).toSVec →ₗ[k] B where
  toFun x :=
    { toFun := fun y => x.1 * y.1
      map_add' := fun y z => mul_add x.1 y.1 z.1
      map_smul' := fun c y => mul_smul_comm c x.1 y.1 }
  map_add' x y := by ext z; exact add_mul x.1 y.1 z.1
  map_smul' c x := by ext y; exact smul_mul_assoc c x.1 y.1

/-- The pairing descends through balancing over the lower cyclotomic algebra. -/
def heightCornerPairingLinear : (tensor P Q).toSVec →ₗ[k] B :=
  tensorLift (heightCornerPairingBi D Sc i a ha n) (fun x r y => mul_assoc x.1 (φ r) y.1)

@[simp] theorem heightCornerPairingLinear_btmul (x : (P).toSVec) (y : (Q).toSVec) :
    heightCornerPairingLinear D Sc i a ha n (btmul P Q x y) = x.1 * y.1 :=
  tensorLift_btmul _ _ x y

/-- The even colour-cut idempotent in the induction bimodule. -/
def heightInductionCornerIdempotent : (P).toSVec :=
  ⟨φ 1, by change φ 1 * φ 1 = φ 1; rw [← map_mul, mul_one]⟩

/-- The lower algebra maps into the restriction bimodule. -/
def heightRestrictionCornerOf : A →ₗ[k] (Q).toSVec where
  toFun r := ⟨φ r, by change φ 1 * φ r = φ r; rw [← map_mul, one_mul]⟩
  map_add' r s := Subtype.ext (map_add φ r s)
  map_smul' c r := Subtype.ext (map_smul φ c r)

theorem heightInductionCornerIdempotent_mem :
    heightInductionCornerIdempotent D Sc i a ha n ∈ (P).toSVec.part 0 :=
  (heightInductionCorner_mem_part_iff D Sc i a ha n).mpr
    (heightAppend_parity D Sc a ha i n (SetLike.one_mem_graded GA))

/-- The linear coevaluation `a ↦ φ(a) ⊗ e`. -/
def heightCornerUnitLinear : A →ₗ[k] (tensor Q P).toSVec where
  toFun r := btmul Q P (heightRestrictionCornerOf D Sc i a ha n r)
    (heightInductionCornerIdempotent D Sc i a ha n)
  map_add' r s := by rw [map_add, btmul_add_left]
  map_smul' c r := by rw [map_smul, btmul_smul_left]; rfl

@[simp] theorem heightCornerUnitLinear_apply (r : A) :
    heightCornerUnitLinear D Sc i a ha n r = btmul Q P (heightRestrictionCornerOf D Sc i a ha n r)
      (heightInductionCornerIdempotent D Sc i a ha n) := rfl

/-- The first elementary triangular identity for the corner pairing. -/
@[simp] theorem heightCornerPairing_right_unit (x : (P).toSVec) :
    heightCornerPairingLinear D Sc i a ha n
      (btmul P Q x (heightRestrictionCornerOf D Sc i a ha n 1)) = x.1 := by
  rw [heightCornerPairingLinear_btmul]
  exact x.2

/-- The second elementary triangular identity for the corner pairing. -/
@[simp] theorem heightCornerPairing_left_unit (y : (Q).toSVec) :
    heightCornerPairingLinear D Sc i a ha n
      (btmul P Q (heightInductionCornerIdempotent D Sc i a ha n) y) = y.1 := by
  rw [heightCornerPairingLinear_btmul]
  exact y.2

/-! ### From `SuperAdjunctionUnit` -/
local notation "ep" => heightInductionCornerIdempotent D Sc i a ha n
local notation "eq" => heightRestrictionCornerOf D Sc i a ha n 1
local notation "F" => heightSuperInduction D Sc i a ha n
local notation "E" => heightSuperRestriction D Sc i a ha n

/-- The two even colour idempotents give the linear unit. -/
def heightSuperUnitLinear (M : HeightModules D Sc a ha n) :
    M.toSVec →ₗ[k] (tensor Q (tensor P M)).toSVec where
  toFun m := btmul Q (tensor P M) eq (btmul P M ep m)
  map_add' x y := by rw [btmul_add_right, btmul_add_right]
  map_smul' c x := by rw [btmul_smul_right, btmul_smul_right]; rfl

@[simp] theorem heightSuperUnitLinear_apply (M : HeightModules D Sc a ha n) (m : M.toSVec) :
    heightSuperUnitLinear D Sc i a ha n M m = btmul Q (tensor P M) eq (btmul P M ep m) := rfl

theorem heightRestrictionCornerOf_one_mem : eq ∈ (Q).toSVec.part 0 :=
  (heightRestrictionCorner_mem_part_iff D Sc i a ha n).mpr
    (heightAppend_parity D Sc a ha i n (SetLike.one_mem_graded _))

theorem heightSuperUnitLinear_mem (M : HeightModules D Sc a ha n) :
    SVec.ofHom (heightSuperUnitLinear D Sc i a ha n M) ∈
      SVec.parityHom M.toSVec (tensor Q (tensor P M)).toSVec 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro p m hm
  change btmul Q (tensor P M) eq (btmul P M ep m) ∈
    (tensor Q (tensor P M)).toSVec.part (p + 0)
  simpa only [zero_add, add_zero] using
    btmul_mem_part Q (tensor P M) (heightRestrictionCornerOf_one_mem D Sc i a ha n)
      (btmul_mem_part P M (heightInductionCornerIdempotent_mem D Sc i a ha n) hm)

theorem heightSuperUnitLinear_lact (M : HeightModules D Sc a ha n) (r : A) (m : M.toSVec) :
    heightSuperUnitLinear D Sc i a ha n M (M.lact r m) =
      (tensor Q (tensor P M)).lact r (heightSuperUnitLinear D Sc i a ha n M m) := by
  rw [heightSuperUnitLinear_apply, heightSuperUnitLinear_apply, lact_btmul, ← btmul_ract_lact]
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
def heightSuperUnitComponent (M : HeightModules D Sc a ha n) : M ⟶ tensor Q (tensor P M) :=
  ⟨SVec.ofHom (heightSuperUnitLinear D Sc i a ha n M), by
    apply (isHom_iff_of_mem (heightSuperUnitLinear_mem D Sc i a ha n M)).mpr
    constructor
    · intro p r _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply SVec.hom_ext
      intro m
      exact heightSuperUnitLinear_lact D Sc i a ha n M r m
    · intro c
      apply SVec.hom_ext
      intro m
      rfl⟩

theorem heightSuperUnitComponent_mem (M : HeightModules D Sc a ha n) :
    heightSuperUnitComponent D Sc i a ha n M ∈ Supercategory.parity (R := k) _ _ 0 :=
  mem_parity_iff.mpr (heightSuperUnitLinear_mem D Sc i a ha n M)

/-- Naturality includes homogeneous odd module maps. -/
theorem heightSuperUnitComponent_naturality_of_mem
    {M N : HeightModules D Sc a ha n} {p : ZMod 2} (f : M ⟶ N)
    (hf : f ∈ Supercategory.parity (R := k) M N p) :
    f ≫ heightSuperUnitComponent D Sc i a ha n N =
      heightSuperUnitComponent D Sc i a ha n M ≫ whiskerLeft Q (whiskerLeft P f) := by
  apply SuperBimodule.hom_ext
  apply SVec.hom_ext
  intro m
  change heightSuperUnitLinear D Sc i a ha n N (f.1 m) =
    (whiskerLeft Q (whiskerLeft P f)).1 (heightSuperUnitLinear D Sc i a ha n M m)
  rw [heightSuperUnitLinear_apply, heightSuperUnitLinear_apply,
    whiskerLeft_btmul Q _ (whiskerLeft_mem P f hf) (heightRestrictionCornerOf_one_mem D Sc i a ha n),
    whiskerLeft_btmul P f hf (heightInductionCornerIdempotent_mem D Sc i a ha n)]
  simp only [zero_mul, Supercategory.sign_zero, one_smul]

/-- The actual even unit as a natural transformation between superfunctors. -/
def heightSuperUnit : 𝟭 (HeightModules D Sc a ha n) ⟶
    heightSuperInduction D Sc i a ha n ⋙ heightSuperRestriction D Sc i a ha n where
  app M := heightSuperUnitComponent D Sc i a ha n M
  naturality {M N} f := by
    change f ≫ heightSuperUnitComponent D Sc i a ha n N =
      heightSuperUnitComponent D Sc i a ha n M ≫ whiskerLeft Q (whiskerLeft P f)
    refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
    · simp only [whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
    · intro p g hg
      exact heightSuperUnitComponent_naturality_of_mem D Sc i a ha n g hg
    · intro f g hf hg
      simp only [whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]

/-! ### From `SuperAdjunctionCounit` -/
section Counit
variable (M : HeightModules D Sc a ha (n + 1))

/-- The inner bilinear action of a fixed induction element. -/
def heightSuperCounitInnerBi (x : (P).toSVec) :
    (Q).toSVec →ₗ[k] M.toSVec →ₗ[k] M.toSVec :=
  M.lact.comp (heightCornerPairingBi D Sc i a ha n x)

theorem heightSuperCounitInner_balance (x : (P).toSVec) (y : (Q).toSVec) (b : B) (m : M.toSVec) :
    heightSuperCounitInnerBi D Sc i a ha n M x ((Q).ract b y) m =
      heightSuperCounitInnerBi D Sc i a ha n M x y (M.lact b m) := by
  change M.lact (x.1 * (y.1 * b)) m = M.lact (x.1 * y.1) (M.lact b m)
  rw [← mul_assoc, M.lact_mul]
  rfl

/-- Balanced evaluation in the inner tensor factor. -/
def heightSuperCounitInner (x : (P).toSVec) : (tensor Q M).toSVec →ₗ[k] M.toSVec :=
  tensorLift (heightSuperCounitInnerBi D Sc i a ha n M x) (heightSuperCounitInner_balance D Sc i a ha n M x)

@[simp] theorem heightSuperCounitInner_btmul (x : (P).toSVec) (y : (Q).toSVec) (m : M.toSVec) :
    heightSuperCounitInner D Sc i a ha n M x (btmul Q M y m) = M.lact (x.1 * y.1) m :=
  tensorLift_btmul _ _ y m

/-- The bilinear outer evaluation. -/
def heightSuperCounitBi : (P).toSVec →ₗ[k] (tensor Q M).toSVec →ₗ[k] M.toSVec where
  toFun := heightSuperCounitInner D Sc i a ha n M
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

theorem heightSuperCounit_balance (x : (P).toSVec) (r : A) (z : (tensor Q M).toSVec) :
    heightSuperCounitBi D Sc i a ha n M ((P).ract r x) z =
      heightSuperCounitBi D Sc i a ha n M x ((tensor Q M).lact r z) := by
  refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
    heightSuperCounitBi D Sc i a ha n M ((P).ract r x) z =
      heightSuperCounitBi D Sc i a ha n M x ((tensor Q M).lact r z)) z ?_ ?_ ?_
  · simp only [map_zero]
  · intro y m
    change heightSuperCounitInner D Sc i a ha n M ((P).ract r x) (btmul Q M y m) =
      heightSuperCounitInner D Sc i a ha n M x ((tensor Q M).lact r (btmul Q M y m))
    rw [lact_btmul, heightSuperCounitInner_btmul, heightSuperCounitInner_btmul]
    change M.lact ((x.1 * φ r) * y.1) m = M.lact (x.1 * (φ r * y.1)) m
    rw [mul_assoc]
  · intro z w hz hw
    simp only [map_add, hz, hw]

/-- The actual linear counit on the doubly balanced tensor. -/
def heightSuperCounitLinear : (tensor P (tensor Q M)).toSVec →ₗ[k] M.toSVec :=
  tensorLift (heightSuperCounitBi D Sc i a ha n M) (heightSuperCounit_balance D Sc i a ha n M)

@[simp] theorem heightSuperCounitLinear_btmul (x : (P).toSVec) (z : (tensor Q M).toSVec) :
    heightSuperCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z) =
      heightSuperCounitInner D Sc i a ha n M x z := tensorLift_btmul _ _ x z

@[simp] theorem heightSuperCounitLinear_btmul_btmul (x : (P).toSVec) (y : (Q).toSVec) (m : M.toSVec) :
    heightSuperCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x (btmul Q M y m)) =
      M.lact (x.1 * y.1) m := by rw [heightSuperCounitLinear_btmul, heightSuperCounitInner_btmul]

theorem heightSuperCounitInner_mem {p : ZMod 2} {x : (P).toSVec} (hx : x ∈ (P).toSVec.part p) :
    SVec.ofHom (heightSuperCounitInner D Sc i a ha n M x) ∈
      SVec.parityHom (tensor Q M).toSVec M.toSVec p := by
  apply tensor_mem_parity_of_btmul
  intro q r y m hy hm
  change M.lact (x.1 * y.1) m ∈ M.toSVec.part (q + r + p)
  have hxy := SetLike.GradedMul.mul_mem
    ((heightInductionCorner_mem_part_iff D Sc i a ha n).mp hx)
    ((heightRestrictionCorner_mem_part_iff D Sc i a ha n).mp hy)
  simpa only [add_comm, add_left_comm, add_assoc] using
    SVec.apply_mem_part (M.lact_mem (p + q) (x.1 * y.1) hxy) hm

theorem heightSuperCounitLinear_mem :
    SVec.ofHom (heightSuperCounitLinear D Sc i a ha n M) ∈
      SVec.parityHom (tensor P (tensor Q M)).toSVec M.toSVec 0 := by
  apply tensor_mem_parity_of_btmul
  intro p q x z hx hz
  change (SVec.ofHom (heightSuperCounitInner D Sc i a ha n M x)) z ∈ M.toSVec.part (p + q + 0)
  simpa only [add_zero, add_comm] using
    SVec.apply_mem_part (heightSuperCounitInner_mem D Sc i a ha n M hx) hz

theorem heightSuperCounitLinear_lact (b : B) (t : (tensor P (tensor Q M)).toSVec) :
    heightSuperCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b t) =
      M.lact b (heightSuperCounitLinear D Sc i a ha n M t) := by
  refine tensor_induction_on (M := P) (N := tensor Q M) («P» := fun t =>
    heightSuperCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b t) =
      M.lact b (heightSuperCounitLinear D Sc i a ha n M t)) t ?_ ?_ ?_
  · simp only [map_zero]
  · intro x z
    refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
      heightSuperCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b (btmul P (tensor Q M) x z)) =
        M.lact b (heightSuperCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
    · simp only [btmul_zero_right, map_zero]
    · intro y m
      rw [lact_btmul, heightSuperCounitLinear_btmul_btmul, heightSuperCounitLinear_btmul_btmul]
      change M.lact ((b * x.1) * y.1) m = M.lact b (M.lact (x.1 * y.1) m)
      rw [mul_assoc, M.lact_mul]
      rfl
    · intro z w hz hw
      simp only [btmul_add_right, map_add, hz, hw]
  · intro z w hz hw
    simp only [map_add, hz, hw]

theorem heightSuperCounitLinear_ract (c : k) (t : (tensor P (tensor Q M)).toSVec) :
    heightSuperCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c t) =
      M.ract c (heightSuperCounitLinear D Sc i a ha n M t) := by
  refine tensor_induction_on (M := P) (N := tensor Q M) («P» := fun t =>
    heightSuperCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c t) =
      M.ract c (heightSuperCounitLinear D Sc i a ha n M t)) t ?_ ?_ ?_
  · simp only [map_zero]
  · intro x z
    refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
      heightSuperCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c (btmul P (tensor Q M) x z)) =
        M.ract c (heightSuperCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
    · simp only [btmul_zero_right, map_zero]
    · intro y m
      rw [ract_btmul, ract_btmul, heightSuperCounitLinear_btmul_btmul, heightSuperCounitLinear_btmul_btmul]
      exact (congrArg (fun f : M.toSVec ⟶ M.toSVec => f m) (M.lact_ract (x.1 * y.1) c)).symm
    · intro z w hz hw
      simp only [btmul_add_right, map_add, hz, hw]
  · intro z w hz hw
    simp only [map_add, hz, hw]

/-- The even component of the restriction-induction counit. -/
def heightSuperCounitComponent : tensor P (tensor Q M) ⟶ M :=
  ⟨SVec.ofHom (heightSuperCounitLinear D Sc i a ha n M), by
    apply (isHom_iff_of_mem (heightSuperCounitLinear_mem D Sc i a ha n M)).mpr
    constructor
    · intro p b _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply SVec.hom_ext
      intro t
      exact heightSuperCounitLinear_lact D Sc i a ha n M b t
    · intro c
      apply SVec.hom_ext
      intro t
      exact heightSuperCounitLinear_ract D Sc i a ha n M c t⟩

theorem heightSuperCounitComponent_mem :
    heightSuperCounitComponent D Sc i a ha n M ∈ Supercategory.parity (R := k) _ _ 0 :=
  mem_parity_iff.mpr (heightSuperCounitLinear_mem D Sc i a ha n M)

/-- Signed naturality of evaluation for a homogeneous module map. -/
theorem heightSuperCounitComponent_naturality_of_mem
    {M N : HeightModules D Sc a ha (n + 1)} {s : ZMod 2} (f : M ⟶ N)
    (hf : f ∈ Supercategory.parity (R := k) M N s) :
    whiskerLeft P (whiskerLeft Q f) ≫ heightSuperCounitComponent D Sc i a ha n N =
      heightSuperCounitComponent D Sc i a ha n M ≫ f := by
  apply SuperBimodule.hom_ext
  apply tensor_hom_ext_homogeneous P (tensor Q M)
  intro p _ x z hx _
  change heightSuperCounitLinear D Sc i a ha n N
    ((whiskerLeft P (whiskerLeft Q f)).1 (btmul P (tensor Q M) x z)) =
      f.1 (heightSuperCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))
  refine tensor_induction_on_homogeneous (M := Q) (N := M) («P» := fun z =>
    heightSuperCounitLinear D Sc i a ha n N
      ((whiskerLeft P (whiskerLeft Q f)).1 (btmul P (tensor Q M) x z)) =
        f.1 (heightSuperCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
  · simp only [btmul_zero_right, map_zero]
  · intro q r y m hy _
    rw [whiskerLeft_btmul P _ (whiskerLeft_mem Q f hf) hx,
      whiskerLeft_btmul Q f hf hy, btmul_smul_right, map_smul, map_smul,
      heightSuperCounitLinear_btmul_btmul, heightSuperCounitLinear_btmul_btmul]
    have hxy := SetLike.GradedMul.mul_mem
      ((heightInductionCorner_mem_part_iff D Sc i a ha n).mp hx)
      ((heightRestrictionCorner_mem_part_iff D Sc i a ha n).mp hy)
    have h := congrArg (fun g : M.toSVec ⟶ N.toSVec => g m)
      (((isHom_iff_of_mem (mem_parity_iff.mp hf)).mp f.2).1 (p + q) (x.1 * y.1) hxy)
    change f.1 (M.lact (x.1 * y.1) m) =
      Supercategory.sign k ((p + q) * s) • N.lact (x.1 * y.1) (f.1 m) at h
    rw [h, smul_smul, ← Supercategory.sign_add, ← add_mul]
  · intro z w hz hw
    simp only [btmul_add_right, map_add, hz, hw]

/-- The actual even counit as a natural transformation between superfunctors. -/
def heightSuperCounit :
    heightSuperRestriction D Sc i a ha n ⋙ heightSuperInduction D Sc i a ha n ⟶
      𝟭 (HeightModules D Sc a ha (n + 1)) where
  app M := heightSuperCounitComponent D Sc i a ha n M
  naturality {M N} f := by
    change whiskerLeft P (whiskerLeft Q f) ≫ heightSuperCounitComponent D Sc i a ha n N =
      heightSuperCounitComponent D Sc i a ha n M ≫ f
    refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
    · simp only [whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
    · intro p g hg
      exact heightSuperCounitComponent_naturality_of_mem D Sc i a ha n g hg
    · intro f g hf hg
      simp only [whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]

end Counit

/-! ### From `SuperAdjunction` -/

theorem heightSuperInduction_triangle (M : HeightModules D Sc a ha n) :
    (F).map ((heightSuperUnit D Sc i a ha n).app M) ≫
      (heightSuperCounit D Sc i a ha n).app ((F).obj M) = 𝟙 ((F).obj M) := by
  apply SuperBimodule.hom_ext
  apply tensor_hom_ext P M
  intro x m
  change heightSuperCounitLinear D Sc i a ha n (tensor P M)
    ((whiskerLeft P (heightSuperUnitComponent D Sc i a ha n M)).1 (btmul P M x m)) = btmul P M x m
  rw [whiskerLeft_btmul_even P _ (heightSuperUnitComponent_mem D Sc i a ha n M)]
  change heightSuperCounitLinear D Sc i a ha n (tensor P M)
    (btmul P (tensor Q (tensor P M)) x
      (btmul Q (tensor P M) (heightRestrictionCornerOf D Sc i a ha n 1)
        (btmul P M (heightInductionCornerIdempotent D Sc i a ha n) m))) = btmul P M x m
  rw [heightSuperCounitLinear_btmul_btmul, lact_btmul]
  congr 1
  apply Subtype.ext
  change (x.1 * φ 1) * φ 1 = x.1
  rw [x.2, x.2]

theorem heightSuperRestriction_triangle (M : HeightModules D Sc a ha (n + 1)) :
    (heightSuperUnit D Sc i a ha n).app ((E).obj M) ≫
      (E).map ((heightSuperCounit D Sc i a ha n).app M) = 𝟙 ((E).obj M) := by
  apply SuperBimodule.hom_ext
  apply tensor_hom_ext Q M
  intro y m
  change (whiskerLeft Q (heightSuperCounitComponent D Sc i a ha n M)).1
    (heightSuperUnitLinear D Sc i a ha n (tensor Q M) (btmul Q M y m)) = btmul Q M y m
  rw [heightSuperUnitLinear_apply,
    whiskerLeft_btmul_even Q _ (heightSuperCounitComponent_mem D Sc i a ha n M)]
  change btmul Q M (heightRestrictionCornerOf D Sc i a ha n 1)
    (heightSuperCounitLinear D Sc i a ha n M
      (btmul P (tensor Q M) (heightInductionCornerIdempotent D Sc i a ha n) (btmul Q M y m))) =
    btmul Q M y m
  rw [heightSuperCounitLinear_btmul_btmul]
  change btmul Q M (heightRestrictionCornerOf D Sc i a ha n 1) (M.lact (φ 1 * y.1) m) = btmul Q M y m
  rw [y.2, ← btmul_ract_lact]
  congr 1
  apply Subtype.ext
  exact y.2

/-! ### Content blocks at every height -/

section Content
variable (β : Multiset I) (hβ : β.card = n)

/-- The even unit at every height, restricted to content blocks. -/
def heightContentUnit : 𝟭 (ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β)) ⟶
    (heightContentInduction D Sc i a ha n β).toFunctor ⋙
      (heightContentRestriction D Sc i a ha n β hβ).toFunctor where
  app M := ⟨(heightSuperUnit D Sc i a ha n).app M.obj⟩
  naturality _ _ f := InducedCategory.hom_ext ((heightSuperUnit D Sc i a ha n).naturality f.hom)

/-- The even counit at every height, restricted to content blocks. -/
def heightContentCounit : (heightContentRestriction D Sc i a ha n β hβ).toFunctor ⋙
    (heightContentInduction D Sc i a ha n β).toFunctor ⟶
      𝟭 (ObjectProperty.FullSubcategory
        (heightContentSupported D Sc a ha (n + 1) (({i} : Multiset I) + β))) where
  app M := ⟨(heightSuperCounit D Sc i a ha n).app M.obj⟩
  naturality _ _ f :=
    InducedCategory.hom_ext ((heightSuperCounit D Sc i a ha n).naturality f.hom)

/-- Induction is left adjoint to restriction on content blocks at every height, including
from the empty word to one strand. -/
def heightContentAdjunction :
    (heightContentInduction D Sc i a ha n β).toFunctor ⊣
      (heightContentRestriction D Sc i a ha n β hβ).toFunctor where
  unit := heightContentUnit D Sc i a ha n β hβ
  counit := heightContentCounit D Sc i a ha n β hβ
  left_triangle_components M :=
    InducedCategory.hom_ext (heightSuperInduction_triangle D Sc i a ha n M.obj)
  right_triangle_components M :=
    InducedCategory.hom_ext (heightSuperRestriction_triangle D Sc i a ha n M.obj)

theorem heightContentUnit_mem
    (M : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β)) :
    (heightContentUnit D Sc i a ha n β hβ).app M ∈ Supercategory.parity (R := k) _ _ 0 :=
  heightSuperUnitComponent_mem D Sc i a ha n M.obj

theorem heightContentCounit_mem (M : ObjectProperty.FullSubcategory
    (heightContentSupported D Sc a ha (n + 1) (({i} : Multiset I) + β))) :
    (heightContentCounit D Sc i a ha n β hβ).app M ∈ Supercategory.parity (R := k) _ _ 0 :=
  heightSuperCounitComponent_mem D Sc i a ha n M.obj

end Content

/-- The identity transports along equal heights and contents are mutually adjoint. -/
def heightContentCastAdjunction {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m') (hγ : γ = γ') :
    (heightContentCast D Sc a ha hm hγ).toFunctor ⊣
      (heightContentCast D Sc a ha hm.symm hγ.symm).toFunctor := by
  subst hm
  subst hγ
  exact Adjunction.id

/-- **Induction is left adjoint to restriction** between global content categories,
`δ = {i} + β`, including from the empty content. -/
def globalContentAdjunction {β δ : Multiset I} (h : {i} + β = δ) :
    (globalContentInduction D Sc i a ha h).toFunctor ⊣
      (globalContentRestriction D Sc i a ha h).toFunctor :=
  (heightContentAdjunction D Sc i a ha β.card β rfl).comp
    (heightContentCastAdjunction D Sc a ha (card_of_add i h) h)

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# Induction on the cyclotomic weight spaces

Ports `globalE` of `Categorification/KLR/CyclotomicAction/Global.lean`. The
even file sums induction over the blocks `β` of weight `x` with
`{i} + β = δ`; there is at most one such block (`blockSucc_injective`). Here
the component at `δ` is `globalContentInduction` of the component at that
block when it exists, and the zero supermodule (the empty biproduct)
otherwise. Every component is a superfunctor, so the weight-space functor
keeps odd module morphisms. The adjunction with `globalF` on weight spaces
needs the vacuum unit and counit, which are not constructed here.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

/-- The zero supermodule over the algebra of height `n`. -/
def zeroSupermodule (n : ℕ) : HeightModules D Sc a ha n where
  toSVec := { carrier := PUnit.{u + 1}, odd := 0, odd_comp_odd := LinearMap.ext fun _ => rfl }
  lact := 0
  ract := 0
  lact_one := SVec.hom_ext fun _ => rfl
  lact_mul _ _ := SVec.hom_ext fun _ => rfl
  ract_one := SVec.hom_ext fun _ => rfl
  ract_mul _ _ := SVec.hom_ext fun _ => rfl
  lact_ract _ _ := SVec.hom_ext fun _ => rfl
  lact_mem _ _ _ := by rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
  ract_mem _ _ _ := by rw [LinearMap.zero_apply]; exact Submodule.zero_mem _

/-- The zero supermodule satisfies the content condition of every content of its height. -/
theorem zeroSupermodule_supported (n : ℕ) (δ : Multiset I) (hδ : δ.card = n) :
    heightContentSupported D Sc a ha n δ (zeroSupermodule D Sc a ha n) := by
  cases n with
  | zero => exact Multiset.card_eq_zero.mp hδ
  | succ n => intro _; rfl

/-- The zero object of a global content supercategory. -/
def globalZero (δ : Multiset I) : GlobalContentModules D Sc a ha δ :=
  ⟨zeroSupermodule D Sc a ha δ.card, zeroSupermodule_supported D Sc a ha δ.card δ rfl⟩

theorem globalZero_isZero (δ : Multiset I) : Limits.IsZero (globalZero D Sc a ha δ) :=
  (Limits.IsZero.iff_id_eq_zero _).mpr
    (InducedCategory.hom_ext (SuperBimodule.hom_ext (SVec.hom_ext fun _ => rfl)))

section ZeroFunctor
variable {C : Type*} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
  (δ : Multiset I)

/-- The constant functor at the zero supermodule. -/
def zeroFunctor : C ⥤ GlobalContentModules D Sc a ha δ :=
  (Functor.const C).obj (globalZero D Sc a ha δ)

instance : (zeroFunctor D Sc a ha (C := C) δ).Additive where
  map_add := (globalZero_isZero D Sc a ha δ).eq_of_src _ _

instance : (zeroFunctor D Sc a ha (C := C) δ).Linear k where
  map_smul _ _ := (globalZero_isZero D Sc a ha δ).eq_of_src _ _

instance : IsSuperfunctor k (zeroFunctor D Sc a ha (C := C) δ) where
  map_mem {_ _ _ f} _ := by
    rw [(globalZero_isZero D Sc a ha δ).eq_of_src ((zeroFunctor D Sc a ha δ).map f) 0]
    exact Submodule.zero_mem _

end ZeroFunctor

section Weight
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The product of the content supercategories of weight `x`. -/
abbrev WeightProduct (x : X) :=
  ∀ β : WeightBlocks D Λ x, GlobalContentModules D Sc a ha β.1

/-- Evaluation at one content block, as a superfunctor. -/
def blockEval (β : WeightBlocks D Λ x) :
    Superfunctor k (WeightProduct D Sc a ha Λ x) (GlobalContentModules D Sc a ha β.1) :=
  ⟨Pi.eval (fun β : WeightBlocks D Λ x => GlobalContentModules D Sc a ha β.1) β⟩

open scoped Classical in
/-- The component of induction at a block `δ` of weight `y`: induction from its unique
predecessor block when it exists, and zero otherwise. -/
def inductionComponent (δ : WeightBlocks D Λ y) :
    Superfunctor k (WeightProduct D Sc a ha Λ x) (GlobalContentModules D Sc a ha δ.1) :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    (blockEval D Sc a ha Λ hδ.choose).comp
      (globalContentInduction D Sc i a ha (blockSucc_eq D Λ i hδ.choose_spec))
  else ⟨zeroFunctor D Sc a ha δ.1⟩

private theorem inductionComponent_choice (β c : WeightBlocks D Λ x)
    (hc : blockSucc D Λ i h c = blockSucc D Λ i h β) :
    (blockEval D Sc a ha Λ c).comp (globalContentInduction D Sc i a ha (blockSucc_eq D Λ i hc)) =
      (blockEval D Sc a ha Λ β).comp
        (globalContentInduction D Sc i a ha (blockSucc_val D Λ i h β).symm) := by
  obtain rfl := blockSucc_injective D Λ i h hc
  rfl

/-- At a successor block the component is induction from the predecessor. -/
theorem inductionComponent_blockSucc (β : WeightBlocks D Λ x) :
    inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β) =
      (blockEval D Sc a ha Λ β).comp
        (globalContentInduction D Sc i a ha (blockSucc_val D Λ i h β).symm) := by
  have hδ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β := ⟨β, rfl⟩
  unfold inductionComponent
  split
  · rename_i hc
    exact inductionComponent_choice D Sc a ha i Λ h β _ hc.choose_spec
  · exact absurd hδ ‹_›

/-- Without a predecessor block the component is zero. -/
theorem inductionComponent_isZero (δ : WeightBlocks D Λ y)
    (hδ : ¬ ∃ β, blockSucc D Λ i h β = δ) (M : WeightProduct D Sc a ha Λ x) :
    Limits.IsZero ((inductionComponent D Sc a ha i Λ h δ).obj M) := by
  unfold inductionComponent
  split
  · exact absurd ‹_› hδ
  · exact globalZero_isZero D Sc a ha δ.1

/-- The underlying functor of induction on weight spaces. -/
def globalEFunctor : WeightProduct D Sc a ha Λ x ⥤ WeightProduct D Sc a ha Λ y :=
  Functor.pi' fun δ => (inductionComponent D Sc a ha i Λ h δ).toFunctor

instance : (globalEFunctor D Sc a ha i Λ h).Additive where
  map_add := funext fun δ => (inductionComponent D Sc a ha i Λ h δ).toFunctor.map_add

instance : (globalEFunctor D Sc a ha i Λ h).Linear k where
  map_smul f r := funext fun δ => (inductionComponent D Sc a ha i Λ h δ).toFunctor.map_smul r f

instance : IsSuperfunctor k (globalEFunctor D Sc a ha i Λ h) where
  map_mem hf δ := IsSuperfunctor.map_mem (F := (inductionComponent D Sc a ha i Λ h δ).toFunctor) hf

/-- **Induction on weight spaces** `x ⟶ y` for `x + α_i = y`. -/
def globalE : globalWeightSpace D Sc a ha Λ x ⟶ globalWeightSpace D Sc a ha Λ y :=
  ⟨globalEFunctor D Sc a ha i Λ h⟩

@[simp] theorem globalE_obj (M : WeightProduct D Sc a ha Λ x) (δ : WeightBlocks D Λ y) :
    (globalE D Sc a ha i Λ h).obj M δ = (inductionComponent D Sc a ha i Λ h δ).obj M := rfl

end Weight

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The induction–restriction adjunction on cyclotomic weight spaces

Ports the adjunction `globalE ⊣ globalF` of
`Categorification/KLR/CyclotomicAction/Global.lean`. At a block `blockSucc β`
the unit and counit are those of `globalContentAdjunction`, transported along
`inductionComponent_blockSucc`; at a block with no predecessor the induced
component is a zero supermodule and the counit is zero. All components are
even, and `globalActionAdjunction` packages the result as an
`SKM.SuperAdjunction` in the `SCat` action target of `ActionSupercategory`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

/-- A superfunctor equality, read on morphisms through the induced object equalities. -/
theorem superfunctor_map_of_eq {C₁ C₂ : Type*} [Category C₁] [Preadditive C₁] [Linear k C₁]
    [Supercategory k C₁] [Category C₂] [Preadditive C₂] [Linear k C₂] [Supercategory k C₂]
    {G G' : Superfunctor k C₁ C₂} (hG : G = G') {M M' : C₁} (f : M ⟶ M') :
    G.map f = eqToHom (by rw [hG]) ≫ G'.map f ≫ eqToHom (by rw [hG]) := by
  subst hG
  simp

theorem eqToHom_mem_parity_zero {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {M N : C} (e : M = N) : eqToHom e ∈ parity (R := k) M N 0 := by
  subst e
  exact id_mem M

theorem heightContentCastAdjunction_unit_mem {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m')
    (hγ : γ = γ') (M : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m γ)) :
    (heightContentCastAdjunction D Sc a ha hm hγ).unit.app M ∈ parity (R := k) _ _ 0 := by
  subst hm
  subst hγ
  exact id_mem M

theorem heightContentCastAdjunction_counit_mem {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m')
    (hγ : γ = γ') (M : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m' γ')) :
    (heightContentCastAdjunction D Sc a ha hm hγ).counit.app M ∈ parity (R := k) _ _ 0 := by
  subst hm
  subst hγ
  exact id_mem M

theorem globalContentAdjunction_unit_mem (i : I) {β δ : Multiset I} (h : {i} + β = δ)
    (M : GlobalContentModules D Sc a ha β) :
    (globalContentAdjunction D Sc i a ha h).unit.app M ∈ parity (R := k) _ _ 0 := by
  rw [globalContentAdjunction, Adjunction.comp_unit_app]
  rw [← zero_add (0 : ZMod 2)]
  exact comp_mem (heightContentUnit_mem D Sc i a ha β.card β rfl M)
    (IsSuperfunctor.map_mem (heightContentCastAdjunction_unit_mem D Sc a ha _ _ _))

theorem globalContentAdjunction_counit_mem (i : I) {β δ : Multiset I} (h : {i} + β = δ)
    (M : GlobalContentModules D Sc a ha δ) :
    (globalContentAdjunction D Sc i a ha h).counit.app M ∈ parity (R := k) _ _ 0 := by
  rw [globalContentAdjunction, Adjunction.comp_counit_app]
  rw [← zero_add (0 : ZMod 2)]
  exact comp_mem (IsSuperfunctor.map_mem (heightContentCounit_mem D Sc i a ha β.card β rfl _))
    (heightContentCastAdjunction_counit_mem D Sc a ha _ _ _)

section Weight
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- Content induction from a block of weight `x` to its successor. -/
abbrev blockInd (β : WeightBlocks D Λ x) :=
  globalContentInduction D Sc i a ha (blockSucc_val D Λ i h β).symm

/-- Content restriction from the successor of a block of weight `x`. -/
abbrev blockRes (β : WeightBlocks D Λ x) :=
  globalContentRestriction D Sc i a ha (blockSucc_val D Λ i h β).symm

/-- The content adjunction between a block and its successor. -/
abbrev blockAdj (β : WeightBlocks D Λ x) :=
  globalContentAdjunction D Sc i a ha (blockSucc_val D Λ i h β).symm

theorem inductionComponent_obj_blockSucc (β : WeightBlocks D Λ x)
    (M : WeightProduct D Sc a ha Λ x) :
    (inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).obj M =
      (blockInd D Sc a ha i Λ h β).obj (M β) := by
  rw [inductionComponent_blockSucc]
  rfl

theorem inductionComponent_map_blockSucc (β : WeightBlocks D Λ x)
    {M M' : WeightProduct D Sc a ha Λ x} (f : M ⟶ M') :
    (inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).map f =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M) ≫
        (blockInd D Sc a ha i Λ h β).map (f β) ≫
          eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M').symm :=
  superfunctor_map_of_eq (inductionComponent_blockSucc D Sc a ha i Λ h β) f

/-- The unit component at a block of weight `x`. -/
def globalWeightUnitApp (β : WeightBlocks D Λ x) (M : WeightProduct D Sc a ha Λ x) :
    M β ⟶ (blockRes D Sc a ha i Λ h β).obj
      ((inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).obj M) :=
  (blockAdj D Sc a ha i Λ h β).unit.app (M β) ≫
    (blockRes D Sc a ha i Λ h β).map
      (eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M).symm)

theorem globalWeightUnitApp_naturality (β : WeightBlocks D Λ x)
    {M M' : WeightProduct D Sc a ha Λ x} (f : M ⟶ M') :
    f β ≫ globalWeightUnitApp D Sc a ha i Λ h β M' =
      globalWeightUnitApp D Sc a ha i Λ h β M ≫ (blockRes D Sc a ha i Λ h β).map
        ((inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [inductionComponent_map_blockSucc]
  simp only [globalWeightUnitApp, Superfunctor.map, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [Functor.map_comp, ← Adjunction.unit_naturality_assoc]

/-- The unit on weight spaces. -/
def globalWeightUnit : 𝟭 (WeightProduct D Sc a ha Λ x) ⟶
    globalEFunctor D Sc a ha i Λ h ⋙ (globalF D Sc i a ha Λ h).toFunctor where
  app M β := globalWeightUnitApp D Sc a ha i Λ h β M
  naturality _ _ f := funext fun β => globalWeightUnitApp_naturality D Sc a ha i Λ h β f

/-- The counit at a block with a chosen predecessor. -/
def globalWeightCounitVia (N : WeightProduct D Sc a ha Λ y) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (inductionComponent D Sc a ha i Λ h δ).obj ((globalF D Sc i a ha Λ h).obj N) ⟶ N δ := by
  subst hβ
  exact eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β _) ≫
    (blockAdj D Sc a ha i Λ h β).counit.app (N (blockSucc D Λ i h β))

theorem globalWeightCounitVia_eq (N : WeightProduct D Sc a ha Λ y) (β β' : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) (hβ' : blockSucc D Λ i h β' = δ) :
    globalWeightCounitVia D Sc a ha i Λ h N β δ hβ =
      globalWeightCounitVia D Sc a ha i Λ h N β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The counit component at a block: through the predecessor, or zero. -/
def globalWeightCounitComponent (N : WeightProduct D Sc a ha Λ y) (δ : WeightBlocks D Λ y) :
    (inductionComponent D Sc a ha i Λ h δ).obj ((globalF D Sc i a ha Λ h).obj N) ⟶ N δ :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    globalWeightCounitVia D Sc a ha i Λ h N hδ.choose δ hδ.choose_spec
  else 0

theorem globalWeightCounitComponent_blockSucc (N : WeightProduct D Sc a ha Λ y)
    (β : WeightBlocks D Λ x) :
    globalWeightCounitComponent D Sc a ha i Λ h N (blockSucc D Λ i h β) =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β
        ((globalF D Sc i a ha Λ h).obj N)) ≫
        (blockAdj D Sc a ha i Λ h β).counit.app (N (blockSucc D Λ i h β)) := by
  unfold globalWeightCounitComponent
  split
  · rename_i hc
    exact globalWeightCounitVia_eq D Sc a ha i Λ h N _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem globalWeightCounitComponent_naturality (β : WeightBlocks D Λ x)
    {N N' : WeightProduct D Sc a ha Λ y} (g : N ⟶ N') :
    (inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).map
        ((globalF D Sc i a ha Λ h).map g) ≫
      globalWeightCounitComponent D Sc a ha i Λ h N' (blockSucc D Λ i h β) =
    globalWeightCounitComponent D Sc a ha i Λ h N (blockSucc D Λ i h β) ≫
      g (blockSucc D Λ i h β) := by
  rw [inductionComponent_map_blockSucc, globalWeightCounitComponent_blockSucc,
    globalWeightCounitComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  congr 1
  exact (blockAdj D Sc a ha i Λ h β).counit_naturality (g (blockSucc D Λ i h β))

/-- The counit on weight spaces. -/
def globalWeightCounit : (globalF D Sc i a ha Λ h).toFunctor ⋙ globalEFunctor D Sc a ha i Λ h ⟶
    𝟭 (WeightProduct D Sc a ha Λ y) where
  app N δ := globalWeightCounitComponent D Sc a ha i Λ h N δ
  naturality N N' g := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact globalWeightCounitComponent_naturality D Sc a ha i Λ h β g
    · exact (inductionComponent_isZero D Sc a ha i Λ h δ hδ _).eq_of_src _ _

theorem globalWeight_left_triangle (β : WeightBlocks D Λ x) (M : WeightProduct D Sc a ha Λ x) :
    (inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).map
        ((globalWeightUnit D Sc a ha i Λ h).app M) ≫
      globalWeightCounitComponent D Sc a ha i Λ h ((globalEFunctor D Sc a ha i Λ h).obj M)
        (blockSucc D Λ i h β) = 𝟙 _ := by
  rw [inductionComponent_map_blockSucc, globalWeightCounitComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  change eqToHom _ ≫ (blockInd D Sc a ha i Λ h β).map (globalWeightUnitApp D Sc a ha i Λ h β M) ≫
    _ = _
  simp only [globalWeightUnitApp, Superfunctor.map, Functor.map_comp, Category.assoc]
  erw [Adjunction.counit_naturality, Adjunction.left_triangle_components_assoc]
  simp

theorem globalWeight_right_triangle (β : WeightBlocks D Λ x) (N : WeightProduct D Sc a ha Λ y) :
    globalWeightUnitApp D Sc a ha i Λ h β ((globalF D Sc i a ha Λ h).obj N) ≫
      (blockRes D Sc a ha i Λ h β).map
        (globalWeightCounitComponent D Sc a ha i Λ h N (blockSucc D Λ i h β)) = 𝟙 _ := by
  rw [globalWeightCounitComponent_blockSucc]
  simp only [globalWeightUnitApp, Superfunctor.map, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact (blockAdj D Sc a ha i Λ h β).right_triangle_components _

/-- **Induction is left adjoint to restriction on weight spaces.** -/
def globalWeightAdjunction :
    globalEFunctor D Sc a ha i Λ h ⊣ (globalF D Sc i a ha Λ h).toFunctor where
  unit := globalWeightUnit D Sc a ha i Λ h
  counit := globalWeightCounit D Sc a ha i Λ h
  left_triangle_components M := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact globalWeight_left_triangle D Sc a ha i Λ h β M
    · exact (inductionComponent_isZero D Sc a ha i Λ h δ hδ _).eq_of_src _ _
  right_triangle_components N := funext fun β => globalWeight_right_triangle D Sc a ha i Λ h β N

theorem globalWeightUnitApp_mem (β : WeightBlocks D Λ x) (M : WeightProduct D Sc a ha Λ x) :
    globalWeightUnitApp D Sc a ha i Λ h β M ∈ parity (R := k) _ _ 0 := by
  unfold globalWeightUnitApp
  rw [← zero_add (0 : ZMod 2)]
  exact comp_mem (globalContentAdjunction_unit_mem D Sc a ha i (blockSucc_val D Λ i h β).symm (M β))
    (IsSuperfunctor.map_mem (F := (blockRes D Sc a ha i Λ h β).toFunctor)
      (eqToHom_mem_parity_zero (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M).symm))

theorem globalWeightUnit_mem (M : WeightProduct D Sc a ha Λ x) :
    (globalWeightUnit D Sc a ha i Λ h).app M ∈ parity (R := k) _ _ 0 := fun β =>
  globalWeightUnitApp_mem D Sc a ha i Λ h β M

theorem globalWeightCounit_mem (N : WeightProduct D Sc a ha Λ y) :
    (globalWeightCounit D Sc a ha i Λ h).app N ∈ parity (R := k) _ _ 0 := fun δ => by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change globalWeightCounitComponent D Sc a ha i Λ h N (blockSucc D Λ i h β) ∈ _
    rw [globalWeightCounitComponent_blockSucc, ← zero_add (0 : ZMod 2)]
    exact comp_mem (eqToHom_mem_parity_zero (inductionComponent_obj_blockSucc D Sc a ha i Λ h β
        ((globalF D Sc i a ha Λ h).obj N)))
      (globalContentAdjunction_counit_mem D Sc a ha i (blockSucc_val D Λ i h β).symm
        (N (blockSucc D Λ i h β)))
  · rw [(inductionComponent_isZero D Sc a ha i Λ h δ hδ _).eq_of_src
      ((globalWeightCounit D Sc a ha i Λ h).app N δ) 0]
    exact Submodule.zero_mem _

/-- Weight-space induction as a 1-morphism of the action target. -/
def globalActionE : (globalWeightSpace D Sc a ha Λ x : cyclotomicActionTarget (k := k)) ⟶
    (globalWeightSpace D Sc a ha Λ y : cyclotomicActionTarget (k := k)) :=
  globalE D Sc a ha i Λ h

/-- Weight-space restriction as a 1-morphism of the action target. -/
def globalActionF : (globalWeightSpace D Sc a ha Λ y : cyclotomicActionTarget (k := k)) ⟶
    (globalWeightSpace D Sc a ha Λ x : cyclotomicActionTarget (k := k)) :=
  globalF D Sc i a ha Λ h

/-- The weight-space unit as an even supernatural transformation. -/
def globalActionUnit : 𝟙 _ ⟶ globalActionE D Sc a ha i Λ h ≫ globalActionF D Sc a ha i Λ h :=
  SuperNatTrans.ofNatTrans (globalWeightUnit D Sc a ha i Λ h)
    (globalWeightUnit_mem D Sc a ha i Λ h)

/-- The weight-space counit as an even supernatural transformation. -/
def globalActionCounit : globalActionF D Sc a ha i Λ h ≫ globalActionE D Sc a ha i Λ h ⟶ 𝟙 _ :=
  SuperNatTrans.ofNatTrans (globalWeightCounit D Sc a ha i Λ h)
    (globalWeightCounit_mem D Sc a ha i Λ h)

/-- **The even adjunction `E_i ⊣ F_i` on weight spaces** in the Rouquier interface. -/
def globalActionAdjunction :
    SKM.SuperAdjunction (k := k) (globalActionE D Sc a ha i Λ h) (globalActionF D Sc a ha i Λ h) where
  unit := globalActionUnit D Sc a ha i Λ h
  counit := globalActionCounit D Sc a ha i Λ h
  unit_mem := Superfunctor.mem_parity_iff_isHomogeneous.2
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)
  counit_mem := Superfunctor.mem_parity_iff_isHomogeneous.2
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)
  left_triangle := by
    simp only [SCat.leftUnitor_inv, SCat.associator_hom, SCat.rightUnitor_hom]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    apply Superfunctor.hom_ext_parity
    · intro M
      change _ = 𝟙 ((globalEFunctor D Sc a ha i Λ h).obj M)
      simp [globalActionUnit, globalActionCounit, SuperNatTrans.ofNatTrans,
        globalActionE, globalE, Superfunctor.map,
        Superfunctor.obj]
      exact (globalWeightAdjunction D Sc a ha i Λ h).left_triangle_components M
    · intro M
      simp [globalActionUnit, globalActionCounit, SuperNatTrans.ofNatTrans]
  right_triangle := by
    simp only [SCat.rightUnitor_inv, SCat.associator_inv, SCat.leftUnitor_hom]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    apply Superfunctor.hom_ext_parity
    · intro N
      change _ = 𝟙 ((globalF D Sc i a ha Λ h).toFunctor.obj N)
      simp [globalActionUnit, globalActionCounit, SuperNatTrans.ofNatTrans,
        globalActionF, Superfunctor.map,
        Superfunctor.obj]
      exact (globalWeightAdjunction D Sc a ha i Λ h).right_triangle_components N
    · intro N
      simp [globalActionUnit, globalActionCounit, SuperNatTrans.ofNatTrans]

end Weight

end OddMath.QuiverHecke.CyclotomicAction
end

end
