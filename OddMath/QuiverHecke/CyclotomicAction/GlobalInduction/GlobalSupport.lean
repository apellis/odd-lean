import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Categorification.TwoRep.BlockSum
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.SKM.Basic
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient

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
