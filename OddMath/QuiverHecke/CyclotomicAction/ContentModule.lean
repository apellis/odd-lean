import OddMath.QuiverHecke.CyclotomicAction.CategoryGrading
import StringDiagrams.Super.PiTwo
import OddMath.QuiverHecke.CyclotomicAction.ContentModules
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import OddMath.QuiverHecke.CyclotomicAction.ParameterUntwist
import OddMath.QuiverHecke.CyclotomicAction.FullyFaithfulInduction
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.KernelDegree
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Content module

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Parity shifts on the full-ELV content module categories

The factor target in `DeformedActionAssembly.md` §5 is a product of
Pi-supercategories of full-ELV content modules. This module supplies that
structure on the existing `ContentModules`, rather than replacing those
modules by the older ordinary-polynomial module construction.

Postcomposition with the parity shift of super vector spaces and its odd
isomorphism supplies the parity shift of the entire module supercategory.
The source category need not admit a parity shift.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u v w
section Supermodules
variable {k : Type u} [CommRing k]
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]

/-- Parity shift of a module is the actual postcomposition with vector parity. -/
def supermoduleParityObj (M : Superfunctor k C (SVec.{u} k)) :
    Superfunctor k C (SVec.{u} k) :=
  M.comp (PiSCat.piHom (PiSCat.of k (SVec.{u} k)))

/-- The odd vector parity isomorphism is whiskered by the entire module. -/
def supermoduleParityIso (M : Superfunctor k C (SVec.{u} k)) :
    supermoduleParityObj M ≅ M where
  hom := Superfunctor.whiskerLeft M (PiSCat.ζHom (PiSCat.of k (SVec.{u} k))).hom
  inv := Superfunctor.whiskerLeft M (PiSCat.ζHom (PiSCat.of k (SVec.{u} k))).inv
  hom_inv_id := by
    rw [← Superfunctor.whiskerLeft_comp, Iso.hom_inv_id, Superfunctor.whiskerLeft_id]
    rfl
  inv_hom_id := by
    rw [← Superfunctor.whiskerLeft_comp, Iso.inv_hom_id, Superfunctor.whiskerLeft_id]
    rfl

theorem supermoduleParityIso_hom_mem (M : Superfunctor k C (SVec.{u} k)) :
    (supermoduleParityIso M).hom ∈ parity (R := k) (supermoduleParityObj M) M 1 :=
  Superfunctor.whiskerLeft_mem M
    (Superfunctor.IsSupernatural.toSuperNatTrans_mem
      (PiSupercategory.ζ_isSupernatural (R := k) (C := SVec.{u} k)))

/-- Full supernatural module maps, including odd maps, form a Pi-supercategory. -/
@[instance_reducible]
def supermodulePiSupercategory :
    PiSupercategory k (Superfunctor k C (SVec.{u} k)) :=
  PiSupercategory.ofIso supermoduleParityObj supermoduleParityIso
    supermoduleParityIso_hom_mem

@[simp] theorem supermoduleParityObj_obj (M : Superfunctor k C (SVec.{u} k)) (v : C) :
    (supermoduleParityObj M).obj v =
      (PiSupercategory.pi (R := k) (C := SVec.{u} k)).obj (M.obj v) := rfl

@[simp] theorem supermoduleParityIso_hom_app_zero
    (M : Superfunctor k C (SVec.{u} k)) (v : C) :
    (supermoduleParityIso M).hom.app 0 v = 0 := rfl

@[simp] theorem supermoduleParityIso_hom_app_one
    (M : Superfunctor k C (SVec.{u} k)) (v : C) :
    (supermoduleParityIso M).hom.app 1 v =
      (PiSupercategory.ζ (R := k) (M.obj v)).hom := rfl

end Supermodules

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Exact-content induction transformations

The dot and normalized crossing of `DeformedActionAssembly.md` §5 act on
balanced induction between exact-content module categories. A common target
content avoids casts between the two orders of a pair of colours. Induction
reverses the direction of the affine transformation. Equal-colour crossings
have the negative normalization; distinct-colour crossings retain the raw
normalization. No presentation relations or comparison with composites of
single-colour induction functors are asserted here.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
namespace BalancedInduction
variable {k : Type u} [CommRing k]
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
variable {J K : C ⥤ B} [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]

/-- The two homogeneous components of induction's mate on a balanced generator. -/
theorem transform_app_tensor {p : ZMod 2} {α : ∀ v, J.obj v ⟶ K.obj v}
    (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k))
    (w : B) (v : C) (h : K.obj v ⟶ w) (m : M.obj v) :
    ((transform hα).app p M).app p w (tensor K M.toFunctor v h m) =
      tensor J M.toFunctor v (α v ≫ twist k p h) m := by
  simp only [transform, IsSupernatural.toSuperNatTrans, ↓reduceIte]
  change (transformComponent hα M).app p w (tensor K M.toFunctor v h m) = _
  rw [transformComponent_apply, ite_eq_left rfl]
  exact transformLinear_tensor hα M w v h m
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

instance contentAppendTo_additive (β : Multiset I) (σ : List I) (γ : Multiset I)
    (hσ : β + (σ : Multiset I) = γ) :
    (contentAppendTo D Sc cutoff N β σ γ hσ).Additive where
  map_add := (truncatedAppend D Sc cutoff N σ).map_add
instance contentAppendTo_linear (β : Multiset I) (σ : List I) (γ : Multiset I)
    (hσ : β + (σ : Multiset I) = γ) :
    (contentAppendTo D Sc cutoff N β σ γ hσ).Linear k where
  map_smul f r := (truncatedAppend D Sc cutoff N σ).map_smul r f
instance contentAppendTo_super (β : Multiset I) (σ : List I) (γ : Multiset I)
    (hσ : β + (σ : Multiset I) = γ) :
    IsSuperfunctor k (contentAppendTo D Sc cutoff N β σ γ hσ) where
  map_mem := Supercategory.map_mem (truncatedAppend D Sc cutoff N σ)

abbrev contentInductionTo (β : Multiset I) (σ : List I) (γ : Multiset I)
    (hσ : β + (σ : Multiset I) = γ) :
    ContentModules D Sc cutoff N β ⥤ ContentModules D Sc cutoff N γ :=
  BalancedInduction.induction (contentAppendTo D Sc cutoff N β σ γ hσ)

/-- The exact-content component is the same quotient morphism. -/
def contentAppendToComponent {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ))
    (v : ContentCategory D Sc cutoff N β) :
    (contentAppendTo D Sc cutoff N β σ γ hσ).obj v ⟶
      (contentAppendTo D Sc cutoff N β τ γ hτ).obj v :=
  truncatedAppendComponent D Sc cutoff N a v.obj

/-- The concrete quotient component as a linear map in its affine input. -/
def contentAppendToLinear {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (v : ContentCategory D Sc cutoff N β) :
    ((pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)) →ₗ[k]
      ((contentAppendTo D Sc cutoff N β σ γ hσ).obj v ⟶
       (contentAppendTo D Sc cutoff N β τ γ hτ).obj v) := by
  let L : ((pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)) →ₗ[k]
      ((pres D Sc).obj (ob D (v.obj.word ++ σ)) ⟶
       (pres D Sc).obj (ob D (v.obj.word ++ τ))) :=
    { toFun := fun a => MonoidalCategoryStruct.whiskerLeft ((pres D Sc).obj (ob D v.obj.word)) a
      map_add' := fun a b => MonoidalSupercategory.whiskerLeft_add k _ a b
      map_smul' := fun r a => MonoidalSupercategory.whiskerLeft_smul (R := k) _ r a }
  exact (truncatedIdeal D Sc cutoff N _ _).mkQ.comp
    ((TensorProduct.mk k (End (obj D Sc cutoff v.obj.word).fst) _ (𝟙 _)).comp L)

@[simp] theorem contentAppendToLinear_apply {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (v : ContentCategory D Sc cutoff N β)
    (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)) :
    contentAppendToLinear D Sc cutoff N hσ hτ v a =
      contentAppendToComponent D Sc cutoff N hσ hτ a v := rfl

@[simp] theorem contentAppendToComponent_neg {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ))
    (v : ContentCategory D Sc cutoff N β) :
    contentAppendToComponent D Sc cutoff N hσ hτ (-a) v =
      -contentAppendToComponent D Sc cutoff N hσ hτ a v := by
  exact (contentAppendToLinear D Sc cutoff N hσ hτ v).map_neg a

/-- Restrict the appended affine transformation to exact-content objects. -/
theorem contentAppendTo_supernatural {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (ha : a ∈ parity (R := k) _ _ p) :
    IsSupernatural k p (F := contentAppendTo D Sc cutoff N β σ γ hσ)
      (G := contentAppendTo D Sc cutoff N β τ γ hτ)
      (contentAppendToComponent D Sc cutoff N hσ hτ a) where
  mem v := (truncatedAppendComponent_supernatural D Sc cutoff N ha).mem v.obj
  naturality hf := (truncatedAppendComponent_supernatural D Sc cutoff N ha).naturality hf

/-- Balanced induction reverses the affine map, keeping exact endpoints. -/
def contentInductionTransform {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (ha : a ∈ parity (R := k) _ _ p) :
    SuperNatTrans k (contentInductionTo D Sc cutoff N β τ γ hτ)
      (contentInductionTo D Sc cutoff N β σ γ hσ) :=
  BalancedInduction.transform (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha)

@[simp] theorem contentInductionTransform_tensor {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (ha : a ∈ parity (R := k) _ _ p) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β τ γ hτ).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionTransform D Sc cutoff N hσ hτ ha).app p M).app p w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β τ γ hτ) M.toFunctor v h m) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ γ hσ) M.toFunctor v
      (contentAppendToComponent D Sc cutoff N hσ hτ a v ≫ twist k p h) m :=
  BalancedInduction.transform_app_tensor
    (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M w v h m

/-- The dot acts on the raising functor `E`. -/
def contentInductionDot (β : Multiset I) (i : I) :
    SuperNatTrans k (contentE D Sc cutoff N β i) (contentE D Sc cutoff N β i) :=
  contentInductionTransform D Sc cutoff N rfl rfl (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

/-- The two colour orders have the same exact target content. -/
theorem content_pair_swap (β : Multiset I) (i j : I) :
    β + ([j, i] : Multiset I) = β + ([i, j] : Multiset I) := by
  congr 1
  exact Multiset.coe_eq_coe.mpr (List.Perm.swap i j [])

/-- Raw crossing with a common exact target, contravariant in append. -/
def contentInductionCrossRaw (β : Multiset I) (i j : I) :
    SuperNatTrans k
      (contentInductionTo D Sc cutoff N β [j, i] (β + ([i, j] : Multiset I))
        (content_pair_swap β i j))
      (contentInductionTo D Sc cutoff N β [i, j] (β + ([i, j] : Multiset I)) rfl) :=
  contentInductionTransform D Sc cutoff N rfl (content_pair_swap β i j) (crossTwo_mem D Sc i j)

/-- The normalized affine representative used by the induction crossing. -/
def contentCrossAffine (i j : I) :
    (pres D Sc).obj (ob D [i, j]) ⟶ (pres D Sc).obj (ob D [j, i]) := by
  classical
  exact if i = j then -crossTwo D Sc i j else crossTwo D Sc i j

theorem contentCrossAffine_mem (i j : I) :
    contentCrossAffine D Sc i j ∈ parity (R := k) _ _ (D.parity i * D.parity j) := by
  classical
  unfold contentCrossAffine
  split_ifs
  · exact Submodule.neg_mem _ (crossTwo_mem D Sc i j)
  · exact crossTwo_mem D Sc i j

@[simp] theorem contentCrossAffine_equal (i : I) :
    contentCrossAffine D Sc i i = -crossTwo D Sc i i := by
  simp [contentCrossAffine]

@[simp] theorem contentCrossAffine_distinct (i j : I) (h : i ≠ j) :
    contentCrossAffine D Sc i j = crossTwo D Sc i j := by
  simp [contentCrossAffine, h]

/-- Source normalization: minus the raw affine crossing for equal colours. -/
def contentInductionCross (β : Multiset I) (i j : I) :
    SuperNatTrans k
      (contentInductionTo D Sc cutoff N β [j, i] (β + ([i, j] : Multiset I))
        (content_pair_swap β i j))
      (contentInductionTo D Sc cutoff N β [i, j] (β + ([i, j] : Multiset I)) rfl) :=
  contentInductionTransform D Sc cutoff N rfl (content_pair_swap β i j)
    (contentCrossAffine_mem D Sc i j)

@[simp] theorem contentInductionDot_tensor (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppend D Sc cutoff N β [i]).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionDot D Sc cutoff N β i).app (D.parity i) M).app (D.parity i) w
      (BalancedInduction.tensor (contentAppend D Sc cutoff N β [i]) M.toFunctor v h m) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i] _ rfl) M.toFunctor v
      (contentAppendToComponent D Sc cutoff N rfl rfl (dotE D Sc [i] 0) v ≫
        twist k (D.parity i) h) m :=
  contentInductionTransform_tensor D Sc cutoff N rfl rfl _ M w v h m

@[simp] theorem contentInductionCross_tensor (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i, j] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j)).obj v ⟶ w)
    (m : M.obj v) :
    ((contentInductionCross D Sc cutoff N β i j).app (D.parity i * D.parity j) M).app
      (D.parity i * D.parity j) w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [j, i] _
        (content_pair_swap β i j)) M.toFunctor v h m) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i, j] _ rfl) M.toFunctor v
      (contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j)
        (contentCrossAffine D Sc i j) v ≫ twist k (D.parity i * D.parity j) h) m :=
  contentInductionTransform_tensor D Sc cutoff N rfl (content_pair_swap β i j) _ M w v h m

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Content induction composition

The all-module comparison needed by `DeformedActionAssembly.md` §5 identifies
successive right-append induction with block induction. It is the existing
balanced induction composition isomorphism followed by the equality induced
by word associativity. Both directions are even, and naturality includes odd
module maps. Common-target content proofs are explicit. No crossing relation
on composites or triple coherence is asserted here.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u

private theorem appendFamily_map_heq {ι : Type*} {A B : ι → Type*}
    (F : ∀ i, A i → B i) {i j : ι} (h : i = j)
    {a : A i} {b : A j} (hab : HEq a b) : HEq (F i a) (F j b) := by
  cases h
  cases hab
  rfl

private theorem appendFamily_add_heq {ι : Type*} (A : ι → Type*)
    [∀ i, Add (A i)] {i j : ι} (h : i = j)
    {a c : A i} {b d : A j} (hab : HEq a b) (hcd : HEq c d) :
    HEq (a + c) (b + d) := by
  cases h
  cases hab
  cases hcd
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem appendPair_assoc (v w σ τ : List I) :
    ((v ++ σ) ++ τ, (w ++ σ) ++ τ) = (v ++ (σ ++ τ), w ++ (σ ++ τ)) := by
  simp only [List.append_assoc]

/-- This is a statement about linear maps, not signed composition: no parity
restriction on the coefficient tensor is needed. -/
theorem rightContext_append_heq (σ τ v w : List I) (f : hom D Sc cutoff v w) :
    HEq (rightContext D Sc cutoff τ (v ++ σ) (w ++ σ)
      (rightContext D Sc cutoff σ v w f))
      (rightContext D Sc cutoff (σ ++ τ) v w f) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    exact (heq_of_eq (((rightContext D Sc cutoff τ (v ++ σ) (w ++ σ)).comp
      (rightContext D Sc cutoff σ v w)).map_add f g)).trans
      ((appendFamily_add_heq (fun z : List I × List I => hom D Sc cutoff z.1 z.2)
        (appendPair_assoc v w σ τ) hf hg).trans
        (heq_of_eq ((rightContext D Sc cutoff (σ ++ τ) v w).map_add f g).symm))
  | tmul a f =>
    have hf : HEq ((f ▷ (pres D Sc).obj (ob D σ)) ▷ (pres D Sc).obj (ob D τ))
        (f ▷ (pres D Sc).obj (ob D (σ ++ τ))) :=
      (conj_eqToHom_iff_heq _ _
        (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))
        (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc w σ τ))).1
        (whiskerRight_whiskerRight_list D Sc f σ τ)
    exact appendFamily_map_heq
      (A := fun z : List I × List I =>
        (pres D Sc).obj (ob D z.1) ⟶ (pres D Sc).obj (ob D z.2))
      (B := fun z : List I × List I => hom D Sc cutoff z.1 z.2)
      (fun _ g => a ⊗ₜ[k] g) (appendPair_assoc v w σ τ) hf

variable (N : ℕ)

theorem truncatedRightContext_append_heq (σ τ v w : List I)
    (f : TruncatedOld D Sc cutoff N v w) :
    HEq (truncatedRightContext D Sc cutoff N τ (v ++ σ) (w ++ σ)
      (truncatedRightContext D Sc cutoff N σ v w f))
      (truncatedRightContext D Sc cutoff N (σ ++ τ) v w f) := by
  obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N v w).mkQ_surjective f
  simp only [truncatedRightContext_mk]
  exact appendFamily_map_heq
    (A := fun z : List I × List I => hom D Sc cutoff z.1 z.2)
    (B := fun z : List I × List I => TruncatedOld D Sc cutoff N z.1 z.2)
    (fun z => (truncatedIdeal D Sc cutoff N z.1 z.2).mkQ)
    (appendPair_assoc v w σ τ) (rightContext_append_heq D Sc cutoff σ τ v w f)

private theorem contentWord_ext {β : Multiset I}
    {v w : ContentCategory D Sc cutoff N β} (h : v.obj.word = w.obj.word) : v = w := by
  rcases v with ⟨⟨v⟩, hv⟩
  rcases w with ⟨⟨w⟩, hw⟩
  cases h
  rfl

/-- Independent target proofs are allowed: proof irrelevance identifies them. -/
theorem contentAppend_comp_eq (β : Multiset I) (σ τ : List I) (γ : Multiset I)
    (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ) :
    contentAppend D Sc cutoff N β σ ⋙
        contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h =
      contentAppendTo D Sc cutoff N β (σ ++ τ) γ h' := by
  apply Functor.hext
  · intro v
    exact contentWord_ext D Sc cutoff N (List.append_assoc v.obj.word σ τ)
  · intro v w f
    exact truncatedRightContext_append_heq D Sc cutoff N σ τ v.obj.word w.obj.word f

/-- Equality of append functors induces equality of their balanced induction functors. -/
private theorem induction_eq {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J K : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K] (h : J = K) :
    BalancedInduction.induction (k := k) J = BalancedInduction.induction K := by
  subst K
  rfl

def inductionCompOfEq
    {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (L : C ⥤ E)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [L.Additive] [L.Linear k] [IsSuperfunctor k L] (e : J ⋙ K = L) :
    BalancedInduction.induction J ⋙ BalancedInduction.induction K ≅
      BalancedInduction.induction (k := k) L :=
  BalancedInduction.inductionComp J K ≪≫ eqToIso (induction_eq _ _ e)

/-- Parity of both directions of an ordinary natural comparison. -/
def EvenComparisonAt {C B : Type*} [Category* C] [Category* B]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} (e : F ≅ G) (M : C) : Prop :=
  e.hom.app M ∈ parity (R := k) (F.obj M) (G.obj M) 0 ∧
  e.inv.app M ∈ parity (R := k) (G.obj M) (F.obj M) 0

private theorem inductionCompOfEq_mem
    {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (L : C ⥤ E)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [L.Additive] [L.Linear k] [IsSuperfunctor k L] (e : J ⋙ K = L)
    (M : Superfunctor k C (SVec k)) :
    EvenComparisonAt (k := k) (inductionCompOfEq J K L e) M := by
  subst L
  simpa only [EvenComparisonAt, inductionCompOfEq, eqToIso_refl, Iso.trans_refl] using
    And.intro (BalancedInduction.inductionComp_hom_mem J K M)
      (BalancedInduction.inductionComp_inv_mem J K M)

/-- Successive induction, with the final content transport made explicit. -/
def contentInductionComp (β : Multiset I) (σ τ : List I) (γ : Multiset I)
    (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ) :
    contentInduction D Sc cutoff N β σ ⋙
        contentInductionTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h ≅
      contentInductionTo D Sc cutoff N β (σ ++ τ) γ h' :=
  inductionCompOfEq
    (contentAppend D Sc cutoff N β σ)
    (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
    (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h')
    (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h')

/-- Both directions are even on every module. -/
theorem contentInductionComp_mem (β : Multiset I) (σ τ : List I) (γ : Multiset I)
    (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) :
    EvenComparisonAt (k := k) (contentInductionComp D Sc cutoff N β σ τ γ h h') M :=
  inductionCompOfEq_mem
    (contentAppend D Sc cutoff N β σ)
    (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
    (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h')
    (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h') M

/-- The raising-functor pair comparison, with no common-content recasting of the composite. -/
def contentEPairComparison (β : Multiset I) (i j : I) :
    contentE D Sc cutoff N β i ⋙ contentE D Sc cutoff N (β + ([i] : Multiset I)) j ≅
      contentInductionTo D Sc cutoff N β [i,j]
        ((β + ([i] : Multiset I)) + ([j] : Multiset I))
        (by rw [add_assoc]; rfl) :=
  contentInductionComp D Sc cutoff N β [i] [j] _ rfl _

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Relations on exact-content induction modules

The normalized equal-colour crossing of `DeformedActionAssembly.md` §5
acts square-zero on the balanced induction modules, retaining the total
coefficient parity twist. All statements are over an arbitrary commutative
base ring and on the existing exact-content categories.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem contentAppendToComponent_comp {β γ : Multiset I} {σ τ υ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (hυ : β + (υ : Multiset I) = γ)
    (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ))
    {b : (pres D Sc).obj (ob D τ) ⟶ (pres D Sc).obj (ob D υ)}
    {p : ZMod 2} (hb : b ∈ parity (R := k) _ _ p)
    (v : ContentCategory D Sc cutoff N β) :
    contentAppendToComponent D Sc cutoff N hσ hτ a v ≫
      contentAppendToComponent D Sc cutoff N hτ hυ b v =
    contentAppendToComponent D Sc cutoff N hσ hυ (a ≫ b) v := by
  have he := BoxProd.tmulHom_comp_tmulHom
    (X := ⟨(obj D Sc cutoff v.obj.word).fst,
      (pres D Sc).obj (ob D v.obj.word) ⊗ (pres D Sc).obj (ob D σ)⟩)
    (Y := ⟨(obj D Sc cutoff v.obj.word).fst,
      (pres D Sc).obj (ob D v.obj.word) ⊗ (pres D Sc).obj (ob D τ)⟩)
    (Z := ⟨(obj D Sc cutoff v.obj.word).fst,
      (pres D Sc).obj (ob D v.obj.word) ⊗ (pres D Sc).obj (ob D υ)⟩)
    (id_mem (R := k) (obj D Sc cutoff v.obj.word).fst)
    ((pres D Sc).obj (ob D v.obj.word) ◁ a) (𝟙 _)
    (MonoidalSupercategory.whiskerLeft_mem ((pres D Sc).obj (ob D v.obj.word)) hb)
  rw [koszulSign_zero_left, one_smul, Category.id_comp,
    ← MonoidalSupercategory.whiskerLeft_comp k] at he
  exact congrArg (truncatedIdeal D Sc cutoff N _ _).mkQ he

@[simp] theorem contentAppendToComponent_zero {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (v : ContentCategory D Sc cutoff N β) :
    contentAppendToComponent D Sc cutoff N hσ hτ 0 v = 0 := by
  exact (contentAppendToLinear D Sc cutoff N hσ hτ v).map_zero

theorem contentCrossAffine_square (i : I) :
    contentCrossAffine D Sc i i ≫ contentCrossAffine D Sc i i = 0 := by
  rw [contentCrossAffine_equal, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  have he := crossE_mul_crossE D Sc (w := [i,i]) [] [] i (j := 0) rfl rfl
  have hc : crossE D Sc [i,i] 0 = crossTwo D Sc i i :=
    genE_eq D Sc (by simpa using sChain_cross [] [] i rfl rfl)
  rw [hc] at he
  exact he

/-- Linear action of a homogeneous appended endomorphism on each target object. -/
def contentInductionEndLinear {β : Multiset I} {σ : List I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D σ))} (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) :=
  BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N rfl rfl ha) M w

/-- The normalized equal-colour crossing is square-zero on every induced module. -/
theorem contentInductionCross_square_linear (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,i] : Multiset I))) :
    (contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w).comp
      (contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w) = 0 := by
  unfold contentInductionEndLinear
  rw [BalancedInduction.transformLinear_comp]
  have hz : BalancedInduction.transformLinear
      ((contentAppendTo_supernatural D Sc cutoff N rfl rfl (contentCrossAffine_mem D Sc i i)).comp
       (contentAppendTo_supernatural D Sc cutoff N rfl rfl (contentCrossAffine_mem D Sc i i))) M w = 0 := by
    apply BalancedInduction.hom_ext
    intro v h m
    rw [BalancedInduction.transformLinear_tensor]
    change BalancedInduction.tensor _ M.toFunctor v
      ((contentAppendToComponent D Sc cutoff N rfl rfl (contentCrossAffine D Sc i i) v ≫
        contentAppendToComponent D Sc cutoff N rfl rfl (contentCrossAffine D Sc i i) v) ≫ _) m = 0
    rw [contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _
      (contentCrossAffine_mem D Sc i i), contentCrossAffine_square,
      contentAppendToComponent_zero, Limits.zero_comp]
    simp [BalancedInduction.tensor]
  rw [hz, smul_zero]

namespace BalancedInduction
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  {J : C ⥤ B} [J.Additive] [J.Linear k] [IsSuperfunctor k J]

/-- A square-zero homogeneous linear action gives a square-zero module map. -/
theorem transformComponent_square_of_linear {p : ZMod 2} {a : ∀ v, J.obj v ⟶ J.obj v}
    (ha : IsSupernatural k p a) (M : Superfunctor k C (SVec k))
    (hs : ∀ w, (transformLinear ha M w).comp (transformLinear ha M w) = 0) :
    transformComponent ha M ≫ transformComponent ha M = 0 := by
  apply Superfunctor.hom_ext
  intro r w
  have he := hs w
  simp only [Superfunctor.comp_app, transformComponent_app, Superfunctor.zero_app]
  change (if r = p then transformLinear ha M w else 0).comp
      (if 0 = p then transformLinear ha M w else 0) +
    (if r + 1 = p then transformLinear ha M w else 0).comp
      (if 1 = p then transformLinear ha M w else 0) = 0
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp only [SVec.zmod2_one_add_one, zero_add, add_zero, ↓reduceIte, one_ne_zero, zero_ne_one,
      LinearMap.comp_zero, LinearMap.zero_comp] <;> first | rfl | exact he
/-- A nilHecke slide descends through balanced induction with the negative crossing. -/
theorem transformLinear_slide {p : ZMod 2} {a b c : ∀ v, J.obj v ⟶ J.obj v}
    (ha : IsSupernatural k p a) (hb : IsSupernatural k p b) (hc : IsSupernatural k p c)
    (hrel : ∀ v, b v ≫ a v - sign k (p * p) • (a v ≫ c v) = 𝟙 _)
    (M : Superfunctor k C (SVec k)) (w : B) :
    (-transformLinear ha M w).comp (transformLinear hc M w) -
      sign k (p * p) • ((transformLinear hb M w).comp (-transformLinear ha M w)) =
      LinearMap.id := by
  rw [LinearMap.neg_comp, LinearMap.comp_neg, transformLinear_comp ha hc,
    transformLinear_comp hb ha]
  simp only [smul_neg, smul_smul, Supercategory.sign_mul_self, one_smul, sub_neg_eq_add]
  apply hom_ext
  intro v h m
  have hpp : p + p = 0 := by
    rcases parity_eq_zero_or_one p with rfl | rfl <;> decide
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    transformLinear_tensor, hpp, twist_zero, LinearMap.id_apply]
  have he := congrArg (fun f => tensor J M.toFunctor v (f ≫ h) m) (hrel v)
  simp only [Preadditive.sub_comp, Linear.smul_comp, Category.id_comp,
    tensor, TensorProduct.sub_tmul, ← TensorProduct.smul_tmul', map_sub, map_smul] at he ⊢
  simpa only [sub_eq_add_neg, add_comm] using he

/-- The other nilHecke slide, with the same Koszul composition convention. -/
theorem transformLinear_slide_right {p : ZMod 2} {a b c : ∀ v, J.obj v ⟶ J.obj v}
    (ha : IsSupernatural k p a) (hb : IsSupernatural k p b) (hc : IsSupernatural k p c)
    (hrel : ∀ v, a v ≫ b v - sign k (p * p) • (c v ≫ a v) = 𝟙 _)
    (M : Superfunctor k C (SVec k)) (w : B) :
    (transformLinear hc M w).comp (-transformLinear ha M w) -
      sign k (p * p) • ((-transformLinear ha M w).comp (transformLinear hb M w)) =
      LinearMap.id := by
  rw [LinearMap.comp_neg, LinearMap.neg_comp, transformLinear_comp hc ha,
    transformLinear_comp ha hb]
  simp only [smul_neg, smul_smul, Supercategory.sign_mul_self, one_smul, sub_neg_eq_add]
  apply hom_ext
  intro v h m
  have hpp : p + p = 0 := by
    rcases parity_eq_zero_or_one p with rfl | rfl <;> decide
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    transformLinear_tensor, hpp, twist_zero, LinearMap.id_apply]
  have he := congrArg (fun f => tensor J M.toFunctor v (f ≫ h) m) (hrel v)
  simp only [Preadditive.sub_comp, Linear.smul_comp, Category.id_comp,
    tensor, TensorProduct.sub_tmul, ← TensorProduct.smul_tmul', map_sub, map_smul] at he ⊢
  simpa only [sub_eq_add_neg, add_comm] using he

end BalancedInduction

@[simp] theorem contentAppendToComponent_sub_smul {β : Multiset I} {σ : List I}
    (a b : End ((pres D Sc).obj (ob D σ))) (r : k)
    (v : ContentCategory D Sc cutoff N β) :
    contentAppendToComponent D Sc cutoff N rfl rfl (a - r • b) v =
      contentAppendToComponent D Sc cutoff N rfl rfl a v -
        r • contentAppendToComponent D Sc cutoff N rfl rfl b v := by
  change contentAppendToLinear D Sc cutoff N rfl rfl v (a - r • b) =
    contentAppendToLinear D Sc cutoff N rfl rfl v a -
      r • contentAppendToLinear D Sc cutoff N rfl rfl v b
  rw [map_sub, map_smul]

@[simp] theorem contentAppendToComponent_id {β : Multiset I} {σ : List I}
    (v : ContentCategory D Sc cutoff N β) :
    contentAppendToComponent D Sc cutoff N (σ := σ) rfl rfl (𝟙 _) v = 𝟙 _ := by
  simp only [contentAppendToComponent, truncatedAppendComponent, appendComponent,
    MonoidalSupercategory.whiskerLeft_id k]
  rfl

theorem crossTwo_self_parity (i : I) :
    crossTwo D Sc i i ∈ parity (R := k) _ _ (D.parity i) := by
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
  simpa only [hp] using crossTwo_mem D Sc i i

theorem pairDot_zero_parity (i : I) :
    dotE D Sc [i,i] 0 ∈ parity (R := k) _ _ (D.parity i) :=
  firstDot_parity D Sc i [i]

theorem pairDot_one_parity (i : I) :
    dotE D Sc [i,i] 1 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa using positionedDot_parity D Sc [i] [] i

/-- The first signed nilHecke slide for the normalized crossing on induced modules. -/
theorem contentInduction_slide_linear (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,i] : Multiset I))) :
    (-contentInductionEndLinear D Sc cutoff N (crossTwo_self_parity D Sc i) M w).comp
        (contentInductionEndLinear D Sc cutoff N (pairDot_one_parity D Sc i) M w) -
      sign k (D.parity i * D.parity i) •
        ((contentInductionEndLinear D Sc cutoff N (pairDot_zero_parity D Sc i) M w).comp
          (-contentInductionEndLinear D Sc cutoff N (crossTwo_self_parity D Sc i) M w)) =
      LinearMap.id := by
  apply BalancedInduction.transformLinear_slide
  intro v
  rw [contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _
      (crossTwo_self_parity D Sc i),
    contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _ (pairDot_one_parity D Sc i),
    ← contentAppendToComponent_sub_smul]
  have he := crossE_dotE D Sc (w := [i,i]) [] [] i (j := 0) rfl rfl
  have hc : crossE D Sc [i,i] 0 = crossTwo D Sc i i :=
    genE_eq D Sc (by simpa using sChain_cross [] [] i rfl rfl)
  rw [hc, ← sign_eq_zsign] at he
  change dotE D Sc [i,i] 0 ≫ crossTwo D Sc i i -
    sign k (D.parity i * D.parity i) • (crossTwo D Sc i i ≫ dotE D Sc [i,i] 1) = 𝟙 _ at he
  rw [he, contentAppendToComponent_id]

/-- The existing normalized crossing is exactly the negative raw induction operator. -/
theorem contentInductionCross_linear_eq_neg (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,i] : Multiset I))) :
    contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w =
      -contentInductionEndLinear D Sc cutoff N (crossTwo_self_parity D Sc i) M w := by
  apply BalancedInduction.hom_ext
  intro v h m
  unfold contentInductionEndLinear
  rw [LinearMap.neg_apply, BalancedInduction.transformLinear_tensor,
    BalancedInduction.transformLinear_tensor]
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
  have hn : contentAppendToComponent D Sc cutoff N (β := β) rfl rfl
      (-crossTwo D Sc i i) v =
      -contentAppendToComponent D Sc cutoff N rfl rfl (crossTwo D Sc i i) v := by
    simpa only [zero_sub, one_smul, contentAppendToComponent_zero] using
      contentAppendToComponent_sub_smul D Sc cutoff N 0 (crossTwo D Sc i i) 1 v
  rw [contentCrossAffine_equal, hn, hp, Preadditive.neg_comp]
  simp [BalancedInduction.tensor, TensorProduct.neg_tmul]

/-- The slide above uses the published normalized crossing, not a renamed surrogate. -/
theorem contentInduction_normalized_slide_linear (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,i] : Multiset I))) :
    (contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w).comp
        (contentInductionEndLinear D Sc cutoff N (pairDot_one_parity D Sc i) M w) -
      sign k (D.parity i * D.parity i) •
        ((contentInductionEndLinear D Sc cutoff N (pairDot_zero_parity D Sc i) M w).comp
          (contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w)) =
      LinearMap.id := by
  rw [contentInductionCross_linear_eq_neg]
  exact contentInduction_slide_linear D Sc cutoff N β i M w

/-- The second signed nilHecke slide on the actual normalized induction operator. -/
theorem contentInduction_normalized_slide_right_linear (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,i] : Multiset I))) :
    (contentInductionEndLinear D Sc cutoff N (pairDot_one_parity D Sc i) M w).comp
        (contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w) -
      sign k (D.parity i * D.parity i) •
        ((contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w).comp
          (contentInductionEndLinear D Sc cutoff N (pairDot_zero_parity D Sc i) M w)) =
      LinearMap.id := by
  rw [contentInductionCross_linear_eq_neg]
  apply BalancedInduction.transformLinear_slide_right
  intro v
  rw [contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _ (pairDot_zero_parity D Sc i),
    contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _ (crossTwo_self_parity D Sc i),
    ← contentAppendToComponent_sub_smul]
  have he := dotE_crossE D Sc (w := [i,i]) [] [] i (j := 0) rfl rfl
  have hc : crossE D Sc [i,i] 0 = crossTwo D Sc i i :=
    genE_eq D Sc (by simpa using sChain_cross [] [] i rfl rfl)
  rw [hc, ← sign_eq_zsign] at he
  change crossTwo D Sc i i ≫ dotE D Sc [i,i] 0 -
    sign k (D.parity i * D.parity i) • (dotE D Sc [i,i] 1 ≫ crossTwo D Sc i i) = 𝟙 _ at he
  rw [he, contentAppendToComponent_id]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The original-parameter quadratic on common-content induction tensors

`DeformedActionAssembly.md` §6: the two actual induction crossings, over
`parameterTwist Sc`, compose to the ordered signed evaluation with the
specified `Sc`. The source is the actual two-word affine relation, with no
finite-colour assumption. This does not yet identify powers of the dotted
module operators with that ordered evaluation or assemble weight functors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem crossTwo_comp_pairQuad {i j : I} (hij : i ≠ j) :
    crossTwo D Sc i j ≫ crossTwo D Sc j i =
      pairQuadPoly D Sc i j (dotE D Sc [i,j] 0) (dotE D Sc [i,j] 1) := by
  unfold crossTwo
  rw [cl_comp]
  unfold pairQuadPoly
  split_ifs with hd
  · exact cross_cross_ne_zero D Sc [] [] hij hd _
  · exact cross_cross_ne D Sc [] [] hij hd _

/-- Actual two-word source quadratic, with the parameter involution cancelled. -/
theorem crossTwo_comp_parameterUntwist {i j : I} (hij : i ≠ j) :
    sign k (D.parity i * D.parity j) •
      (crossTwo D (parameterTwist D Sc) i j ≫ crossTwo D (parameterTwist D Sc) j i) =
      elvSignedPairQuadEval D Sc (R := End ((pres D (parameterTwist D Sc)).obj (ob D [i,j]))) i j
        (dotE D (parameterTwist D Sc) [i,j] 0) (dotE D (parameterTwist D Sc) [i,j] 1) := by
  rw [crossTwo_comp_pairQuad D _ hij, sign_eq_zsign]
  exact pairQuadPoly_parameterTwist_eval D Sc
    (R := End ((pres D (parameterTwist D Sc)).obj (ob D [i,j]))) hij _ _

@[simp] theorem contentAppendToComponent_smul {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (r : k) (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ))
    (v : ContentCategory D Sc cutoff N β) :
    contentAppendToComponent D Sc cutoff N hσ hτ (r • a) v =
      r • contentAppendToComponent D Sc cutoff N hσ hτ a v := by
  exact (contentAppendToLinear D Sc cutoff N hσ hτ v).map_smul r a

/-- Two crossed append maps on the same content endpoint, evaluated on an actual
balanced induction tensor. The resulting ordered polynomial has original Sc. -/
theorem contentInduction_quadratic_tensor (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (v : ContentCategory D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I)))
    (h : (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl).obj v ⟶ w)
    (m : M.obj v) :
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N rfl
        (content_pair_swap β i j) (contentCrossAffine_mem D (parameterTwist D Sc) i j)) M w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N
          (content_pair_swap β i j) rfl (contentCrossAffine_mem D (parameterTwist D Sc) j i)) M w
        (BalancedInduction.tensor
          (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v h m)) =
    BalancedInduction.tensor
      (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v
      (contentAppendToComponent D (parameterTwist D Sc) cutoff N rfl rfl
        (elvSignedPairQuadEval D Sc (R := End ((pres D (parameterTwist D Sc)).obj (ob D [i,j]))) i j
          (dotE D (parameterTwist D Sc) [i,j] 0)
          (dotE D (parameterTwist D Sc) [i,j] 1)) v ≫ h) m := by
  let p := D.parity i * D.parity j
  have hp : D.parity j * D.parity i = p := mul_comm _ _
  have hpp : p + p = 0 := by
    rcases parity_eq_zero_or_one p with h | h <;> simp [h]
  have hsq : p * p = p := by
    rcases parity_eq_zero_or_one p with h | h <;> simp [h]
  rw [BalancedInduction.transformLinear_tensor, BalancedInduction.transformLinear_tensor,
    twist_comp]
  rw [twist_of_mem _ ((contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N
    (content_pair_swap β i j) rfl (contentCrossAffine_mem D (parameterTwist D Sc) j i)).mem v)]
  rw [← twist_add, hp, hpp, twist_zero, hsq, Linear.smul_comp, Linear.comp_smul,
    ← Category.assoc,
    contentAppendToComponent_comp D (parameterTwist D Sc) cutoff N rfl
      (content_pair_swap β i j) rfl _ (contentCrossAffine_mem D (parameterTwist D Sc) j i),
    ← Linear.smul_comp, ← contentAppendToComponent_smul,
    contentCrossAffine_distinct D _ i j hij, contentCrossAffine_distinct D _ j i hij.symm,
    crossTwo_comp_parameterUntwist D Sc hij]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Ordered polynomials in content induction operators

`DeformedActionAssembly.md` §5 (8) and §6 (9): powers of the induced dot
operators evaluate on balanced tensors with the total-parity twist. Each
interior coefficient of the specified parameter polynomial is identified
with its ordered source evaluation. The leading terms and the sum forming
the crossing square, and the corrected mixed braid, remain to be assembled.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
namespace BalancedInduction
variable {k : Type u} [CommRing k]
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
variable {J : C ⥤ B} [J.Additive] [J.Linear k] [IsSuperfunctor k J]

private theorem half_succ_parity (n : ℕ) :
    (((n + 1) / 2 : ℕ) : ZMod 2) = (n : ZMod 2) + (n / 2 : ℕ) := by
  have h : (n + 1) / 2 + n / 2 = n := by omega
  have he := congrArg (Nat.cast : ℕ → ZMod 2) h
  push_cast at he
  have hz : (2 : ZMod 2) = 0 := rfl
  linear_combination he - (n / 2 : ℕ) * hz

/-- Powers retain the twist of the entire kernel morphism, including odd coefficients. -/
theorem transformLinear_pow_tensor {p : ZMod 2} {a : ∀ v, End (J.obj v)}
    (ha : IsSupernatural k p a) (M : Superfunctor k C (SVec k))
    (w : B) (n : ℕ) (v : C) (h : J.obj v ⟶ w) (m : M.obj v) :
    (transformLinear ha M w ^ n) (tensor J M.toFunctor v h m) =
      sign k (p * (n / 2 : ℕ)) •
        tensor J M.toFunctor v ((a v ^ n) ≫ twist k ((n : ZMod 2) * p) h) m := by
  induction n generalizing h with
  | zero => simp [twist_zero, sign_zero]
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, transformLinear_tensor, ih, twist_comp,
      twist_of_mem _ (ha.mem v), ← twist_add]
    simp only [Linear.smul_comp, Linear.comp_smul, tensor,
      ← TensorProduct.smul_tmul', map_smul, smul_smul]
    have hp : p * p = p := by
      rcases parity_eq_zero_or_one p with rfl | rfl <;> decide
    rw [← sign_add]
    have he : p * (n / 2 : ℕ) + (n : ZMod 2) * p * p =
        p * ((n + 1) / 2 : ℕ) := by
      rw [half_succ_parity, mul_add, mul_assoc, hp]
      ring
    rw [he]
    congr 2
    rw [pow_succ', End.mul_def, Category.assoc]
    congr 2
    push_cast
    ring
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Append preserves powers without moving any coefficient across a dot. -/
theorem contentAppendToComponent_pow {β : Multiset I} {σ : List I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D σ))} (ha : a ∈ parity (R := k) _ _ p)
    (v : ContentCategory D Sc cutoff N β) (n : ℕ) :
    contentAppendToComponent D Sc cutoff N rfl rfl (a ^ n) v =
      ((show End ((contentAppendTo D Sc cutoff N β σ _ rfl).obj v) from
        contentAppendToComponent D Sc cutoff N rfl rfl a v) ^ n :
        End ((contentAppendTo D Sc cutoff N β σ _ rfl).obj v)) := by
  induction n with
  | zero => exact contentAppendToComponent_id D Sc cutoff N v
  | succ n ih =>
    rw [pow_succ', End.mul_def, ← contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _ ha,
      ih, pow_succ', End.mul_def]

/-- The polynomial powers are powers of the induced linear operator, not source-dot notation. -/
theorem contentInductionEndLinear_pow_tensor {β : Multiset I} {σ : List I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D σ))} (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) (n : ℕ)
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    (contentInductionEndLinear D Sc cutoff N ha M w ^ n)
        (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
      sign k (p * (n / 2 : ℕ)) •
        BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v
          (contentAppendToComponent D Sc cutoff N rfl rfl (a ^ n) v ≫
            twist k ((n : ZMod 2) * p) h) m := by
  rw [contentAppendToComponent_pow D Sc cutoff N ha]
  exact BalancedInduction.transformLinear_pow_tensor _ M w n v h m

theorem contentEnd_pow_parity {σ : List I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D σ))} (ha : a ∈ parity (R := k) _ _ p)
    (n : ℕ) : a ^ n ∈ parity (R := k) _ _ ((n : ZMod 2) * p) := by
  induction n with
  | zero => simpa using id_mem (R := k) ((pres D Sc).obj (ob D σ))
  | succ n ih =>
    rw [pow_succ', End.mul_def]
    simpa [add_mul] using comp_mem ih ha

/-- Ordered powers on admissible support; the second operator acts first. -/
theorem contentInductionEndLinear_ordered_tensor {β : Multiset I} {σ : List I}
    {p q : ZMod 2} {a b : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ q)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) (r s : ℕ)
    (hr : (r : ZMod 2) * p = 0) (hs : (s : ZMod 2) * q = 0)
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionEndLinear D Sc cutoff N ha M w ^ r) *
      (contentInductionEndLinear D Sc cutoff N hb M w ^ s))
        (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
      sign k (p * (r / 2 : ℕ) + q * (s / 2 : ℕ)) •
        BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v
          ((contentAppendToComponent D Sc cutoff N rfl rfl (a ^ r) v ≫
            contentAppendToComponent D Sc cutoff N rfl rfl (b ^ s) v) ≫ h) m := by
  rw [Module.End.mul_apply, contentInductionEndLinear_pow_tensor, map_smul,
    contentInductionEndLinear_pow_tensor, hr, hs, twist_zero, twist_zero,
    smul_smul, ← sign_add, add_comm (q * _) (p * _), Category.assoc]

/-- The second positioned dot on a two-colour block. -/
theorem contentPairDot_one_parity (i j : I) :
    dotE D Sc [i,j] 1 ∈ parity (R := k) _ _ (D.parity j) := by
  simpa using positionedDot_parity D Sc [i] [] j

/-- Each specified interior coefficient acts by the ordered powers of the two
induction dots. No support assumption is added: it follows from `Sc.s_eq_zero`. -/
theorem contentInduction_dot_monomial (β : Multiset I) (i j : I) (r s : ℕ)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I)))
    (v : ContentCategory D (parameterTwist D Sc) cutoff N β)
    (h : (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl).obj v ⟶ w)
    (m : M.obj v) :
    (Sc.s i j r s •
      ((contentInductionEndLinear D (parameterTwist D Sc) cutoff N
          (contentPairDot_one_parity D (parameterTwist D Sc) i j) M w ^ s) *
       (contentInductionEndLinear D (parameterTwist D Sc) cutoff N
          (firstDot_parity D (parameterTwist D Sc) i [j]) M w ^ r)))
      (BalancedInduction.tensor
        (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v h m) =
    BalancedInduction.tensor
      (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v
      (contentAppendToComponent D (parameterTwist D Sc) cutoff N rfl rfl
        ((SKM.zsign k (D.parity i * (r / 2 : ℕ) + D.parity j * (s / 2 : ℕ)) *
          Sc.s i j r s) •
          (dotE D (parameterTwist D Sc) [i,j] 0 ^ r *
           dotE D (parameterTwist D Sc) [i,j] 1 ^ s)) v ≫ h) m := by
  by_cases hc : Sc.s i j r s = 0
  · simp [hc, contentAppendToComponent_zero, BalancedInduction.tensor]
  · obtain ⟨hr, hs⟩ := elvParameter_support D Sc hc
    rw [LinearMap.smul_apply, contentInductionEndLinear_ordered_tensor D _ cutoff N _ _ M w s r hs hr,
      contentAppendToComponent_comp D _ cutoff N rfl rfl rfl _
        (contentEnd_pow_parity D _ (firstDot_parity D _ i [j]) r),
      contentAppendToComponent_smul, Linear.smul_comp]
    simp only [BalancedInduction.tensor, ← TensorProduct.smul_tmul', map_smul, smul_smul,
      ← End.mul_def, sign_eq_zsign]
    rw [add_comm (D.parity j * _) (D.parity i * _), mul_comm (Sc.s i j r s)]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The content induction quadratic polynomial

`DeformedActionAssembly.md` §6 (9): the normalized crossing square equals
the ordered polynomial in the two positioned induction dot operators. The
affine source uses `parameterTwist Sc`, while the operator polynomial has
exactly `Sc`. Its powers are reversed relative to End multiplication on the
affine source, without commuting any dots or coefficients.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Evaluation of an appended source endomorphism on a balanced generator. -/
def contentTensorEval {β : Multiset I} {σ : List I}
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    End ((pres D Sc).obj (ob D σ)) →ₗ[k]
      BalancedInduction.Obj (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor w where
  toFun a := BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v
    (contentAppendToLinear D Sc cutoff N rfl rfl v a ≫ h) m
  map_add' a b := by
    simp only [map_add, Preadditive.add_comp, BalancedInduction.tensor, TensorProduct.add_tmul]
  map_smul' c a := by
    simp only [map_smul, Linear.smul_comp, BalancedInduction.tensor,
      ← TensorProduct.smul_tmul']
    rfl

/-- A supported dot power has no residual twist on the input coefficient. -/
theorem contentInductionEndLinear_supported_power {β : Multiset I} {σ : List I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D σ))} (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (n : ℕ) (hn : (n : ZMod 2) * p = 0) (c : k)
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    (c • (contentInductionEndLinear D Sc cutoff N ha M w ^ n))
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
    contentTensorEval D Sc cutoff N M w v h m
      ((SKM.zsign k (p * (n / 2 : ℕ)) * c) • (a ^ n)) := by
  rw [LinearMap.smul_apply, contentInductionEndLinear_pow_tensor, hn, twist_zero,
    map_smul, smul_smul]
  change _ = _ • BalancedInduction.tensor _ M.toFunctor v
    (contentAppendToComponent D Sc cutoff N rfl rfl (a ^ n) v ≫ h) m
  rw [sign_eq_zsign, mul_comm c]

/-- Ordered polynomial: the first-position power acts before the second-position power. -/
def contentInductionPairPolynomial (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I))) :=
  let A := contentInductionEndLinear D (parameterTwist D Sc) cutoff N
    (firstDot_parity D (parameterTwist D Sc) i [j]) M w
  let B := contentInductionEndLinear D (parameterTwist D Sc) cutoff N
    (contentPairDot_one_parity D (parameterTwist D Sc) i j) M w
  if D.d i j = 0 then (Sc.t i j : k) • (1 : Module.End k _) else
    ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
      Sc.s i j r s • (B ^ s * A ^ r) +
    ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i)

/-- The ordered polynomial in the induction dots evaluates to the specified source polynomial. -/
theorem contentInductionPairPolynomial_tensor (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I)))
    (v : ContentCategory D (parameterTwist D Sc) cutoff N β)
    (h : (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl).obj v ⟶ w)
    (m : M.obj v) :
    contentInductionPairPolynomial D Sc cutoff N β i j M w
      (BalancedInduction.tensor (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl)
        M.toFunctor v h m) =
    contentTensorEval D (parameterTwist D Sc) cutoff N M w v h m
      (elvSignedPairQuadEval D Sc (R := End ((pres D (parameterTwist D Sc)).obj (ob D [i,j])))
        i j (dotE D (parameterTwist D Sc) [i,j] 0) (dotE D (parameterTwist D Sc) [i,j] 1)) := by
  unfold contentInductionPairPolynomial elvSignedPairQuadEval
  split_ifs with hd
  · simp [contentTensorEval, contentAppendToLinear_apply, contentAppendToComponent_id]
  · simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      exact contentInduction_dot_monomial D Sc cutoff N β i j r s M w v h m
    · congr 1
      · exact contentInductionEndLinear_supported_power D _ cutoff N _ M w _
          (CyclotomicAction.dn_cast_mul_parity D hij) _ v h m
      · exact contentInductionEndLinear_supported_power D _ cutoff N _ M w _
          (CyclotomicAction.dn_cast_mul_parity D hij.symm) _ v h m

/-- The crossing square equals the ordered polynomial in the induction dot operators. -/
theorem contentInduction_quadratic_linear (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I))) :
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N rfl
        (content_pair_swap β i j) (contentCrossAffine_mem D (parameterTwist D Sc) i j)) M w).comp
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N
          (content_pair_swap β i j) rfl (contentCrossAffine_mem D (parameterTwist D Sc) j i)) M w) =
      contentInductionPairPolynomial D Sc cutoff N β i j M w := by
  apply BalancedInduction.hom_ext
  intro v h m
  rw [LinearMap.comp_apply, contentInductionPairPolynomial_tensor D Sc cutoff N β hij M w v h m]
  exact contentInduction_quadratic_tensor D Sc cutoff N β hij M v w h m

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Single-letter content induction relations

Advances `DeformedActionAssembly.md` §5 by transporting the checked normalized
source crossing and positioned dots through the canonical even comparison.
`contentEPair_quadratic` is the original-Sc ordered polynomial relation on
successive single-letter induction, for every module. The second target content
is explicitly recast, not silently identified. `contentEPairCrossTransform`
is supernatural against odd module maps and `contentEPairCross_total` identifies
its evaluated map. No triple coherence, mixed braid, weight assembly or
nondegeneracy is asserted in this module.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Evaluation of a module isomorphism on the entire superspace. -/
def moduleIsoLinearEquiv {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M L : Superfunctor k C (SVec k)} (e : M ≅ L) (w : C) : M.obj w ≃ₗ[k] L.obj w where
  toLinearMap := e.hom.total w
  invFun := e.inv.total w
  left_inv x := by
    have h := congrArg (fun f : M ⟶ M => f.total w) e.hom_inv_id
    rw [Superfunctor.comp_total] at h
    simp only [SuperNatTrans.total, Superfunctor.id_app_zero,
      Superfunctor.id_app_one, add_zero] at h
    exact congrArg (fun f : M.obj w →ₗ[k] M.obj w => f x) h
  right_inv x := by
    have h := congrArg (fun f : L ⟶ L => f.total w) e.inv_hom_id
    rw [Superfunctor.comp_total] at h
    simp only [SuperNatTrans.total, Superfunctor.id_app_zero,
      Superfunctor.id_app_one, add_zero] at h
    exact congrArg (fun f : L.obj w →ₗ[k] L.obj w => f x) h

/-- The second single-letter induction has its target content explicitly transported. -/
abbrev contentEPairTo (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) :=
  contentE D Sc cutoff N β i ⋙
    contentInductionTo D Sc cutoff N (β + ([i] : Multiset I)) [j] γ
      (by rw [add_assoc]; exact h)

def contentEPairToComparison (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) :
    contentEPairTo D Sc cutoff N β i j γ h ≅ contentInductionTo D Sc cutoff N β [i,j] γ h :=
  contentInductionComp D Sc cutoff N β [i] [j] γ _ h

/-- The carrier of the actual evaluated pair functor. Keeping its SVec object
intact aligns all inherited module instances with independent whiskering maps. -/
abbrev ContentEPairSpace (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) : Type u :=
  (((contentEPairTo D Sc cutoff N β i j γ h).obj M).obj w).carrier

def contentEPairEquiv (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) :
    ((contentEPairTo D Sc cutoff N β i j γ h).obj M).obj w ≃ₗ[k]
      (((contentInductionTo D Sc cutoff N β [i,j] γ h).obj M).obj w).carrier :=
  moduleIsoLinearEquiv ((contentEPairToComparison D Sc cutoff N β i j γ h).app M) w

/-- Transport of a homogeneous transformation through even natural comparisons. -/
theorem evenComparison_supernatural
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G F' G' : C ⥤ B}
    [F.Additive] [F.Linear k] [G.Additive] [G.Linear k]
    [F'.Additive] [F'.Linear k] [G'.Additive] [G'.Linear k]
    (e : F' ≅ F) (f : G' ≅ G)
    (he : ∀ M, EvenComparisonAt (k := k) e M)
    (hf : ∀ M, EvenComparisonAt (k := k) f M)
    {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M} (hx : IsSupernatural k p x) :
    IsSupernatural k p (fun M => (e.hom.app M ≫ x M) ≫ f.inv.app M) := by
  simpa only [zero_add, add_zero] using
    ((isSupernatural_of_natTrans e.hom (fun M => (he M).1)).comp hx).comp
      (isSupernatural_of_natTrans f.inv (fun M => (hf M).2))

private theorem homogeneous_total
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M}
    (hx : IsSupernatural k p x) (M : C) : hx.toSuperNatTrans.total M = x M := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

/-- Each positioned dot is transported by the same canonical even comparison. -/
def contentEPairDot (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I))) (a : Fin 2) :
    Module.End k (ContentEPairSpace D Sc cutoff N β i j _ rfl M w) :=
  (contentEPairEquiv D Sc cutoff N β i j _ rfl M w).symm.conjAlgEquiv k
    (if a = 0 then contentInductionEndLinear D Sc cutoff N (firstDot_parity D Sc i [j]) M w
      else contentInductionEndLinear D Sc cutoff N (contentPairDot_one_parity D Sc i j) M w)

/-- The polynomial retains the prescribed ordered dot powers and the specified Sc. -/
def contentEPairPolynomial (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I))) :
    Module.End k (ContentEPairSpace D (parameterTwist D Sc) cutoff N β i j _ rfl M w) :=
  let A := contentEPairDot D (parameterTwist D Sc) cutoff N β i j M w 0
  let B := contentEPairDot D (parameterTwist D Sc) cutoff N β i j M w 1
  if D.d i j = 0 then (Sc.t i j : k) • (1 : Module.End k _) else
    ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
      Sc.s i j r s • (B ^ s * A ^ r) +
    ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Append and full-content extension

The literal append/inclusion square gives the induction comparison required
for the content-module realization in SwappedVacuumCoordinates §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (ν : List I) (i : I)

/-- Induce append inside the content block then extend, or extend then use
the established old append. The comparison is natural on all module maps. -/
def oldContentAppendExtensionIso :
    BalancedInduction.induction (k := k) (oldContentAppend D Sc cutoff ν i) ⋙
        BalancedInduction.induction (oldContentInclusion D Sc cutoff (i :: ν)) ≅
      BalancedInduction.induction (oldContentInclusion D Sc cutoff ν) ⋙
        BalancedInduction.induction (CyclotomicCrossingTensor.append D Sc cutoff i) :=
  BalancedInduction.inductionComp (oldContentAppend D Sc cutoff ν i)
      (oldContentInclusion D Sc cutoff (i :: ν)) ≪≫
    BalancedInduction.inductionFunctorIsoOfEq _ _
      (oldContentAppend_inclusion D Sc cutoff ν i) ≪≫
    (BalancedInduction.inductionComp (oldContentInclusion D Sc cutoff ν)
      (CyclotomicCrossingTensor.append D Sc cutoff i)).symm

/-- Restricting old append of the canonical extension recovers content append. -/
def oldContentAppendRestrictionIso
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M ≅
      (BalancedInduction.restriction (oldContentInclusion D Sc cutoff (i :: ν))).obj
        (BalancedInduction.induced (CyclotomicCrossingTensor.append D Sc cutoff i)
          (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M)) :=
  oldContentExtensionUnitIso D Sc cutoff (i :: ν)
      (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M) ≪≫
    (BalancedInduction.restriction (oldContentInclusion D Sc cutoff (i :: ν))).mapIso
      ((oldContentAppendExtensionIso D Sc cutoff ν i).app M)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Old-content append with a prescribed target index

The mixed mate of Brundan–Ellis (1.12) uses a common upper content for the
two orders of append. This functor retains the literal old append on
objects and arrows while allowing any permutation of its content index.
The canonical full-content extension comparisons retain that append.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Append the given colour and retain a prescribed permutation of the target content. -/
def oldContentAppendTo (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ) :
    OldContentCategory D Sc cutoff ν ⥤ OldContentCategory D Sc cutoff μ where
  obj v := ⟨((oldContentAppend D Sc cutoff ν i).obj v).obj,
    ((oldContentAppend D Sc cutoff ν i).obj v).wordPerm.trans h⟩
  map f := (CyclotomicCrossingTensor.append D Sc cutoff i).map f
  map_id v := (CyclotomicCrossingTensor.append D Sc cutoff i).map_id v.obj
  map_comp f g := (CyclotomicCrossingTensor.append D Sc cutoff i).map_comp f g

instance (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ) :
    (oldContentAppendTo D Sc cutoff ν i μ h).Additive where
  map_add := (CyclotomicCrossingTensor.append D Sc cutoff i).map_add
instance (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ) :
    (oldContentAppendTo D Sc cutoff ν i μ h).Linear k where
  map_smul f r := (CyclotomicCrossingTensor.append D Sc cutoff i).map_smul r f
instance (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ) :
    IsSuperfunctor k (oldContentAppendTo D Sc cutoff ν i μ h) where
  map_mem := Supercategory.map_mem (CyclotomicCrossingTensor.append D Sc cutoff i)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Canonical extension and support on an old content block

Content conservation makes extension by the full content inclusion zero off
that content. On supported modules the actual inclusion counit is invertible.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C E : Type u} [Category.{u} C] [Category.{u} E]
  [Preadditive C] [Linear k C] [Preadditive E] [Linear k E]
  (J : C ⥤ E)

omit [Preadditive C] [Linear k C] in
theorem obj_eq_zero_of_coeff_eq_zero (M : C ⥤ SVec k) (w : E)
    (h : ∀ s (g : J.obj s ⟶ w), g = 0) (z : Obj J M w) : z = 0 := by
  have hz : (LinearMap.id : Obj J M w →ₗ[k] Obj J M w) = 0 := by
    apply hom_ext
    intro s g b
    change tensor J M s g b = 0
    rw [h s g]
    exact tensor_zero_left J M s b
  exact LinearMap.congr_fun hz z

variable [J.Full] [J.Faithful] [J.Additive] [J.Linear k]
  (N : E ⥤ SVec k) [N.Additive] [N.Linear k]

theorem counit_eq_fullyFaithfulUnitInverse (v : C) :
    counit J N (J.obj v) = fullyFaithfulUnitInverse J (J ⋙ N) v := by
  apply hom_ext
  intro s g b
  rw [counit_tensor]
  have he := fullyFaithfulUnitInverse_tensor J (J ⋙ N) v s g b
  change fullyFaithfulUnitInverse J (J ⋙ N) v (tensor J (J ⋙ N) s g b) =
    N.map (J.map (J.preimage g)) b at he
  rw [Functor.map_preimage] at he
  exact he.symm

theorem counit_bijective_at_image (v : C) :
    Function.Bijective (counit J N (J.obj v)) := by
  rw [counit_eq_fullyFaithfulUnitInverse]
  have hleft := fullyFaithfulUnitInverse_unit J (J ⋙ N) v
  have hright := unit_fullyFaithfulUnitInverse J (J ⋙ N) v
  exact ⟨fun x y h => by
    have hx := LinearMap.congr_fun hright x
    have hy := LinearMap.congr_fun hright y
    change unit J (J ⋙ N) v (fullyFaithfulUnitInverse J (J ⋙ N) v x) = x at hx
    change unit J (J ⋙ N) v (fullyFaithfulUnitInverse J (J ⋙ N) v y) = y at hy
    exact hx.symm.trans ((congrArg (unit J (J ⋙ N) v) h).trans hy),
    fun y => ⟨unit J (J ⋙ N) v y, LinearMap.congr_fun hleft y⟩⟩

end OddMath.QuiverHecke.ELV.BalancedInduction
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Support means literal zero components outside the chosen colour multiset. -/
def OldContentSupported (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) : Prop :=
  ∀ w : OldCategory D Sc cutoff, (w.word : Multiset I) ≠ (ν : Multiset I) →
    Subsingleton (N.obj w)

theorem oldContentExtension_supported (ν : List I)
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    OldContentSupported D Sc cutoff ν
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν) M) := by
  intro w hw
  have hz : ∀ z : BalancedInduction.Obj (oldContentInclusion D Sc cutoff ν) M.toFunctor w,
      z = 0 := by
    apply BalancedInduction.obj_eq_zero_of_coeff_eq_zero
    intro s g
    apply oldCategory_hom_eq_zero_of_content_ne D Sc cutoff (f := g)
    intro he
    exact hw (he.symm.trans (Multiset.coe_eq_coe.mpr s.wordPerm))
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem supported_contentCounit_bijective (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) (w : OldCategory D Sc cutoff) :
    Function.Bijective (BalancedInduction.counit (oldContentInclusion D Sc cutoff ν)
      N.toFunctor w) := by
  classical
  by_cases hw : (w.word : Multiset I) = (ν : Multiset I)
  · exact BalancedInduction.counit_bijective_at_image
      (oldContentInclusion D Sc cutoff ν) N.toFunctor
      ⟨w, Multiset.coe_eq_coe.mp hw⟩
  · have hsource := oldContentExtension_supported D Sc cutoff ν
      ((BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj N) w hw
    have htarget := hN w hw
    exact ⟨fun x y _ => hsource.elim x y, fun y => ⟨0, htarget.elim _ y⟩⟩

/-- The forward map is precisely the established balanced inclusion counit. -/
def supportedContentCounitEquiv (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (oldContentInclusion D Sc cutoff ν)
        (oldContentInclusion D Sc cutoff ν ⋙ N.toFunctor) w ≃ₗ[k] N.obj w :=
  LinearEquiv.ofBijective _ (supported_contentCounit_bijective D Sc cutoff ν N hN w)

def supportedContentCounitNatIso (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) :
    (BalancedInduction.induced (oldContentInclusion D Sc cutoff ν)
      ((BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj N)).toFunctor ≅
        N.toFunctor :=
  NatIso.ofComponents (fun w =>
    { hom := BalancedInduction.counit (oldContentInclusion D Sc cutoff ν) N.toFunctor w
      inv := (supportedContentCounitEquiv D Sc cutoff ν N hN w).symm.toLinearMap
      hom_inv_id := by
        ext z
        exact (supportedContentCounitEquiv D Sc cutoff ν N hN w).symm_apply_apply z
      inv_hom_id := by
        ext z
        exact (supportedContentCounitEquiv D Sc cutoff ν N hN w).apply_symm_apply z })
    (fun a => BalancedInduction.counit_naturality (oldContentInclusion D Sc cutoff ν)
      N.toFunctor a)

/-- Supported modules are recovered by the actual even inclusion counit. -/
def supportedContentCounitIso (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) :
    BalancedInduction.induced (oldContentInclusion D Sc cutoff ν)
      ((BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj N) ≅ N :=
  moduleIsoOfEvenNatIso _ _ (supportedContentCounitNatIso D Sc cutoff ν N hN)
    (fun w => BalancedInduction.counit_mem (oldContentInclusion D Sc cutoff ν) N w)
    (fun w => Supercategory.inv_mem
      ((supportedContentCounitNatIso D Sc cutoff ν N hN).app w)
      (BalancedInduction.counit_mem (oldContentInclusion D Sc cutoff ν) N w))

theorem supportedContentCounitIso_hom (ν : List I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff ν N) :
    (supportedContentCounitIso D Sc cutoff ν N hN).hom =
      (BalancedInduction.adjunctionCounit (oldContentInclusion D Sc cutoff ν)).app N := by
  apply Superfunctor.hom_ext
  intro p w
  rfl

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Restriction and canonical old-content extension

The literal append/inclusion square and the supported inclusion counit give
an actual supermodule comparison for restriction, alongside the induction
comparison. The support argument uses full coefficients and no flatness.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem oldAppendRestriction_supported (ν : List I) (i : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hN : OldContentSupported D Sc cutoff (i :: ν) N) :
    OldContentSupported D Sc cutoff ν
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj N) := by
  intro w hw
  apply hN ((append D Sc cutoff i).obj w)
  intro he
  apply hw
  change (w.word : Multiset I) + ([i] : Multiset I) =
    ([i] : Multiset I) + (ν : Multiset I) at he
  rw [add_comm ([i] : Multiset I)] at he
  exact add_right_cancel he

/-- The two restrictions in the append/inclusion square agree literally. -/
def oldContentRestrictionSquare (ν : List I) (i : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj
      ((BalancedInduction.restriction (oldContentInclusion D Sc cutoff (i :: ν))).obj N) ≅
    (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj N) := Iso.refl _

/-- Extending fixed-content restriction is canonically old restriction of the
canonical extension. The map is built from the actual inclusion unit/counit. -/
def oldContentRestrictionExtensionIso (ν : List I) (i : I)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    BalancedInduction.induced (oldContentInclusion D Sc cutoff ν)
      ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N) ≅
    (BalancedInduction.restriction (append D Sc cutoff i)).obj
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N) :=
  (BalancedInduction.induction (oldContentInclusion D Sc cutoff ν)).mapIso
    ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).mapIso
      (oldContentExtensionUnitIso D Sc cutoff (i :: ν) N) ≪≫
      oldContentRestrictionSquare D Sc cutoff ν i
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N)) ≪≫
    supportedContentCounitIso D Sc cutoff ν _
      (oldAppendRestriction_supported D Sc cutoff ν i _
        (oldContentExtension_supported D Sc cutoff (i :: ν) N))

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Generator formula for the content restriction comparison

The canonical inclusion unit/counit comparison sends [g ⊗ b] to
[append(g) ⊗ b]. This is the restriction-side map needed to compare the
fixed-content action generators in SwappedVacuumCoordinates §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C E : Type u} [Category.{u} C] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ E) [J.Additive] [J.Linear k] [IsSuperfunctor k J]

theorem unit_total_apply (M : Superfunctor k C (SVec k)) (v : C) (b : M.obj v) :
    ((adjunctionUnit J).app M).total v b = unit J M.toFunctor v b := by
  simp only [adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

theorem counit_total_apply (N : Superfunctor k E (SVec k)) (w : E)
    (z : Obj J (J ⋙ N.toFunctor) w) :
    ((adjunctionCounit J).app N).total w z = counit J N.toFunctor w z := by
  simp only [adjunctionCounit, Superfunctor.homMk, SuperNatTrans.total,
    counitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

end OddMath.QuiverHecke.ELV.BalancedInduction
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The comparison is the induction of the actual inclusion unit followed by
its actual inclusion counit; the append/inclusion restriction square is strict. -/
theorem oldContentRestrictionExtensionIso_hom (ν : List I) (i : I)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom =
      (BalancedInduction.induction (oldContentInclusion D Sc cutoff ν)).map
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).map
          ((BalancedInduction.adjunctionUnit
            (oldContentInclusion D Sc cutoff (i :: ν))).app N)) ≫
      (BalancedInduction.adjunctionCounit (oldContentInclusion D Sc cutoff ν)).app
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N)) := by
  simp only [oldContentRestrictionExtensionIso, Iso.trans_hom, Functor.mapIso_hom,
    oldContentRestrictionSquare, Iso.refl_hom, Category.comp_id,
    oldContentExtensionUnitIso, BalancedInduction.fullyFaithfulUnitIso_hom,
    supportedContentCounitIso_hom]

/-- The prescribed source-arrow generator is unchanged and its old arrow is appended. -/
theorem oldContentRestrictionExtensionIso_tensor (ν : List I) (i : I)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (w : OldCategory D Sc cutoff) (s : OldContentCategory D Sc cutoff ν)
    (g : (oldContentInclusion D Sc cutoff ν).obj s ⟶ w)
    (b : N.obj ((oldContentAppend D Sc cutoff ν i).obj s)) :
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom.total w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor s g b) =
      BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
        ((oldContentAppend D Sc cutoff ν i).obj s) ((append D Sc cutoff i).map g) b := by
  rw [oldContentRestrictionExtensionIso_hom, Superfunctor.comp_total]
  change ((BalancedInduction.adjunctionCounit (oldContentInclusion D Sc cutoff ν)).app
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N))).total w
      ((BalancedInduction.moduleMap (oldContentInclusion D Sc cutoff ν)
        ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).map
          ((BalancedInduction.adjunctionUnit
            (oldContentInclusion D Sc cutoff (i :: ν))).app N))).total w
        (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν)
          ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).obj N).toFunctor
            s g b)) = _
  rw [BalancedInduction.counit_total_apply]
  have hm := BalancedInduction.moduleMap_total_tensor
    (oldContentInclusion D Sc cutoff ν)
    ((BalancedInduction.restriction (oldContentAppend D Sc cutoff ν i)).map
      ((BalancedInduction.adjunctionUnit (oldContentInclusion D Sc cutoff (i :: ν))).app N))
    w s g b
  refine (congrArg (BalancedInduction.counit (oldContentInclusion D Sc cutoff ν)
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N)).toFunctor w) hm).trans ?_
  change BalancedInduction.counit (oldContentInclusion D Sc cutoff ν)
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (BalancedInduction.induced (oldContentInclusion D Sc cutoff (i :: ν)) N)).toFunctor w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν) _ s g
        (BalancedInduction.unit (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
          ((oldContentAppend D Sc cutoff ν i).obj s) b) +
        BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν) _ s (twist k 1 g) 0) = _
  rw [BalancedInduction.tensor_zero_right, add_zero, BalancedInduction.counit_tensor]
  change BalancedInduction.postcompose (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
      ((append D Sc cutoff i).map g)
      (BalancedInduction.unit (oldContentInclusion D Sc cutoff (i :: ν)) N.toFunctor
        ((oldContentAppend D Sc cutoff ν i).obj s) b) = _
  rw [BalancedInduction.unit_apply, BalancedInduction.postcompose_tensor, Category.id_comp]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Chosen content E/F comparisons as families of module isomorphisms

The content action in SwappedVacuumCoordinates §6 uses canonical extension
along the full content inclusion. The chosen append comparison, including
its inclusion unit, is natural on every supernatural input-module map.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open CategoryTheory.Functor
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u v
private theorem inverseMate_app
    {C B A O : Type u} [Category.{v} C] [Category.{v} B]
    [Category.{v} A] [Category.{v} O]
    {L₁ : C ⥤ A} {R₁ : A ⥤ C} {L₀ : B ⥤ O} {R₀ : O ⥤ B}
    {F : C ⥤ B} {G : A ⥤ O} (a : L₁ ⊣ R₁) (b : L₀ ⊣ R₀)
    (sq : R₁ ⋙ F ⟶ G ⋙ R₀) (M : C) :
    ((mateEquiv a b).symm sq).app M =
      L₀.map (F.map (a.unit.app M)) ≫ L₀.map (sq.app (L₁.obj M)) ≫
        b.counit.app (G.obj (L₁.obj M)) := by
  simp [mateEquiv]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)

/-- The chosen comparison for content induction, natural on all input maps. -/
def oldContentAppendRestrictionNaturalIso :
    BalancedInduction.induction (k := k) (oldContentAppend D Sc cutoff ν i) ≅
      (BalancedInduction.induction (oldContentInclusion D Sc cutoff ν) ⋙
        BalancedInduction.induction (append D Sc cutoff i)) ⋙
          BalancedInduction.restriction (oldContentInclusion D Sc cutoff (i :: ν)) :=
  (Functor.rightUnitor _).symm ≪≫
    isoWhiskerLeft (BalancedInduction.induction (oldContentAppend D Sc cutoff ν i))
      (BalancedInduction.fullyFaithfulUnitNaturalIso
        (oldContentInclusion D Sc cutoff (i :: ν))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (oldContentAppendExtensionIso D Sc cutoff ν i)
      (BalancedInduction.restriction (oldContentInclusion D Sc cutoff (i :: ν)))

/-- This family retains the previously chosen comparison at every input module. -/
theorem oldContentAppendRestrictionNaturalIso_hom_app
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldContentAppendRestrictionNaturalIso D Sc cutoff ν i).hom.app M =
      (oldContentAppendRestrictionIso D Sc cutoff ν i M).hom := by
  simp only [oldContentAppendRestrictionNaturalIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Functor.rightUnitor_inv_app, Functor.associator_inv_app,
    Category.id_comp, BalancedInduction.fullyFaithfulUnitNaturalIso,
    NatIso.ofComponents_hom_app, oldContentAppendRestrictionIso,
    oldContentExtensionUnitIso, Functor.mapIso_hom]
  rfl

local notation "L₀" => BalancedInduction.induction (k := k) (oldContentInclusion D Sc cutoff ν)
local notation "R₀" => BalancedInduction.restriction (k := k) (oldContentInclusion D Sc cutoff ν)
local notation "L₁" => BalancedInduction.induction (k := k) (oldContentInclusion D Sc cutoff (i :: ν))
local notation "R₁" => BalancedInduction.restriction (k := k) (oldContentInclusion D Sc cutoff (i :: ν))
local notation "Fc" => BalancedInduction.restriction (k := k) (oldContentAppend D Sc cutoff ν i)
local notation "Fo" => BalancedInduction.restriction (k := k) (append D Sc cutoff i)
local notation "Ec" => BalancedInduction.induction (k := k) (oldContentAppend D Sc cutoff ν i)
local notation "Eo" => BalancedInduction.induction (k := k) (append D Sc cutoff i)

/-- The selected literal restriction square is natural on all input maps. -/
def oldContentRestrictionSquareNaturalIso : R₁ ⋙ Fc ≅ Fo ⋙ R₀ :=
  NatIso.ofComponents (oldContentRestrictionSquare D Sc cutoff ν i) (by
    intro M N f
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [Category.comp_id, Category.id_comp]
    rfl)

private def restrictionExtensionMate : Fc ⋙ L₀ ⟶ L₁ ⋙ Fo :=
  (mateEquiv (BalancedInduction.adjunction (oldContentInclusion D Sc cutoff (i :: ν)))
    (BalancedInduction.adjunction (oldContentInclusion D Sc cutoff ν))).symm
      (oldContentRestrictionSquareNaturalIso D Sc cutoff ν i).hom

private theorem oldContentRestrictionExtensionIso_hom_mate
    (M : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentRestrictionExtensionIso D Sc cutoff ν i M).hom =
      (restrictionExtensionMate D Sc cutoff ν i).app M := by
  rw [oldContentRestrictionExtensionIso_hom, restrictionExtensionMate, inverseMate_app]
  simp only [oldContentRestrictionSquareNaturalIso, NatIso.ofComponents_hom_app,
    oldContentRestrictionSquare, Iso.refl_hom]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The selected restriction-extension comparison is natural for all
supernatural input-module maps, including odd maps. -/
theorem oldContentRestrictionExtensionIso_naturality
    {M N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)} (f : M ⟶ N) :
    (L₀).map ((Fc).map f) ≫ (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom =
      (oldContentRestrictionExtensionIso D Sc cutoff ν i M).hom ≫ (Fo).map ((L₁).map f) := by
  rw [oldContentRestrictionExtensionIso_hom_mate, oldContentRestrictionExtensionIso_hom_mate]
  exact (restrictionExtensionMate D Sc cutoff ν i).naturality f

/-- The chosen restriction comparison as a whole family on input modules. -/
def oldContentRestrictionExtensionNaturalIso :
    Fc ⋙ L₀ ≅ L₁ ⋙ Fo :=
  NatIso.ofComponents (oldContentRestrictionExtensionIso D Sc cutoff ν i)
    (fun f => oldContentRestrictionExtensionIso_naturality D Sc cutoff ν i f)

/-- Extension of the preceding E/F composite at content i::ν uses the
chosen append comparison and the chosen restriction comparison, in order. -/
def oldContentEFExtensionNaturalIso :
    (Fc ⋙ Ec) ⋙ L₁ ≅ (L₁ ⋙ Fo) ⋙ Eo :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft Fc (oldContentAppendExtensionIso D Sc cutoff ν i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (oldContentRestrictionExtensionNaturalIso D Sc cutoff ν i) Eo

/-- The composite comparison retains both prescribed forward maps. -/
theorem oldContentEFExtensionNaturalIso_hom_app
    (M : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentEFExtensionNaturalIso D Sc cutoff ν i).hom.app M =
      (oldContentAppendExtensionIso D Sc cutoff ν i).hom.app ((Fc).obj M) ≫
        (Eo).map (oldContentRestrictionExtensionIso D Sc cutoff ν i M).hom := by
  simp only [oldContentEFExtensionNaturalIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, oldContentRestrictionExtensionNaturalIso, NatIso.ofComponents_hom_app]

/-- The preceding E/F composite at i::ν agrees with old E/F after canonical
extension and restriction. Its source is the chosen content composite. -/
def oldContentEFRestrictionNaturalIso :
    Fc ⋙ Ec ≅ ((L₁ ⋙ Fo) ⋙ Eo) ⋙ R₁ :=
  (Functor.rightUnitor _).symm ≪≫
    isoWhiskerLeft (Fc ⋙ Ec)
      (BalancedInduction.fullyFaithfulUnitNaturalIso
        (oldContentInclusion D Sc cutoff (i :: ν))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (oldContentEFExtensionNaturalIso D Sc cutoff ν i) R₁

/-- The following F/E composite at ν agrees with old F/E after canonical
extension and restriction, using the selected append-restriction map. -/
def oldContentFERestrictionNaturalIso :
    Ec ⋙ Fc ≅ ((L₀ ⋙ Eo) ⋙ Fo) ⋙ R₀ :=
  isoWhiskerRight (oldContentAppendRestrictionNaturalIso D Sc cutoff ν i) Fc ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (L₀ ⋙ Eo) (oldContentRestrictionSquareNaturalIso D Sc cutoff ν i) ≪≫
    (Functor.associator _ _ _).symm

/-- The following-composite chart keeps the chosen E comparison under F. -/
theorem oldContentFERestrictionNaturalIso_hom_app
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldContentFERestrictionNaturalIso D Sc cutoff ν i).hom.app M =
      (Fc).map (oldContentAppendRestrictionIso D Sc cutoff ν i M).hom := by
  simp only [oldContentFERestrictionNaturalIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    oldContentAppendRestrictionNaturalIso_hom_app, oldContentRestrictionSquareNaturalIso,
    NatIso.ofComponents_hom_app, oldContentRestrictionSquare, Iso.refl_hom,
    Category.comp_id]
  erw [Category.comp_id, Category.comp_id]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Canonical content induction comparison on quotient generators

The induction and restriction extension comparisons use the same literal
append/inclusion square. Their tensor formulas support the adjunction-map
comparison in SwappedVacuumCoordinates §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : B ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

private def compInsertion (M : Superfunctor k C (SVec k)) :
    induced (J ⋙ K) M ⟶ induced K (induced J M) := (inductionComp J K).inv.app M

/-- A nested generator with its actual induced superspace endpoint fixed. -/
def inductionInsertedTensor (M : Superfunctor k C (SVec k))
    (s : C) (w : E) (a : K.obj (J.obj s) ⟶ w) (b : M.obj s) :
    (induced K (induced J M)).obj w :=
  tensor K (induced J M).toFunctor (J.obj s) a
    (tensor J M.toFunctor s (𝟙 _) b)

private theorem compInsertion_tensor (M : Superfunctor k C (SVec k))
    (s : C) (w : E) (a : K.obj (J.obj s) ⟶ w) (b : M.obj s) :
    (compInsertion J K M).total w (tensor (J ⋙ K) M.toFunctor s a b) =
      inductionInsertedTensor J K M s w a b := inductionComp_inv_total_tensor J K M s w a b

private def compInsertionLinear (M : Superfunctor k C (SVec k)) (w : E) :
    Obj (J ⋙ K) M.toFunctor w →ₗ[k] Obj K (induced J M).toFunctor w :=
  SVec.toLinearMap ((compInsertion J K M).total w)

private theorem compInsertionLinear_tensor (M : Superfunctor k C (SVec k))
    (s : C) (w : E) (a : K.obj (J.obj s) ⟶ w) (b : M.obj s) :
    compInsertionLinear J K M w (tensor (J ⋙ K) M.toFunctor s a b) =
      inductionInsertedTensor J K M s w a b := compInsertion_tensor J K M s w a b

end OddMath.QuiverHecke.ELV.BalancedInduction
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem oldContentAppendExtensionIso_hom (ν : List I) (i : I)
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M =
      (BalancedInduction.inductionComp (oldContentAppend D Sc cutoff ν i)
        (oldContentInclusion D Sc cutoff (i :: ν))).hom.app M ≫
      (BalancedInduction.inductionComp (oldContentInclusion D Sc cutoff ν)
        (append D Sc cutoff i)).inv.app M := by
  have hm : (BalancedInduction.inductionFunctorIsoOfEq
      (oldContentAppend D Sc cutoff ν i ⋙ oldContentInclusion D Sc cutoff (i :: ν))
      (oldContentInclusion D Sc cutoff ν ⋙ append D Sc cutoff i)
      (oldContentAppend_inclusion D Sc cutoff ν i)).hom.app M = 𝟙 _ := rfl
  simp only [oldContentAppendExtensionIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, hm, Category.id_comp]

private theorem oldContentAppendExtensionIso_flatten (ν : List I) (i : I)
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν)) (w : OldCategory D Sc cutoff)
    (h : t.obj ⟶ w)
    (g : (append D Sc cutoff i).obj s.obj ⟶ t.obj) (b : M.obj s) :
    ((oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M).total w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor t h
        (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i) M.toFunctor s g b)) =
      BalancedInduction.compInsertionLinear (oldContentInclusion D Sc cutoff ν)
        (append D Sc cutoff i) M w
        (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν ⋙ append D Sc cutoff i)
          M.toFunctor s (g ≫ h) b) := by
  rw [oldContentAppendExtensionIso_hom, Superfunctor.comp_total]
  change BalancedInduction.compInsertionLinear (oldContentInclusion D Sc cutoff ν)
      (append D Sc cutoff i) M w
      (((BalancedInduction.inductionComp (oldContentAppend D Sc cutoff ν i)
        (oldContentInclusion D Sc cutoff (i :: ν))).hom.app M).total w
        (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
          (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor t h
          (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i) M.toFunctor s g b))) = _
  have hf := BalancedInduction.inductionComp_hom_total_tensor
    (oldContentAppend D Sc cutoff ν i) (oldContentInclusion D Sc cutoff (i :: ν)) M s t w h g b
  change ((BalancedInduction.inductionComp (oldContentAppend D Sc cutoff ν i)
    (oldContentInclusion D Sc cutoff (i :: ν))).hom.app M).total w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor t h
        (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i) M.toFunctor s g b)) =
    BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν ⋙ append D Sc cutoff i)
      M.toFunctor s (g ≫ h) b at hf
  exact congrArg (BalancedInduction.compInsertionLinear
    (oldContentInclusion D Sc cutoff ν) (append D Sc cutoff i) M w) hf

private theorem oldContentAppendInsertion_tensor (ν : List I) (i : I)
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (w : OldCategory D Sc cutoff)
    (a : (append D Sc cutoff i).obj s.obj ⟶ w) (b : M.obj s) :
    BalancedInduction.compInsertionLinear (oldContentInclusion D Sc cutoff ν)
      (append D Sc cutoff i) M w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff ν ⋙ append D Sc cutoff i)
        M.toFunctor s a b) =
    BalancedInduction.inductionInsertedTensor (oldContentInclusion D Sc cutoff ν)
      (append D Sc cutoff i) M s w a b := by
  exact BalancedInduction.compInsertionLinear_tensor
    (oldContentInclusion D Sc cutoff ν) (append D Sc cutoff i) M s w a b

theorem oldContentAppendExtensionIso_tensor (ν : List I) (i : I)
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν)) (w : OldCategory D Sc cutoff)
    (h : t.obj ⟶ w)
    (g : (append D Sc cutoff i).obj s.obj ⟶ t.obj) (b : M.obj s) :
    ((oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M).total w
      (BalancedInduction.tensor (oldContentInclusion D Sc cutoff (i :: ν))
        (BalancedInduction.induced (oldContentAppend D Sc cutoff ν i) M).toFunctor t h
        (BalancedInduction.tensor (oldContentAppend D Sc cutoff ν i) M.toFunctor s g b)) =
      BalancedInduction.inductionInsertedTensor (oldContentInclusion D Sc cutoff ν)
        (append D Sc cutoff i) M s w
        (g ≫ h) b := by
  have hf := oldContentAppendExtensionIso_flatten D Sc cutoff ν i M s t w h g b
  have hi := oldContentAppendInsertion_tensor D Sc cutoff ν i M s w (g ≫ h) b
  exact hf.trans hi

end OddMath.QuiverHecke.ELV
end

end
