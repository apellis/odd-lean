import StringDiagrams.Super.PiTwo
import Mathlib.CategoryTheory.Adjunction.Mates
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop.WeightedInductionNaturality
import OddMath.QuiverHecke.CyclotomicAction.FullyFaithfulInduction
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction.ModuleInductionTransform

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
