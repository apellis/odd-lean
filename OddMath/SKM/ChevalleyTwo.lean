/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyCoherence
import StringDiagrams.Super.TwoSOpGraded
import StringDiagrams.Super.TwoSOpHorizontal

/-!
# The Chevalley involution as a strict graded 2-superfunctor

[BE2] J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition
3.5, as used in the proof of Proposition 9.3: the strict graded 2-superfunctor `ω : 𝔘(𝔤) →
𝔘(𝔤)^{sop}` (`chevalleyTwo`) given by `λ ↦ -λ` on objects, `chevHomObj` (`Eᵢ ↔ Fᵢ`) on
1-morphisms and `omega` on 2-morphisms (`chevalleyTwo_isStrict`, `chevalleyTwo_isGraded`). The
target is the 2-super-opposite `TwoSOp` of Definition 3.4.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation BicategoryStruct
open Supercategory GradedSupercategory
universe u v w

private theorem sop_heq {k : Type*} [CommRing k] {C : Type*} [Category C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A B A' B' : C} (p : A = A') (q : B = B')
    (η : (SOp.mk A : SOp k C) ⟶ SOp.mk B)
    (θ : (SOp.mk A' : SOp k C) ⟶ SOp.mk B')
    (h : SOp.unsop η = eqToHom q ≫ SOp.unsop θ ≫ eqToHom p.symm) : HEq η θ := by
  subst A' B'
  apply heq_of_eq
  apply SOp.hom_ext
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

/-- Strict data of `ω`: weight negation, `chevHomObj` and `chevHom`. -/
def chevalleyStrictCore :
    TwoSuperfunctor.StrictCore k (UGr D Sc sy hc) (TwoSOp k (UGr D Sc sy hc)) where
  obj a := ⟨negWeight a⟩
  map f := ⟨chevHomObj f⟩
  map₂ {a b f g} η := (chevHom a b).map η
  map₂_id {a b} f := (chevHom a b).map_id f
  map₂_comp {a b f g h} η θ := (chevHom a b).map_comp η θ
  map₂_add {a b f g} η θ := (chevHom a b).map_add (f := η) (g := θ)
  map₂_smul {a b f g} r η := (chevHom a b).map_smul r η
  map₂_mem {a b f g p η} h := IsSuperfunctor.map_mem (F := chevHom a b) h
  map_comp f g := congrArg SOp.mk (chevHomObj_comp f g)
  map_id a := congrArg SOp.mk (chevHomObj_id a)
  map₂_whiskerLeft {a b c} f {g h} η :=
    sop_heq (chevHomObj_comp f _) (chevHomObj_comp f _) _ _ (chevHom_whiskerLeft f η)
  map₂_whiskerRight {a b c f g} η h :=
    sop_heq (chevHomObj_comp _ h) (chevHomObj_comp _ h) _ _ (chevHom_whiskerRight η h)
  map₂_associator f g h := by
    apply sop_heq
      ((chevHomObj_comp (f ≫ g) h).trans
        (congrArg (· ≫ chevHomObj h) (chevHomObj_comp f g)))
      ((chevHomObj_comp f (g ≫ h)).trans
        (congrArg (chevHomObj f ≫ ·) (chevHomObj_comp g h)))
    change SOp.unsop ((chevHom _ _).map (associator f g h).hom) =
      _ ≫ (associator (chevHomObj f) (chevHomObj g) (chevHomObj h)).inv ≫ _
    rw [chevHom_associator]
    simp only [TwoSupercategory.whiskerLeft_eqToHom k,
      TwoSupercategory.eqToHom_whiskerRight k, eqToHom_trans_assoc, eqToHom_trans]
  map₂_leftUnitor f := by
    apply sop_heq
      ((chevHomObj_comp (𝟙 _) f).trans
        (congrArg (· ≫ chevHomObj f) (chevHomObj_id _))) rfl
    change SOp.unsop ((chevHom _ _).map (leftUnitor f).hom) =
      _ ≫ (leftUnitor (chevHomObj f)).inv ≫ _
    rw [chevHom_leftUnitor]
    simp only [eqToHom_refl, TwoSupercategory.id_whiskerRight (R := k), Category.comp_id]
    exact (Category.id_comp _).symm
  map₂_rightUnitor f := by
    apply sop_heq
      ((chevHomObj_comp f (𝟙 _)).trans
        (congrArg (chevHomObj f ≫ ·) (chevHomObj_id _))) rfl
    change SOp.unsop ((chevHom _ _).map (rightUnitor f).hom) =
      _ ≫ (rightUnitor (chevHomObj f)).inv ≫ _
    rw [chevHom_rightUnitor]
    simp only [eqToHom_refl, TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp]
    exact (Category.id_comp _).symm

/-- The Chevalley involution `ω : 𝔘(𝔤) → 𝔘(𝔤)^{sop}` as a 2-superfunctor. -/
def chevalleyTwo : TwoSuperfunctor k (UGr D Sc sy hc) (TwoSOp k (UGr D Sc sy hc)) :=
  chevalleyStrictCore.toTwoSuperfunctor

/-- The composition and identity comparisons are equality isomorphisms. -/
theorem chevalleyTwo_isStrict : (chevalleyTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)).IsStrict :=
  chevalleyStrictCore.isStrict

private theorem eqToHom_degree {R : Type*} [CommRing R] {C : Type*} [Category C]
    [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C]
    {A B : C} (p : A = B) : eqToHom p ∈ degree (R := R) A B 0 := by
  subst B
  exact id_mem_degree A

/-- Integer degrees are unchanged and both comparisons have degree zero. -/
theorem chevalleyTwo_isGraded :
    (chevalleyTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)).IsGraded where
  map₂_mem_degree {a b f g n η} h := (chevHom_graded (sy := sy) (hc := hc) a b).map_mem_degree h
  mapComp_hom_mem_degree f g := by
    change eqToHom (congrArg SOp.mk (chevHomObj_comp f g)).symm ∈ _
    exact eqToHom_degree _
  mapId_hom_mem_degree a := by
    change eqToHom (congrArg SOp.mk (chevHomObj_id a)).symm ∈ _
    exact eqToHom_degree _

end OddMath.SKM
