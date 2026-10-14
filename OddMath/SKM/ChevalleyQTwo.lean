/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQHom
import OddMath.SKM.ChevalleyTwo

/-!
# The Chevalley involution on the `Q`-envelope

[BE2] J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Lemma 9.1 and
Proposition 9.3, `Q`-part: the strict 2-superfunctor `𝔘(𝔤)_q → (𝔘(𝔤)_q)^{sop}`
(`chevalleyQTwo`), `λ ↦ -λ`, `Qᵐ F ↦ Q⁻ᵐ ω(F)`, `ω` on 2-morphisms (`chevalleyQTwo_isStrict`).
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory BicategoryStruct
universe u v w

private theorem q_sop_heq {k : Type*} [CommRing k] {C : Type*} [Category C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A B A' B' : QEnvelope k C} (p : A = A') (q : B = B')
    (η : (SOp.mk A : SOp k (QEnvelope k C)) ⟶ SOp.mk B)
    (θ : (SOp.mk A' : SOp k (QEnvelope k C)) ⟶ SOp.mk B')
    (h : HEq (SOp.mk' (R := k) (X := SOp.mk A.obj) (Y := SOp.mk B.obj)
        (QEnvelope.toHom (SOp.unsop η)))
      (SOp.mk' (R := k) (X := SOp.mk A'.obj) (Y := SOp.mk B'.obj)
        (QEnvelope.toHom (SOp.unsop θ)))) : HEq η θ := by
  subst A' B'
  apply heq_of_eq
  apply SOp.hom_ext
  exact congrArg (SOp.unsop (C := C)) (eq_of_heq h)

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

/-- `ω` on `Q`-shifted 1-morphisms: `Qᵐ F ↦ Q⁻ᵐ ω(F)`. -/
def chevQObj {a b : QTwoEnvelope k (UGr D Sc sy hc)} (f : a ⟶ b) :
    (⟨negWeight a.as⟩ : QTwoEnvelope k (UGr D Sc sy hc)) ⟶ ⟨negWeight b.as⟩ :=
  ⟨-f.shift, chevHomObj f.obj⟩

/-- `chevQObj` respects horizontal composition. -/
theorem chevQObj_comp {a b c : QTwoEnvelope k (UGr D Sc sy hc)}
    (f : a ⟶ b) (g : b ⟶ c) : chevQObj (f ≫ g) = chevQObj f ≫ chevQObj g := by
  apply QEnvelope.ext
  · exact neg_add f.shift g.shift
  · exact chevHomObj_comp f.obj g.obj

/-- Shift negation preserves the identity word and its zero shift. -/
theorem chevQObj_id (a : QTwoEnvelope k (UGr D Sc sy hc)) :
    chevQObj (𝟙 a) = 𝟙 (⟨negWeight a.as⟩ : QTwoEnvelope k (UGr D Sc sy hc)) := by
  apply QEnvelope.ext
  · exact neg_zero
  · exact chevHomObj_id a.as

/-- Strict data of `ω` on the `Q`-envelope. -/
def chevalleyQStrictCore :
    TwoSuperfunctor.StrictCore k (QTwoEnvelope k (UGr D Sc sy hc))
      (TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) where
  obj a := ⟨⟨negWeight a.as⟩⟩
  map f := ⟨chevQObj f⟩
  map₂ {a b f g} η := (chevQHom a.as b.as).map η
  map₂_id {a b} f := (chevQHom a.as b.as).map_id f
  map₂_comp {a b f g h} η θ := (chevQHom a.as b.as).map_comp η θ
  map₂_add {a b f g} η θ := (chevQHom a.as b.as).map_add (f := η) (g := θ)
  map₂_smul {a b f g} r η := (chevQHom a.as b.as).map_smul r η
  map₂_mem {a b f g p η} h := (chevQHom_super a.as b.as).map_mem h
  map_comp f g := congrArg SOp.mk (chevQObj_comp f g)
  map_id a := congrArg SOp.mk (chevQObj_id a)
  map₂_whiskerLeft {a b c} f {g h} η := by
    apply q_sop_heq (chevQObj_comp f g) (chevQObj_comp f h)
    exact chevalleyStrictCore.map₂_whiskerLeft f.obj (QEnvelope.toHom η)
  map₂_whiskerRight {a b c f g} η h := by
    apply q_sop_heq (chevQObj_comp f h) (chevQObj_comp g h)
    exact chevalleyStrictCore.map₂_whiskerRight (QEnvelope.toHom η) h.obj
  map₂_associator f g h := by
    apply q_sop_heq
      ((chevQObj_comp (f ≫ g) h).trans
        (congrArg (· ≫ chevQObj h) (chevQObj_comp f g)))
      ((chevQObj_comp f (g ≫ h)).trans
        (congrArg (chevQObj f ≫ ·) (chevQObj_comp g h)))
    exact chevalleyStrictCore.map₂_associator f.obj g.obj h.obj
  map₂_leftUnitor f := by
    apply q_sop_heq
      ((chevQObj_comp (𝟙 _) f).trans
        (congrArg (· ≫ chevQObj f) (chevQObj_id _))) rfl
    exact chevalleyStrictCore.map₂_leftUnitor f.obj
  map₂_rightUnitor f := by
    apply q_sop_heq
      ((chevQObj_comp f (𝟙 _)).trans
        (congrArg (chevQObj f ≫ ·) (chevQObj_id _))) rfl
    exact chevalleyStrictCore.map₂_rightUnitor f.obj

/-- The Chevalley involution `𝔘(𝔤)_q → (𝔘(𝔤)_q)^{sop}`. -/
def chevalleyQTwo :
    TwoSuperfunctor k (QTwoEnvelope k (UGr D Sc sy hc))
      (TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))) :=
  chevalleyQStrictCore.toTwoSuperfunctor

/-- All global comparisons are equality isomorphisms. -/
theorem chevalleyQTwo_isStrict :
    (chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)).IsStrict :=
  chevalleyQStrictCore.isStrict
end OddMath.SKM
