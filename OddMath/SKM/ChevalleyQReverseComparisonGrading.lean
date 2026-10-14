/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseReflection

/-!
# Grading of the comparisons of `G_q`

The composition and identity comparisons of `G_q` are even of degree zero.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory BicategoryStruct
  TwoSupercategory GradedTwoSupercategory
universe u v w
private theorem eqToHom_degree {R : Type*} [CommRing R] {C : Type*} [Category C]
    [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C]
    {A B : C} (p : A = B) : eqToHom p ∈ degree (R := R) A B 0 := by
  subst B
  exact id_mem_degree A
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "B" => TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))
local notation "r" => chevalleyQReverseObj (D := D) (Sc := Sc) (sy := sy) (hc := hc)

/-- The reverse composition comparison has degree zero. -/
theorem chevalleyQReverseMapComp_degree {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (chevalleyQReverseMapComp f g).hom ∈ degree (R := k) _ _ 0 := by
  apply q_bundled_reflect_degree (r a) (r c)
  rw [chevalleyQReverseMapComp_image]
  let A : B := (F).obj (r a)
  let M : B := (F).obj (r b)
  let C : B := (F).obj (r c)
  let x : A ⟶ M := (F).map ((chevalleyQReverseHom a b).obj f)
  let y : M ⟶ C := (F).map ((chevalleyQReverseHom b c).obj g)
  let x' : A ⟶ M := (chevalleyQReverseTransport a b).obj f
  let y' : M ⟶ C := (chevalleyQReverseTransport b c).obj g
  have h₁ : ((F).mapComp ((chevalleyQReverseHom a b).obj f)
      ((chevalleyQReverseHom b c).obj g)).inv ∈ degree (R := k) (C := A ⟶ C) _ _ 0 := by
    simpa only [neg_zero] using inv_mem_degree (C := A ⟶ C) _
      (chevalleyQTwo_isGraded.mapComp_hom_mem_degree
        ((chevalleyQReverseHom a b).obj f) ((chevalleyQReverseHom b c).obj g))
  have h₂ : (chevalleyQReverseHomCounit f).hom ▷ y ∈
      degree (R := k) (C := A ⟶ C) (x ≫ y) (x' ≫ y) 0 :=
    whiskerRight_mem_degree (R := k) (a := A) (b := M) (c := C) y
      (chevalleyQReverseHomCounit_degree f)
  have h₃ : x' ◁ (chevalleyQReverseHomCounit g).hom ∈
      degree (R := k) (C := A ⟶ C) (x' ≫ y) (x' ≫ y') 0 :=
    whiskerLeft_mem_degree (R := k) (a := A) (b := M) (c := C) x'
      (chevalleyQReverseHomCounit_degree g)
  have h₄ := eqToHom_degree (R := k) (C := A ⟶ C)
    (chevalleyQReverseTransport_comp f g).symm
  have h₅ : (chevalleyQReverseHomCounit (f ≫ g)).inv ∈
      degree (R := k) (C := A ⟶ C) _ _ 0 := by
    simpa only [neg_zero] using inv_mem_degree (C := A ⟶ C) _
      (chevalleyQReverseHomCounit_degree (f ≫ g))
  change (((F).mapComp ((chevalleyQReverseHom a b).obj f)
    ((chevalleyQReverseHom b c).obj g)).inv ≫
    (chevalleyQReverseHomCounit f).hom ▷ y ≫
    x' ◁ (chevalleyQReverseHomCounit g).hom ≫
    eqToHom (chevalleyQReverseTransport_comp f g).symm ≫
    (chevalleyQReverseHomCounit (f ≫ g)).inv) ∈ degree (R := k) (C := A ⟶ C) _ _ 0
  simpa only [add_zero] using
    comp_mem_degree (C := A ⟶ C) h₁ (comp_mem_degree (C := A ⟶ C) h₂
      (comp_mem_degree (C := A ⟶ C) h₃ (comp_mem_degree (C := A ⟶ C) h₄ h₅)))

/-- The reverse identity comparison has degree zero. -/
theorem chevalleyQReverseMapId_degree (a : B) :
    (chevalleyQReverseMapId a).hom ∈ degree (R := k) _ _ 0 := by
  apply q_bundled_reflect_degree (r a) (r a)
  rw [chevalleyQReverseMapId_image]
  let A : B := (F).obj (r a)
  have h₁ : ((F).mapId (r a)).inv ∈ degree (R := k) (C := A ⟶ A) _ _ 0 := by
    simpa only [neg_zero] using inv_mem_degree (C := A ⟶ A) _
      (chevalleyQTwo_isGraded.mapId_hom_mem_degree (r a))
  have h₂ := eqToHom_degree (R := k) (C := A ⟶ A)
    (chevalleyQReverseTransport_id a).symm
  have h₃ : (chevalleyQReverseHomCounit (𝟙 a)).inv ∈
      degree (R := k) (C := A ⟶ A) _ _ 0 := by
    simpa only [neg_zero] using inv_mem_degree (C := A ⟶ A) _
      (chevalleyQReverseHomCounit_degree (𝟙 a))
  change (((F).mapId (r a)).inv ≫ eqToHom (chevalleyQReverseTransport_id a).symm ≫
    (chevalleyQReverseHomCounit (𝟙 a)).inv) ∈ degree (R := k) (C := A ⟶ A) _ _ 0
  simpa only [add_zero] using
    comp_mem_degree (C := A ⟶ A) h₁ (comp_mem_degree (C := A ⟶ A) h₂ h₃)

/-- The reverse composition comparison is even. -/
theorem chevalleyQReverseMapComp_even {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (chevalleyQReverseMapComp f g).hom ∈ parity (R := k) _ _ 0 := by
  apply q_bundled_reflect_parity (r a) (r c)
  rw [chevalleyQReverseMapComp_image]
  let A : B := (F).obj (r a)
  let M : B := (F).obj (r b)
  let C : B := (F).obj (r c)
  let x : A ⟶ M := (F).map ((chevalleyQReverseHom a b).obj f)
  let y : M ⟶ C := (F).map ((chevalleyQReverseHom b c).obj g)
  let x' : A ⟶ M := (chevalleyQReverseTransport a b).obj f
  let y' : M ⟶ C := (chevalleyQReverseTransport b c).obj g
  have h₁ := inv_mem (C := A ⟶ C)
    ((F).mapComp ((chevalleyQReverseHom a b).obj f) ((chevalleyQReverseHom b c).obj g))
    ((F).mapComp_hom_mem _ _)
  have h₂ : (chevalleyQReverseHomCounit f).hom ▷ y ∈
      parity (R := k) (C := A ⟶ C) (x ≫ y) (x' ≫ y) 0 :=
    whiskerRight_mem (R := k) (a := A) (b := M) (c := C) y
      (chevalleyQReverseHomCounit_even f)
  have h₃ : x' ◁ (chevalleyQReverseHomCounit g).hom ∈
      parity (R := k) (C := A ⟶ C) (x' ≫ y) (x' ≫ y') 0 :=
    whiskerLeft_mem (R := k) (a := A) (b := M) (c := C) x'
      (chevalleyQReverseHomCounit_even g)
  have h₄ := eqToHom_mem (R := k) (C := A ⟶ C)
    (chevalleyQReverseTransport_comp f g).symm
  have h₅ := inv_mem (C := A ⟶ C) _ (chevalleyQReverseHomCounit_even (f ≫ g))
  change (((F).mapComp ((chevalleyQReverseHom a b).obj f)
    ((chevalleyQReverseHom b c).obj g)).inv ≫
    (chevalleyQReverseHomCounit f).hom ▷ y ≫
    x' ◁ (chevalleyQReverseHomCounit g).hom ≫
    eqToHom (chevalleyQReverseTransport_comp f g).symm ≫
    (chevalleyQReverseHomCounit (f ≫ g)).inv) ∈ parity (R := k) (C := A ⟶ C) _ _ 0
  simpa only [add_zero] using
    comp_mem (C := A ⟶ C) h₁ (comp_mem (C := A ⟶ C) h₂
      (comp_mem (C := A ⟶ C) h₃ (comp_mem (C := A ⟶ C) h₄ h₅)))

/-- The reverse identity comparison is even. -/
theorem chevalleyQReverseMapId_even (a : B) :
    (chevalleyQReverseMapId a).hom ∈ parity (R := k) _ _ 0 := by
  apply q_bundled_reflect_parity (r a) (r a)
  rw [chevalleyQReverseMapId_image]
  let A : B := (F).obj (r a)
  have h₁ := inv_mem (C := A ⟶ A) ((F).mapId (r a)) ((F).mapId_hom_mem (r a))
  have h₂ := eqToHom_mem (R := k) (C := A ⟶ A) (chevalleyQReverseTransport_id a).symm
  have h₃ := inv_mem (C := A ⟶ A) _ (chevalleyQReverseHomCounit_even (𝟙 a))
  change (((F).mapId (r a)).inv ≫ eqToHom (chevalleyQReverseTransport_id a).symm ≫
    (chevalleyQReverseHomCounit (𝟙 a)).inv) ∈ parity (R := k) (C := A ⟶ A) _ _ 0
  simpa only [add_zero] using comp_mem (C := A ⟶ A) h₁ (comp_mem (C := A ⟶ A) h₂ h₃)
end OddMath.SKM
