/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.ChevalleyPlacement

/-!
# Chevalley compatibility with actual whiskering

`chevHom_whiskerLeft` and `chevHom_whiskerRight` identify the original Chevalley
hom functor on the actual `UGr` whiskerings, with reversed endpoints and explicit
composition comparisons. They hold for arbitrary quotient 2-morphisms, without
a homogeneity hypothesis on those morphisms, and supply the whiskering equations
for the remaining global 2-superfunctor construction. These are prerequisites
for [BE2] §9, Proposition 9.3, not the global coherence or shifted-envelope extension.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

private theorem omega_transport {A A' B B' : Obj (sig D)}
    (ha : A = A') (hb : B' = B)
    (x : (pres D Sc).obj A' ⟶ (pres D Sc).obj B') :
    SOp.unsop ((omega Sc).map
      (eqToHom (congrArg (pres D Sc).obj ha) ≫ x ≫
        eqToHom (congrArg (pres D Sc).obj hb))) =
      eqToHom (congrArg (fun z => (pres D Sc).obj ((chevMap D).obj z)) hb.symm) ≫
        SOp.unsop ((omega Sc).map x) ≫
          eqToHom (congrArg (fun z => (pres D Sc).obj ((chevMap D).obj z)) ha.symm) := by
  subst A B
  change SOp.unsop ((omega Sc).map (𝟙 _ ≫ x ≫ 𝟙 _)) =
    𝟙 _ ≫ SOp.unsop ((omega Sc).map x) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id, Category.id_comp, Category.comp_id]

private theorem transport_paste {C : Type*} [Category C]
    {A A₁ A₂ S T B₁ B₂ B : C}
    (p : A = A₁) (q : A₁ = S) (r : T = B₁) (s : B₁ = B)
    (p' : A = A₂) (q' : A₂ = S) (r' : T = B₂) (s' : B₂ = B) (z : S ⟶ T) :
    eqToHom p ≫ (eqToHom q ≫ z ≫ eqToHom r) ≫ eqToHom s =
      eqToHom p' ≫ (eqToHom q' ≫ z ≫ eqToHom r') ≫ eqToHom s' := by
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

private theorem omega_wL {A B B' : Obj (sig D)}
    (x : (pres D Sc).obj B ⟶ (pres D Sc).obj B') (h : A.Composable B) :
    SOp.unsop ((omega Sc).map ((pres D Sc).wL A x)) =
      eqToHom (congrArg (pres D Sc).obj ((chevMap D).obj_tensor A B')) ≫
        (pres D Sc).wL ((chevMap D).obj A) (SOp.unsop ((omega Sc).map x)) ≫
          eqToHom (congrArg (pres D Sc).obj ((chevMap D).obj_tensor A B)).symm := by
  unfold Presentation.wL
  rw [omega_transport (Obj.tensor_eq_whisker_nil A B) (Obj.tensor_eq_whisker_nil A B').symm]
  erw [omega_whisk x (u := A) (v := []) ⟨h.left_wf, h.endR_eq, trivial⟩]
  exact transport_paste _ _ _ _ _ _ _ _ _

private theorem omega_wRAt {A A' B : Obj (sig D)} {r : X}
    (x : (pres D Sc).obj A ⟶ (pres D Sc).obj A') (h : A.Composable B)
    (ha : A.start = r) (ha' : A'.start = r) :
    SOp.unsop ((omega Sc).map ((pres D Sc).wRAt r x B ha ha')) =
      eqToHom (congrArg (pres D Sc).obj ((chevMap D).obj_tensor A' B)) ≫
        (pres D Sc).wRAt (-r) (SOp.unsop ((omega Sc).map x)) ((chevMap D).obj B)
          (congrArg (fun z : X => -z) ha') (congrArg (fun z : X => -z) ha) ≫
          eqToHom (congrArg (pres D Sc).obj ((chevMap D).obj_tensor A B)).symm := by
  unfold Presentation.wRAt
  rw [omega_transport (Obj.tensor_eq_whisker_nil_of_start B ha)
    (Obj.tensor_eq_whisker_nil_of_start B ha').symm]
  erw [omega_whisk x (u := Obj.nil r) (v := B.word) ⟨trivial, ha.symm, h.ok_endR⟩]
  exact transport_paste _ _ _ _ _ _ _ _ _

variable {sy : Symmetrizer D} {hc : Sc.Homogeneous}

private theorem hom_eqToHom {a b : UGr D Sc sy hc} {f g : a ⟶ b} (h : f = g) :
    (eqToHom h : f ⟶ g) =
      (eqToHom (congrArg (fun z : a ⟶ b => (pres D Sc).obj z.obj) h) :
        (pres D Sc).obj f.obj ⟶ (pres D Sc).obj g.obj) := by
  subst g
  rfl

/-- Left whiskering compatibility on arbitrary actual quotient 2-morphisms. -/
theorem chevHom_whiskerLeft {a b c : UGr D Sc sy hc}
    (f : a ⟶ b) {g h : b ⟶ c} (x : g ⟶ h) :
    SOp.unsop (C := (negWeight a ⟶ negWeight c)) ((chevHom a c).map (f ◁ x)) =
      eqToHom (chevHomObj_comp f h) ≫
        (chevHomObj f ◁ SOp.unsop (C := (negWeight b ⟶ negWeight c)) ((chevHom b c).map x)) ≫
          eqToHom (chevHomObj_comp f g).symm := by
  simp only [hom_eqToHom]
  change SOp.unsop ((omega Sc).map ((pres D Sc).wL f.obj x)) =
    eqToHom (congrArg (pres D Sc).obj ((chevMap D).obj_tensor f.obj h.obj)) ≫
      (pres D Sc).wL ((chevMap D).obj f.obj) (SOp.unsop ((omega Sc).map x)) ≫
        eqToHom (congrArg (pres D Sc).obj ((chevMap D).obj_tensor f.obj g.obj)).symm
  exact omega_wL x (f.composable g)

/-- Right whiskering compatibility on arbitrary actual quotient 2-morphisms. -/
theorem chevHom_whiskerRight {a b c : UGr D Sc sy hc}
    {f f' : a ⟶ b} (x : f ⟶ f') (g : b ⟶ c) :
    SOp.unsop (C := (negWeight a ⟶ negWeight c)) ((chevHom a c).map (x ▷ g)) =
      eqToHom (chevHomObj_comp f' g) ≫
        (SOp.unsop (C := (negWeight a ⟶ negWeight b)) ((chevHom a b).map x) ▷ chevHomObj g) ≫
          eqToHom (chevHomObj_comp f g).symm := by
  simp only [hom_eqToHom]
  change SOp.unsop ((omega Sc).map
    ((pres D Sc).wRAt a.region x g.obj f.start_eq f'.start_eq)) =
    eqToHom (congrArg (pres D Sc).obj ((chevMap D).obj_tensor f'.obj g.obj)) ≫
      (pres D Sc).wRAt (-(show X from a.region))
        (SOp.unsop ((omega Sc).map x)) ((chevMap D).obj g.obj)
        (congrArg (fun z : X => -z) f'.start_eq)
        (congrArg (fun z : X => -z) f.start_eq) ≫
        eqToHom (congrArg (pres D Sc).obj ((chevMap D).obj_tensor f.obj g.obj)).symm
  exact omega_wRAt x (f.composable g) f.start_eq f'.start_eq

end OddMath.SKM
