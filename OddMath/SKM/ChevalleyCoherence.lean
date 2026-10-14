/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyWhiskering
import StringDiagrams.Super.TwoFunctorStrict

/-!
# Coherence of the Chevalley involution on `𝔘(𝔤)`

[BE2] J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition
3.5 and §9: the Chevalley involution `ω` sends the associator and unitors of `UGr` to the
inverse associator and unitors of the target, up to the equalities `chevHomObj_comp` and
`chevHomObj_id` (`chevHom_associator`, `chevHom_leftUnitor`, `chevHom_rightUnitor`). Input for
the strict 2-superfunctor `chevalleyTwo`.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

private theorem chev_eqToHom {a b : UGr D Sc sy hc} {f g : a ⟶ b} (e : f = g) :
    SOp.unsop ((chevHom a b).map (eqToHom e)) =
      eqToHom (congrArg chevHomObj e.symm) := by
  subst g
  exact congrArg SOp.unsop ((chevHom a b).map_id f)

private theorem assoc_eq {a b c d : UGr D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : (f ≫ g) ≫ h = f ≫ g ≫ h := by
  apply Presentation.Bicat.Hom.ext
  exact Obj.tensor_assoc f.obj g.obj h.obj

private theorem left_eq {a b : UGr D Sc sy hc} (f : a ⟶ b) : 𝟙 a ≫ f = f := by
  apply Presentation.Bicat.Hom.ext
  exact Obj.nil_tensor f.start_eq

private theorem right_eq {a b : UGr D Sc sy hc} (f : a ⟶ b) : f ≫ 𝟙 b = f := by
  apply Presentation.Bicat.Hom.ext
  exact Obj.tensor_nil f.obj b.region

private theorem assoc_iso {a b c d : UGr D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    associator f g h = eqToIso (assoc_eq f g h) :=
  Presentation.Bicat.isoOfEq_eq_eqToIso (Obj.tensor_assoc f.obj g.obj h.obj) _

private theorem left_iso {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    leftUnitor f = eqToIso (left_eq f) :=
  Presentation.Bicat.isoOfEq_eq_eqToIso (a := 𝟙 a ≫ f) (b := f)
    (Obj.nil_tensor f.start_eq) (left_eq f)

private theorem right_iso {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    rightUnitor f = eqToIso (right_eq f) :=
  Presentation.Bicat.isoOfEq_eq_eqToIso (Obj.tensor_nil f.obj b.region) _

/-- `ω` on the associator, with the composition comparisons explicit. -/
theorem chevHom_associator {a b c d : UGr D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    SOp.unsop ((chevHom a d).map (associator f g h).hom) =
      eqToHom (chevHomObj_comp f (g ≫ h)) ≫
        (chevHomObj f ◁ eqToHom (chevHomObj_comp g h)) ≫
        (associator (chevHomObj f) (chevHomObj g) (chevHomObj h)).inv ≫
        (eqToHom (chevHomObj_comp f g).symm ▷ chevHomObj h) ≫
        eqToHom (chevHomObj_comp (f ≫ g) h).symm := by
  simp only [assoc_iso, eqToIso.hom, eqToIso.inv, chev_eqToHom,
    TwoSupercategory.whiskerLeft_eqToHom k, TwoSupercategory.eqToHom_whiskerRight k,
    eqToHom_trans]

/-- `ω` on the left unitor, including the identity comparison. -/
theorem chevHom_leftUnitor {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    SOp.unsop ((chevHom a b).map (leftUnitor f).hom) =
      (leftUnitor (chevHomObj f)).inv ≫
        (eqToHom (chevHomObj_id a).symm ▷ chevHomObj f) ≫
        eqToHom (chevHomObj_comp (𝟙 a) f).symm := by
  simp only [left_iso, eqToIso.hom, eqToIso.inv, chev_eqToHom,
    TwoSupercategory.eqToHom_whiskerRight k, eqToHom_trans]

/-- `ω` on the right unitor, including the identity comparison. -/
theorem chevHom_rightUnitor {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    SOp.unsop ((chevHom a b).map (rightUnitor f).hom) =
      (rightUnitor (chevHomObj f)).inv ≫
        (chevHomObj f ◁ eqToHom (chevHomObj_id b).symm) ≫
        eqToHom (chevHomObj_comp f (𝟙 b)).symm := by
  simp only [right_iso, eqToIso.hom, eqToIso.inv, chev_eqToHom,
    TwoSupercategory.whiskerLeft_eqToHom k, eqToHom_trans]
end OddMath.SKM
