import OddMath.SKM.Rho.Coherence
import StringDiagrams.Super.TwoFunctorStrict

/-!
# Target Coherence for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoTwo
open CategoryTheory StringDiagrams Presentation BicategoryStruct RhoWords RhoEvaluator
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

theorem eq_underlying {ν μ : X}
    {a b : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ} (h : a = b) :
    eqToHom h = eqToHom (congrArg (fun x => (pres D Sc).obj x.obj.obj.obj) h) := by
  cases h
  rfl

theorem rev_associator {Ω ν ξ μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) Ω ⟶ rhoObj ν)
    (b : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj ξ)
    (c : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ξ ⟶ rhoObj μ)
    (h : (a ≫ b) ≫ c = a ≫ b ≫ c) :
    (associator a b c).hom = eqToHom h := by
  rw [eq_underlying]
  rfl

theorem rev_associator_inv {Ω ν ξ μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) Ω ⟶ rhoObj ν)
    (b : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj ξ)
    (c : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ξ ⟶ rhoObj μ)
    (h : (a ≫ b) ≫ c = a ≫ b ≫ c) :
    (associator a b c).inv = eqToHom h.symm := by
  rw [eq_underlying]
  rfl

theorem rev_leftUnitor {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : 𝟙 _ ≫ a = a) : (leftUnitor a).hom = eqToHom h := by
  rw [eq_underlying]
  rfl

theorem rev_leftUnitor_inv {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : 𝟙 _ ≫ a = a) : (leftUnitor a).inv = eqToHom h.symm := by
  rw [eq_underlying]
  rfl

theorem rev_rightUnitor {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : a ≫ 𝟙 _ = a) : (rightUnitor a).hom = eqToHom h := by
  rw [eq_underlying]
  rfl

theorem rev_rightUnitor_inv {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : a ≫ 𝟙 _ = a) : (rightUnitor a).inv = eqToHom h.symm := by
  rw [eq_underlying]
  rfl

theorem source_assoc {a b c d : UGr D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : (f ≫ g) ≫ h = f ≫ g ≫ h :=
  Presentation.Bicat.Hom.ext (Obj.tensor_assoc f.obj g.obj h.obj)
theorem source_left {a b : UGr D Sc sy hc} (f : a ⟶ b) : 𝟙 a ≫ f = f :=
  Presentation.Bicat.Hom.ext (Obj.nil_tensor f.start_eq)
theorem source_right {a b : UGr D Sc sy hc} (f : a ⟶ b) : f ≫ 𝟙 b = f :=
  Presentation.Bicat.Hom.ext (Obj.tensor_nil f.obj b.region)

theorem target_assoc {a b c d : UGr D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (rhoMap f ≫ rhoMap g) ≫ rhoMap h = rhoMap f ≫ rhoMap g ≫ rhoMap h := by
  rw [← rhoMap_comp, ← rhoMap_comp, ← rhoMap_comp, ← rhoMap_comp, source_assoc]
theorem target_left {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    𝟙 (rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) a.region) ≫ rhoMap f = rhoMap f := by
  rw [← rhoMap_id, ← rhoMap_comp, source_left]
theorem target_right {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    rhoMap f ≫ 𝟙 (rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) b.region) = rhoMap f := by
  rw [← rhoMap_id, ← rhoMap_comp, source_right]

theorem source_assoc_hom {a b c d : UGr D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (associator f g h).hom = eqToHom (source_assoc f g h) := by
  have he : associator f g h = eqToIso (source_assoc f g h) :=
    Presentation.Bicat.isoOfEq_eq_eqToIso (Obj.tensor_assoc f.obj g.obj h.obj) _
  exact congrArg (fun x => x.hom) he
theorem source_left_hom {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    (leftUnitor f).hom = eqToHom (source_left f) := by
  have he : leftUnitor f = eqToIso (source_left f) :=
    Presentation.Bicat.isoOfEq_eq_eqToIso (a := 𝟙 a ≫ f) (b := f)
      (Obj.nil_tensor f.start_eq) _
  exact congrArg (fun x => x.hom) he
theorem source_right_hom {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    (rightUnitor f).hom = eqToHom (source_right f) := by
  have he : rightUnitor f = eqToIso (source_right f) :=
    Presentation.Bicat.isoOfEq_eq_eqToIso (Obj.tensor_nil f.obj b.region) _
  exact congrArg (fun x => x.hom) he

end OddMath.SKM.RhoTwo
