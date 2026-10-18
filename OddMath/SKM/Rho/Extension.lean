import OddMath.SKM.Rho.TwoFunctor

/-!
# Extension for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
The corrected functor extends to arbitrary Q/Π shifts by Lemma 9.6.
Its action preserves the integer grading.
-/

noncomputable section
namespace OddMath.SKM.RhoExtension
open CategoryTheory StringDiagrams BicategoryStruct RhoWords RhoTwo
  Supercategory QPiSupercategory PiSupercategory Envelope
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

def rhoEnvelope (t : k) (ht : t ^ 2 = -1) :
    TwoSuperfunctor k (Uqπ D Sc sy hc) (TwoSRev k (Uqπ D Sc sy hc)) :=
  extendEnvelopeSRev (rhoTwo t ht)

theorem rhoEnvelope_isGraded (t : k) (ht : t ^ 2 = -1) :
    (rhoEnvelope (sy := sy) (hc := hc) t ht).IsGraded :=
  extendEnvelopeSRev_isGraded _ (rhoTwo_isGraded t ht)

theorem rhoEnvelope_restrict (t : k) (ht : t ^ 2 = -1) :
    (QPiTwoEnvelope.twoJ k (UGr D Sc sy hc)).comp (rhoEnvelope t ht) = rhoTwo t ht :=
  twoJ_comp_extendEnvelopeSRev _

theorem rhoEnvelope_obj (t : k) (ht : t ^ 2 = -1) (a : Uqπ D Sc sy hc) :
    (rhoEnvelope t ht).obj a = rhoObj (D := D) (Sc := Sc) a.as.as.region := rfl

local instance (a b : TwoSRev k (Uqπ D Sc sy hc)) : QPiSupercategory k (a ⟶ b) :=
  QPiTwoSupercategory.homQPiLeft a b

theorem rhoEnvelope_map (t : k) (ht : t ^ 2 = -1)
    {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    (rhoEnvelope t ht).map f = piPow k f.par (qPow k f.obj.shift (rhoMap f.obj.obj)) := rfl

theorem rhoEnvelope_map₂ (t : k) (ht : t ^ 2 = -1)
    {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g) :
    (rhoEnvelope t ht).map₂ η =
      (ζPow k f.par _).hom ≫ ((σPow k f.obj.shift (rhoMap f.obj.obj)).hom ≫
        rhoMap₂ t ht f.obj.obj g.obj.obj (QPiTwoEnvelope.toHom η) ≫
          (σPow k g.obj.shift (rhoMap g.obj.obj)).inv) ≫ (ζPow k g.par _).inv := rfl

theorem rhoEnvelope_mapComp_hom (t : k) (ht : t ^ 2 = -1)
    {a b c : Uqπ D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    ((rhoEnvelope t ht).mapComp f g).hom = sign k (f.par * g.par) •
      ((ζPow k f.par _).hom ▷ (rhoEnvelope t ht).map g ≫
        qPow k f.obj.shift (rhoMap f.obj.obj) ◁ (ζPow k g.par _).hom ≫
        ((σPow k f.obj.shift (rhoMap f.obj.obj)).hom ▷ qPow k g.obj.shift (rhoMap g.obj.obj) ≫
          rhoMap f.obj.obj ◁ (σPow k g.obj.shift (rhoMap g.obj.obj)).hom ≫
          eqToHom (rhoMap_comp f.obj.obj g.obj.obj).symm ≫
          (σPow k (f.obj.shift + g.obj.shift) (rhoMap (f.obj.obj ≫ g.obj.obj))).inv) ≫
        (ζPow k (f.par + g.par) _).inv) := rfl

theorem rhoEnvelope_mapComp_inv (t : k) (ht : t ^ 2 = -1)
    {a b c : Uqπ D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    ((rhoEnvelope t ht).mapComp f g).inv = sign k (f.par * g.par) •
      ((ζPow k (f.par + g.par) _).hom ≫
        ((σPow k (f.obj.shift + g.obj.shift) (rhoMap (f.obj.obj ≫ g.obj.obj))).hom ≫
          eqToHom (rhoMap_comp f.obj.obj g.obj.obj) ≫
          rhoMap f.obj.obj ◁ (σPow k g.obj.shift (rhoMap g.obj.obj)).inv ≫
          (σPow k f.obj.shift (rhoMap f.obj.obj)).inv ▷ qPow k g.obj.shift (rhoMap g.obj.obj)) ≫
        qPow k f.obj.shift (rhoMap f.obj.obj) ◁ (ζPow k g.par _).inv ≫
        (ζPow k f.par _).inv ▷ (rhoEnvelope t ht).map g) := rfl

theorem rhoEnvelope_mapId (t : k) (ht : t ^ 2 = -1) (a : Uqπ D Sc sy hc) :
    (rhoEnvelope t ht).mapId a = eqToIso (rhoMap_id a.as.as).symm := rfl

theorem rhoEnvelope_map_J (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    (rhoEnvelope t ht).map (QPiTwoEnvelope.Jm (R := k) f) = rhoMap f := rfl

theorem rhoEnvelope_map₂_J (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g) :
    (rhoEnvelope t ht).map₂ (QPiTwoEnvelope.J2 (R := k) η) = rhoMap₂ t ht f g η :=
  extendEnvelopeSRev_map₂_J (rhoTwo t ht) η

theorem rhoEnvelope_mapComp_J (t : k) (ht : t ^ 2 = -1)
    {a b c : UGr D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    (rhoEnvelope t ht).mapComp (QPiTwoEnvelope.Jm (R := k) f) (QPiTwoEnvelope.Jm g) =
      eqToIso (rhoMap_comp f g).symm := by
  apply Iso.ext
  exact extendEnvelopeSRev_mapComp_J (rhoTwo t ht) f g

theorem rhoEnvelope_map_QPi (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    (rhoEnvelope t ht).map (⟨1, ⟨1, f⟩⟩ : (⟨⟨a⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨b⟩⟩) =
      (rhoMap f ≫ QPiTwoSupercategory.q (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)) (rhoObj b.region)) ≫
        PiTwoSupercategory.pi (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)) (rhoObj b.region) := rfl

theorem rhoEnvelope_map_Qinv (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    (rhoEnvelope t ht).map (⟨0, ⟨-1, f⟩⟩ : (⟨⟨a⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨b⟩⟩) =
      rhoMap f ≫ QPiTwoSupercategory.qinv (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)) (rhoObj b.region) := rfl
end OddMath.SKM.RhoExtension
