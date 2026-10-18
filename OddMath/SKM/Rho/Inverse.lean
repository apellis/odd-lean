import OddMath.SKM.Rho.Roundtrip

/-!
# Inverse for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
The inverse is obtained by horizontal super-reversal and replacing t by −t.
It preserves the integer grading.
-/

noncomputable section
namespace OddMath.SKM.RhoInverse
open CategoryTheory StringDiagrams BicategoryStruct RhoWords RhoTwo RhoExtension
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

private def reverseEnvelopeFunctor
    (F : TwoSuperfunctor k (Uqπ D Sc sy hc) (TwoSRev k (Uqπ D Sc sy hc))) :
    TwoSuperfunctor k (TwoSRev k (Uqπ D Sc sy hc)) (Uqπ D Sc sy hc) where
  obj a := (F.obj a.unrev).unrev
  map f := F.map f
  map₂ η := F.map₂ η
  map₂_id f := F.map₂_id f
  map₂_comp η θ := F.map₂_comp η θ
  map₂_add η θ := F.map₂_add η θ
  map₂_smul r η := F.map₂_smul r η
  map₂_mem h := F.map₂_mem h
  mapComp f g := F.mapComp g f
  mapId a := F.mapId a.unrev
  mapComp_hom_mem f g := F.mapComp_hom_mem g f
  mapId_hom_mem a := F.mapId_hom_mem a.unrev
  mapComp_naturality_left η g :=
    F.mapComp_naturality_right g η
  mapComp_naturality_right f _ _ η :=
    F.mapComp_naturality_left η f
  map₂_associator f g h := by
    have e := F.map₂_associator h g f
    change (F.mapComp h g).hom ▷ F.map f ≫ (F.mapComp (h ≫ g) f).hom ≫
        F.map₂ (associator (B := Uqπ D Sc sy hc) h g f).hom =
      (associator (B := TwoSRev k (Uqπ D Sc sy hc)) (F.map h) (F.map g) (F.map f)).hom ≫
        F.map h ◁ (F.mapComp g f).hom ≫ (F.mapComp h (g ≫ f)).hom
    apply (cancel_mono (F.map₂Iso (associator (B := Uqπ D Sc sy hc) h g f)).inv).mp
    dsimp only [TwoSuperfunctor.map₂Iso]
    simp only [Category.assoc, ← F.map₂_comp, Iso.hom_inv_id, F.map₂_id,
      Category.comp_id]
    rw [e]
    simp only [Iso.hom_inv_id_assoc]
  map₂_leftUnitor f := F.map₂_rightUnitor f
  map₂_rightUnitor f := F.map₂_leftUnitor f
def rhoInverse (t : k) (ht : t ^ 2 = -1) :
    TwoSuperfunctor k (TwoSRev k (Uqπ D Sc sy hc)) (Uqπ D Sc sy hc) :=
  reverseEnvelopeFunctor (rhoEnvelope (-t) (by simpa only [neg_sq] using ht))

private theorem reverseEnvelopeFunctor_isGraded
    (F : TwoSuperfunctor k (Uqπ D Sc sy hc) (TwoSRev k (Uqπ D Sc sy hc)))
    (hF : F.IsGraded) : (reverseEnvelopeFunctor F).IsGraded where
  map₂_mem_degree h := hF.map₂_mem_degree h
  mapComp_hom_mem_degree f g := hF.mapComp_hom_mem_degree g f
  mapId_hom_mem_degree a := hF.mapId_hom_mem_degree a.unrev

theorem rhoInverse_isGraded (t : k) (ht : t ^ 2 = -1) :
    (rhoInverse (sy := sy) (hc := hc) t ht).IsGraded :=
  reverseEnvelopeFunctor_isGraded _
    (rhoEnvelope_isGraded (-t) (by simpa only [neg_sq] using ht))

theorem rhoInverse_obj (t : k) (ht : t ^ 2 = -1) (a : TwoSRev k (Uqπ D Sc sy hc)) :
    (rhoInverse t ht).obj a = a.unrev := rfl

theorem rhoInverse_map (t : k) (ht : t ^ 2 = -1)
    {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) :
    (rhoInverse t ht).map f =
      (rhoEnvelope (-t) (by simpa only [neg_sq] using ht)).map f := rfl

theorem rhoInverse_map₂ (t : k) (ht : t ^ 2 = -1)
    {a b : TwoSRev k (Uqπ D Sc sy hc)} {f g : a ⟶ b} (η : f ⟶ g) :
    (rhoInverse t ht).map₂ η =
      (rhoEnvelope (-t) (by simpa only [neg_sq] using ht)).map₂ η := rfl

theorem rhoInverse_mapComp (t : k) (ht : t ^ 2 = -1)
    {a b c : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) (g : b ⟶ c) :
    (rhoInverse t ht).mapComp f g =
      (rhoEnvelope (-t) (by simpa only [neg_sq] using ht)).mapComp g f := rfl

theorem rhoInverse_mapId (t : k) (ht : t ^ 2 = -1) (a : TwoSRev k (Uqπ D Sc sy hc)) :
    (rhoInverse t ht).mapId a =
      (rhoEnvelope (-t) (by simpa only [neg_sq] using ht)).mapId a.unrev := rfl

theorem rhoInverse_rho_map (t : k) (ht : t ^ 2 = -1)
    {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    (rhoInverse t ht).map ((rhoEnvelope t ht).map f) = f :=
  rhoEnvelope_map_roundtrip t (-t) ht (by simpa only [neg_sq] using ht) f

theorem rho_rhoInverse_map (t : k) (ht : t ^ 2 = -1)
    {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) :
    (rhoEnvelope t ht).map ((rhoInverse t ht).map f) = f :=
  rhoEnvelope_map_roundtrip (-t) t (by simpa only [neg_sq] using ht) ht f
end OddMath.SKM.RhoInverse
