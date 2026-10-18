import OddMath.SKM.Rho.QuotientRoundtrips
import OddMath.SKM.Rho.EnvelopeRoundtrips

/-!
# Map Inverses for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
Both map₂ inverse identities hold for arbitrary Q/Π shifts and unrestricted
2-morphisms, with no quotient-roundtrip premise.
-/

noncomputable section
namespace OddMath.SKM.RhoMapInverses
open CategoryTheory StringDiagrams BicategoryStruct RhoWords RhoTwo RhoExtension RhoInverse
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

theorem rhoEnvelope_bare_roundtrip (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g) :
    HEq ((rhoEnvelope (-t) (by simpa only [neg_sq] using ht)).map₂
      ((rhoEnvelope t ht).map₂ (QPiTwoEnvelope.J2 (R := k) η))) η := by
  have h := RhoQuotientRoundtrips.rhoForwardInverse_word t ht f g η
  rw [rhoInverse_map₂] at h
  exact h

theorem rhoEnvelope_bare_roundtrip_reverse (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g) :
    HEq ((rhoEnvelope t ht).map₂
      ((rhoEnvelope (-t) (by simpa only [neg_sq] using ht)).map₂
        (QPiTwoEnvelope.J2 (R := k) η))) η := by
  have h := rhoEnvelope_bare_roundtrip (-t) (by simpa only [neg_sq] using ht) η
  have e : rhoEnvelope (sy := sy) (hc := hc) (-(-t))
      (by simpa only [neg_sq] using ht) = rhoEnvelope t ht := by
    congr 1
    exact neg_neg t
  rw [e] at h
  exact h

theorem rhoForwardInverse_map₂ (t : k) (ht : t ^ 2 = -1)
    {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g) :
    ((rhoEnvelope t ht).comp (rhoInverse t ht)).map₂ η =
      eqToHom (rhoInverse_rho_map t ht f) ≫ η ≫ eqToHom (rhoInverse_rho_map t ht g).symm :=
  rhoForwardInverse_map₂_of_bare t ht (fun η => rhoEnvelope_bare_roundtrip t ht η) η

theorem rhoInverseForward_map₂ (t : k) (ht : t ^ 2 = -1)
    {a b : TwoSRev k (Uqπ D Sc sy hc)} {f g : a ⟶ b} (η : f ⟶ g) :
    ((rhoInverse t ht).comp (rhoEnvelope t ht)).map₂ η =
      eqToHom (rho_rhoInverse_map t ht f) ≫ η ≫ eqToHom (rho_rhoInverse_map t ht g).symm :=
  rhoInverseForward_map₂_of_bare t ht
    (fun η => rhoEnvelope_bare_roundtrip_reverse t ht η) η

end OddMath.SKM.RhoMapInverses
