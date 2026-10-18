import OddMath.SKM.Rho.PlacedDots

/-!
# Boundaries for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.SKM.RhoCoefficients
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem rho_pair_E_comp (μ : X) (i j a : I) :
    rhoUpAt (Sc := Sc) (sy := sy) (hc := hc)
      (wt D (wt D μ [up a]) (ups [i,j])) (wt D μ [up a]) [i,j] rfl ≫ rhoE μ a =
    rhoUpAt (wt D μ (ups [i,j,a])) μ [i,j,a] rfl := by
  apply Envelope.ext
  · rfl
  · apply QEnvelope.ext
    · change rhoUpShift sy μ [a] + rhoUpShift sy (wt D μ [up a]) [i,j] = rhoUpShift sy μ [i,j,a]
      simp [rhoUpShift, ups, add_comm, add_left_comm, add_assoc]
    · apply Presentation.Bicat.Hom.ext
      change (ob D (wt D μ [up a]) [dn a]).tensor
        (ob D (wt D (wt D μ [up a]) (ups [i,j])) [dn j,dn i]) =
          ob D (wt D μ (ups [i,j,a])) [dn a,dn j,dn i]
      simp [ob, wd, wt, sh, ups, StringDiagrams.Obj.tensor]

theorem rho_E_pair_comp (μ : X) (i j a : I) :
    rhoE (Sc := Sc) (sy := sy) (hc := hc) (wt D μ (ups [j,a])) i ≫
      rhoUpAt (wt D μ (ups [j,a])) μ [j,a] rfl =
    rhoUpAt (wt D μ (ups [i,j,a])) μ [i,j,a] rfl := by
  apply Envelope.ext
  · rfl
  · apply QEnvelope.ext
    · change rhoUpShift sy μ [j,a] + rhoUpShift sy (wt D μ (ups [j,a])) [i] = rhoUpShift sy μ [i,j,a]
      simp [rhoUpShift, ups, add_comm, add_left_comm, add_assoc]
    · apply Presentation.Bicat.Hom.ext
      change (ob D (wt D μ (ups [j,a])) [dn a,dn j]).tensor
        (ob D (wt D (wt D μ (ups [j,a])) [up i]) [dn i]) =
          ob D (wt D μ (ups [i,j,a])) [dn a,dn j,dn i]
      simp [ob, wd, wt, sh, ups, StringDiagrams.Obj.tensor]

end OddMath.SKM.RhoCoefficients
