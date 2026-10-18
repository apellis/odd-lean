import OddMath.SKM.Rho.WhiskerComparison

/-!
# Small Layers for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoUpwardKernel
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords RhoEvaluator RhoCoefficients
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem dot_left (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j] = ν) :
    forget (Sc := Sc) (sy := sy) (hc := hc) ν μ h h
      (rhoRaw t ν μ [([], .dot i, [up j])] h h ⟨rfl,rfl⟩) =
      psiCoeff t (D.parity i) • cl D Sc ν [dn j,dn i] [dn j,dn i]
        ((ddotL i).map (whL [dn j] [])) := by
  subst ν
  apply eq_of_heq
  exact (right_layer t μ (.dot i) [j]).trans (left_whisker_layers t μ i j)

theorem dot_right (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j] = ν) :
    forget (Sc := Sc) (sy := sy) (hc := hc) ν μ h h
      (rhoRaw t ν μ [([up i], .dot j, [])] h h ⟨rfl,rfl⟩) =
      psiCoeff t (D.parity j) • cl D Sc ν [dn j,dn i] [dn j,dn i]
        ((ddotL j).map (whL [] [dn i])) := by
  subst ν
  apply eq_of_heq
  exact (left_layer t μ [i] (.dot j)).trans (right_whisker_layers t μ i j)

theorem cross_left3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ [up i,up j,up a] = ν) :
    forget (Sc := Sc) (sy := sy) (hc := hc) ν μ h ((wt_swap_left3 μ i j a).trans h)
      (rhoRaw t ν μ [([], .cross i j, [up a])] h _ ⟨rfl,rfl⟩) =
      psiCoeff t (D.parity i * D.parity j) • cl D Sc ν [dn a,dn j,dn i] [dn a,dn i,dn j]
        ((dcrossL j i).map (whL [dn a] [])) := by
  subst ν
  apply eq_of_heq
  have H := right_layer (Sc := Sc) (sy := sy) (hc := hc) t μ (.cross i j) [a]
  rw [RhoGenerators.cross_agreement] at H
  exact H.trans (crossLeft3_whisker t μ i j a)

theorem cross_right3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ [up i,up j,up a] = ν) :
    forget (Sc := Sc) (sy := sy) (hc := hc) ν μ h ((wt_swap_right3 μ i j a).trans h)
      (rhoRaw t ν μ [([up i], .cross j a, [])] h _ ⟨rfl,rfl⟩) =
      psiCoeff t (D.parity j * D.parity a) • cl D Sc ν [dn a,dn j,dn i] [dn j,dn a,dn i]
        ((dcrossL a j).map (whL [] [dn i])) := by
  subst ν
  apply eq_of_heq
  have H := left_layer (Sc := Sc) (sy := sy) (hc := hc) t μ [i] (.cross j a)
  rw [RhoGenerators.cross_agreement] at H
  exact H.trans (crossRight3_whisker t μ i j a)

theorem dot_first3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ [up i,up j,up a] = ν) :
    forget (Sc := Sc) (sy := sy) (hc := hc) ν μ h h
      (rhoRaw t ν μ [([], .dot i, [up j,up a])] h h ⟨rfl,rfl⟩) =
      psiCoeff t (D.parity i) • cl D Sc ν [dn a,dn j,dn i] [dn a,dn j,dn i]
        ((ddotL i).map (whL [dn a,dn j] [])) := by
  subst ν
  apply eq_of_heq
  exact (right_layer t μ (.dot i) [j,a]).trans (dotFirst3_whisker t μ i j a)

end OddMath.SKM.RhoUpwardKernel
