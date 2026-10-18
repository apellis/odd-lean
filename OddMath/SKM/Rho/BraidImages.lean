import OddMath.SKM.Rho.Quadratic
import OddMath.SKM.Rho.BraidDots

/-!
# Braid Images for ρ

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

theorem wt_swap_left3 (μ : X) (i j a : I) :
    wt D μ (ups [j,i,a]) = wt D μ (ups [i,j,a]) := by
  simp [ups, wt, sh, add_comm, add_left_comm]
theorem wt_swap_right3 (μ : X) (i j a : I) :
    wt D μ (ups [i,a,j]) = wt D μ (ups [i,j,a]) := by
  simp [ups, wt, sh, add_comm, add_left_comm, add_assoc]

def crossLeft3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ (ups [i,j,a]) = ν) :
    rhoUpAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [i,j,a] h ⟶
      rhoUpAt ν μ [j,i,a] ((wt_swap_left3 μ i j a).trans h) :=
  psiCoeff t (D.parity i * D.parity j) •
    cl D Sc ν [dn a,dn j,dn i] [dn a,dn i,dn j]
      ((dcrossL j i).map (whL [dn a] []))

def crossRight3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ (ups [i,j,a]) = ν) :
    rhoUpAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [i,j,a] h ⟶
      rhoUpAt ν μ [i,a,j] ((wt_swap_right3 μ i j a).trans h) :=
  psiCoeff t (D.parity j * D.parity a) •
    cl D Sc ν [dn a,dn j,dn i] [dn j,dn a,dn i]
      ((dcrossL a j).map (whL [] [dn i]))

def braidCoeff (t : k) (i j a : I) : k :=
  psiCoeff t (D.parity i * D.parity j) * psiCoeff t (D.parity i * D.parity a) *
    psiCoeff t (D.parity j * D.parity a)

theorem crossLeft3_comp (t : k) (ν μ : X) (i j a : I) (h : wt D μ (ups [i,j,a]) = ν) :
    crossLeft3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h ≫
      crossRight3 t ν μ j i a ((wt_swap_left3 μ i j a).trans h) ≫
      crossLeft3 t ν μ j a i ((wt_swap_right3 μ j i a).trans ((wt_swap_left3 μ i j a).trans h)) =
    braidCoeff (D := D) t i j a •
      cl D Sc ν [dn a,dn j,dn i] [dn i,dn j,dn a] (lemma33_eq9_lhs i j a) := by
  change (psiCoeff t (D.parity i * D.parity j) • cl D Sc ν _ _ _) ≫
    (psiCoeff t (D.parity i * D.parity a) • cl D Sc ν _ _ _) ≫
    (psiCoeff t (D.parity j * D.parity a) • cl D Sc ν _ _ _) = _
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul]
  have h1 : SChain [dn a,dn j,dn i] ((dcrossL j i).map (whL [dn a] [])) [dn a,dn i,dn j] :=
    (sChain_dcrossL j i).wh [dn a] [] rfl rfl
  have h2 : SChain [dn a,dn i,dn j] ((dcrossL a i).map (whL [] [dn j])) [dn i,dn a,dn j] :=
    (sChain_dcrossL a i).wh [] [dn j] rfl rfl
  have h3 : SChain [dn i,dn a,dn j] ((dcrossL a j).map (whL [dn i] [])) [dn i,dn j,dn a] :=
    (sChain_dcrossL a j).wh [dn i] [] rfl rfl
  rw [cl_comp (D := D) (Sc := Sc) (μ := ν) h2 h3,
    cl_comp (D := D) (Sc := Sc) (μ := ν) h1 (h2.append h3)]
  simp only [braidCoeff, lemma33_eq9_lhs, List.append_assoc, mul_assoc, mul_comm]

theorem crossRight3_comp (t : k) (ν μ : X) (i j a : I) (h : wt D μ (ups [i,j,a]) = ν) :
    crossRight3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h ≫
      crossLeft3 t ν μ i a j ((wt_swap_right3 μ i j a).trans h) ≫
      crossRight3 t ν μ a i j ((wt_swap_left3 μ i a j).trans ((wt_swap_right3 μ i j a).trans h)) =
    braidCoeff (D := D) t i j a •
      cl D Sc ν [dn a,dn j,dn i] [dn i,dn j,dn a] (lemma33_eq9_rhs i j a) := by
  change (psiCoeff t (D.parity j * D.parity a) • cl D Sc ν _ _ _) ≫
    (psiCoeff t (D.parity i * D.parity a) • cl D Sc ν _ _ _) ≫
    (psiCoeff t (D.parity i * D.parity j) • cl D Sc ν _ _ _) = _
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul]
  have h1 : SChain [dn a,dn j,dn i] ((dcrossL a j).map (whL [] [dn i])) [dn j,dn a,dn i] :=
    (sChain_dcrossL a j).wh [] [dn i] rfl rfl
  have h2 : SChain [dn j,dn a,dn i] ((dcrossL a i).map (whL [dn j] [])) [dn j,dn i,dn a] :=
    (sChain_dcrossL a i).wh [dn j] [] rfl rfl
  have h3 : SChain [dn j,dn i,dn a] ((dcrossL j i).map (whL [] [dn a])) [dn i,dn j,dn a] :=
    (sChain_dcrossL j i).wh [] [dn a] rfl rfl
  rw [cl_comp (D := D) (Sc := Sc) (μ := ν) h2 h3,
    cl_comp (D := D) (Sc := Sc) (μ := ν) h1 (h2.append h3)]
  simp only [braidCoeff, lemma33_eq9_rhs, List.append_assoc, mul_assoc]

end OddMath.SKM.RhoCoefficients
