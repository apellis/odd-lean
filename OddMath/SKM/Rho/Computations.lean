import OddMath.SKM.Rho.Gradings

/-!
# Computations for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoEvaluator
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem rhoLin_gen (t : k) (ν μ : X) (g : Shape I) (h : wt D μ g.dom = ν) :
    rhoLin (sy := sy) (hc := hc) t ν μ h ((g.wt_dom_eq_wt_cod D μ).symm.trans h)
      (dg D μ [([], g, [])] (by simp [SChain])) =
      RhoGenerators.generator t ν μ g h := by
  rw [rhoLin_dg, rhoRaw_gen]

theorem rhoLin_formula (t : k) (ν μ : X) (g : Shape I) (h : wt D μ g.dom = ν) :
    HEq (rhoLin (sy := sy) (hc := hc) t ν μ h ((g.wt_dom_eq_wt_cod D μ).symm.trans h)
      (dg D μ [([], g, [])] (by simp [SChain])))
      (RhoGenerators.normal (sy := sy) (hc := hc) t ν μ g h) := by
  rw [rhoLin_gen]
  exact RhoGenerators.generator_formula t ν μ g h

private theorem rhoLayer_at (t : k) (Ω ν ξ μ : X)
    (u : List (Letter I)) (g : Shape I) (v : List (Letter I))
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hg : wt D ξ g.dom = ν) :
    rhoLayer (sy := sy) (hc := hc) t Ω μ u g v
        (by rw [wt_append, wt_append, hv, hg, hu]) =
      place Ω ν ξ μ u v hu hv hg ((g.wt_dom_eq_wt_cod D ξ).symm.trans hg)
        (RhoGenerators.generator t ν ξ g hg) := by
  subst ξ ν
  rfl

theorem rhoRaw_layer (t : k) (Ω ν ξ μ : X)
    (u : List (Letter I)) (g : Shape I) (v : List (Letter I))
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hg : wt D ξ g.dom = ν) :
    rhoRaw (sy := sy) (hc := hc) t Ω μ [(u, g, v)]
        (by rw [wt_append, wt_append, hv, hg, hu])
        (by rw [wt_append, wt_append, hv, ← g.wt_dom_eq_wt_cod D, hg, hu]) ⟨rfl, rfl⟩ =
      place Ω ν ξ μ u v hu hv hg ((g.wt_dom_eq_wt_cod D ξ).symm.trans hg)
        (RhoGenerators.generator t ν ξ g hg) := by
  simp only [rhoRaw, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact rhoLayer_at t Ω ν ξ μ u g v hu hv hg

theorem rhoLin_onGen (t : k) (g : (sig D).Gen) :
    rhoLin (sy := sy) (hc := hc) t ((sig D).left g) ((sig D).right g)
      (s := g.1.dom) (r := g.1.cod) rfl (g.1.wt_dom_eq_wt_cod D g.2).symm
      (dg D g.2 [([], g.1, [])] (by simp [SChain])) =
      RhoGenerators.onGen t g := rhoLin_gen t _ _ g.1 rfl

end OddMath.SKM.RhoEvaluator
