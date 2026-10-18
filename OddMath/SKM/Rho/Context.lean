import OddMath.SKM.Rho.Formulas

/-!
# Context for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoGenerators
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

def onGen (t : k) (g : (sig D).Gen) :
    rhoMap (sy := sy) (hc := hc) (psiWordAt (D := D) (Sc := Sc) ((sig D).left g) ((sig D).right g) g.1.dom rfl) ⟶
      rhoMap (psiWordAt (D := D) ((sig D).left g) ((sig D).right g) g.1.cod
        (g.1.wt_dom_eq_wt_cod D g.2).symm) :=
  generator t _ _ g.1 rfl

def rightStrand (t : k) (μ : X) (g : Shape I) (a : I) :=
  BicategoryStruct.whiskerRight (B := TwoSRev k (Uqπ D Sc sy hc))
    (generator t (wt D (wt D μ [up a]) g.dom) (wt D μ [up a]) g rfl)
    (rhoMap (psiWord (Sc := Sc) μ [up a]))

theorem rightStrand_degree (t : k) (μ : X) (g : Shape I) (a : I) :
    rightStrand (Sc := Sc) (sy := sy) (hc := hc) t μ g a ∈
      GradedSupercategory.degree (R := k) _ _ (gdeg D sy (g, wt D μ [up a])) :=
  GradedTwoSupercategory.whiskerRight_mem_degree (R := k) (B := TwoSRev k (Uqπ D Sc sy hc))
    (rhoMap (psiWord (Sc := Sc) μ [up a])) (generator_degree t _ _ g rfl)

theorem rightStrand_parity (t : k) (μ : X) (g : Shape I) (a : I) :
    rightStrand (Sc := Sc) (sy := sy) (hc := hc) t μ g a ∈
      parity (R := k) _ _ (g.parity D) :=
  TwoSupercategory.whiskerRight_mem (R := k) (B := TwoSRev k (Uqπ D Sc sy hc))
    (rhoMap (psiWord (Sc := Sc) μ [up a])) (generator_parity t _ _ g rfl)

theorem rightStrand_source (μ : X) (g : Shape I) (a : I) :
    rhoMap (sy := sy) (hc := hc)
      (psiWordAt (Sc := Sc) (wt D (wt D μ [up a]) g.dom) (wt D μ [up a]) g.dom rfl ≫
        psiWord μ [up a]) =
      rhoMap (psiWordAt (Sc := Sc) (wt D (wt D μ [up a]) g.dom) (wt D μ [up a]) g.dom rfl) ≫
        rhoMap (psiWord μ [up a]) := rhoMap_comp _ _

end OddMath.SKM.RhoGenerators
