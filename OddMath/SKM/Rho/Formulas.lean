import OddMath.SKM.Rho.Generators

/-!
# Formulas for ρ

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

private theorem transport_heq {C : Type*} [Category C] {a b a' b' : C}
    (ha : a = a') (hb : b' = b) (f : a' ⟶ b') :
    HEq (eqToHom ha ≫ f ≫ eqToHom hb) f := by
  subst a' b'
  exact heq_of_eq (by simp)

theorem generator_formula (t : k) (ν μ : X) (g : Shape I) (h : wt D μ g.dom = ν) :
    HEq (generator (Sc := Sc) (sy := sy) (hc := hc) t ν μ g h)
      (coeff (D := D) t g • cl D Sc ν (rhoWord g.dom) (rhoWord g.cod) (layers g)) :=
  transport_heq _ _ (normal t ν μ g h)

private theorem wt_ud (μ : X) (i : I) : wt D μ [up i, dn i] = μ := by simp [wt, sh]
private theorem wt_du (μ : X) (i : I) : wt D μ [dn i, up i] = μ := by simp [wt, sh]

theorem dot_agreement (t : k) (μ : X) (i : I) :
    normal (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up i]) μ (.dot i) rfl =
      rhoDot t μ i := rfl

theorem cross_agreement (t : k) (ν μ : X) (i j : I) (h : wt D μ (ups [i,j]) = ν) :
    normal (Sc := Sc) (sy := sy) (hc := hc) t ν μ (.cross i j) h =
      RhoCoefficients.correctedCrossing t ν μ i j h := (RhoCoefficients.correctedCrossing_eq t ν μ i j h).symm

theorem cup_agreement (t : k) (μ : X) (i : I) :
    normal (Sc := Sc) (sy := sy) (hc := hc) t μ μ (.cup i) rfl =
      RhoParity.cup (sy := sy) (hc := hc) 0 μ i := by
  exact one_smul k _

theorem cap_agreement (t : k) (μ : X) (i : I) :
    normal (Sc := Sc) (sy := sy) (hc := hc) t μ μ (.cap i) (wt_ud μ i) =
      RhoParity.cap (sy := sy) (hc := hc) 0 μ i := by
  exact one_smul k _

theorem lcross_agreement (t : k) (ν μ : X) (i j : I) (h : wt D μ [dn i, up j] = ν) :
    normal (Sc := Sc) (sy := sy) (hc := hc) t ν μ (.lcross i j) h =
      RhoMixed.mixedInverse t ν i j := rfl

theorem dcup_agreement (t : k) (μ : X) (i : I) (n : ℕ) :
    normal (Sc := Sc) (sy := sy) (hc := hc) t μ μ (.dcup i n) rfl =
      RhoMixed.cupDiamond t μ i n := rfl

theorem dcap_agreement (t : k) (μ : X) (i : I) (n : ℕ) :
    normal (Sc := Sc) (sy := sy) (hc := hc) t μ μ (.dcap i n) (wt_du μ i) =
      RhoMixed.capDiamond t μ i n := rfl

theorem dcup_zero (t : k) (ν μ : X) (i : I) (n : ℕ)
    (h : wt D μ (Shape.dcup i n).dom = ν) (hn : D.h i μ ≤ n) :
    generator (Sc := Sc) (sy := sy) (hc := hc) t ν μ (.dcup i n) h = 0 := by
  have hw : μ = ν := h
  cases hw
  unfold generator
  rw [dcup_agreement, RhoMixed.cupDiamond_zero t ν i n hn]
  simp

theorem dcap_zero (t : k) (ν μ : X) (i : I) (n : ℕ)
    (h : wt D μ (Shape.dcap i n).dom = ν) (hn : -D.h i μ ≤ n) :
    generator (Sc := Sc) (sy := sy) (hc := hc) t ν μ (.dcap i n) h = 0 := by
  have hw : μ = ν := by simpa [Shape.dom, wt, sh] using h
  cases hw
  unfold generator
  rw [dcap_agreement, RhoMixed.capDiamond_zero t ν i n hn]
  simp

end OddMath.SKM.RhoGenerators
