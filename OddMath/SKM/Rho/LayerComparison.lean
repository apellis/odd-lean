import OddMath.SKM.Rho.Transport

/-!
# Layer Comparison for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoUpwardKernel
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords RhoEvaluator
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem transport_heq {C : Type*} [Category C] {a b a' b' : C}
    (ha : a = a') (hb : b' = b) (f : a' ⟶ b') :
    HEq (eqToHom ha ≫ f ≫ eqToHom hb) f := by
  subst a' b'
  exact heq_of_eq (by simp)

theorem forget_heq (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (f : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ rhoAt ν μ r hr) :
    HEq (forget ν μ hs hr f) f := by
  exact transport_heq (at_obj (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs).symm
    (at_obj ν μ r hr)
    (show (pres D Sc).obj (rhoAt ν μ s hs).obj.obj.obj ⟶
      (pres D Sc).obj (rhoAt ν μ r hr).obj.obj.obj from f)

theorem place_heq (Ω ν ξ μ : X) (u v : List (Letter I)) {s r : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν)
    (η : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ rhoAt ν ξ r hr) :
    HEq (place Ω ν ξ μ u v hu hv hs hr η) (rhoAt Ω ν u hu ◁ (η ▷ rhoAt ξ μ v hv)) :=
  transport_heq _ _ _

theorem bare_cross (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j] = ν) :
    forget (Sc := Sc) (sy := sy) (hc := hc) ν μ h ((Shape.cross i j).wt_dom_eq_wt_cod D μ |>.symm.trans h)
      (rhoRaw t ν μ (crossL [] i j []) h _ (by simp [crossL, SChain, Shape.dom, Shape.cod])) =
    psiCoeff t (D.parity i * D.parity j) • cl D Sc ν [dn j,dn i] [dn i,dn j] (dcrossL j i) := by
  simp only [crossL]
  rw [rhoRaw_gen]
  exact forget_generator t ν μ (.cross i j) h

end OddMath.SKM.RhoUpwardKernel
