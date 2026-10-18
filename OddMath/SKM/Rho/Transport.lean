import OddMath.SKM.Rho.Computations
import OddMath.SKM.Rho.PlacedDots
import OddMath.SKM.Rho.Boundaries

/-!
# Transport for ρ

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

theorem eq_underlying {ν μ : X}
    {a b : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ} (h : a = b) :
    eqToHom h = eqToHom (congrArg (fun x => (pres D Sc).obj x.obj.obj.obj) h) := by
  cases h
  rfl

theorem at_obj (ν μ : X) (s : List (Letter I)) (hs : wt D μ s = ν) :
    (pres D Sc).obj (rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs).obj.obj.obj =
      (pres D Sc).obj (ob D ν (rhoWord s)) :=
  congrArg (fun x : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ =>
    (pres D Sc).obj x.obj.obj.obj) (RhoGenerators.map_word (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs)

def forget (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) :
    (rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ rhoAt ν μ r hr) →ₗ[k]
      ((pres D Sc).obj (ob D ν (rhoWord s)) ⟶ (pres D Sc).obj (ob D ν (rhoWord r))) where
  toFun f := eqToHom (at_obj ν μ s hs).symm ≫ f ≫
    eqToHom (at_obj ν μ r hr)
  map_add' _ _ := by simp [Preadditive.comp_add, Preadditive.add_comp]
  map_smul' _ _ := by simp [Linear.comp_smul, Linear.smul_comp]

theorem forget_injective (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) :
    Function.Injective (forget (Sc := Sc) (sy := sy) (hc := hc) ν μ hs hr) := by
  intro f g h
  change (eqToHom (at_obj (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs).symm ≫
    (show (pres D Sc).obj (rhoAt ν μ s hs).obj.obj.obj ⟶
      (pres D Sc).obj (rhoAt ν μ r hr).obj.obj.obj from f) ≫ eqToHom (at_obj ν μ r hr)) =
    eqToHom (at_obj ν μ s hs).symm ≫ g ≫ eqToHom (at_obj ν μ r hr) at h
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id] using
    congrArg (fun z => eqToHom (at_obj ν μ s hs) ≫ z ≫
      eqToHom (at_obj ν μ r hr).symm) h

theorem forget_comp (ν μ : X) {s r q : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hq : wt D μ q = ν)
    (f : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ rhoAt ν μ r hr)
    (g : rhoAt ν μ r hr ⟶ rhoAt ν μ q hq) :
    forget ν μ hs hq (f ≫ g) = forget ν μ hs hr f ≫ forget ν μ hr hq g := by
  change (eqToHom (at_obj (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs).symm ≫
    ((show (pres D Sc).obj (rhoAt ν μ s hs).obj.obj.obj ⟶
      (pres D Sc).obj (rhoAt ν μ r hr).obj.obj.obj from f) ≫ g) ≫ eqToHom (at_obj ν μ q hq)) = _
  simp [forget, Category.assoc]

theorem forget_id (ν μ : X) (s : List (Letter I)) (hs : wt D μ s = ν) :
    forget (Sc := Sc) (sy := sy) (hc := hc) ν μ hs hs (𝟙 _) = 𝟙 _ := by
  change eqToHom (at_obj (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs).symm ≫
    𝟙 ((pres D Sc).obj (rhoAt ν μ s hs).obj.obj.obj) ≫ eqToHom (at_obj ν μ s hs) = _
  simp
theorem forget_generator (t : k) (ν μ : X) (g : Shape I) (h : wt D μ g.dom = ν) :
    forget (Sc := Sc) (sy := sy) (hc := hc) ν μ h ((g.wt_dom_eq_wt_cod D μ).symm.trans h)
      (RhoGenerators.generator t ν μ g h) =
    RhoGenerators.coeff (D := D) t g •
      cl D Sc ν (rhoWord g.dom) (rhoWord g.cod) (RhoGenerators.layers g) := by
  simp only [forget, LinearMap.coe_mk, AddHom.coe_mk, RhoGenerators.generator,
    eq_underlying, RhoGenerators.normal]
  change eqToHom (at_obj (Sc := Sc) (sy := sy) (hc := hc) ν μ g.dom h).symm ≫
    (eqToHom (at_obj ν μ g.dom h) ≫
      (RhoGenerators.coeff (D := D) t g • cl D Sc ν _ _ (RhoGenerators.layers g)) ≫
      eqToHom (at_obj ν μ g.cod ((g.wt_dom_eq_wt_cod D μ).symm.trans h)).symm) ≫
      eqToHom (at_obj ν μ g.cod ((g.wt_dom_eq_wt_cod D μ).symm.trans h)) = _
  simp [Category.assoc]

end OddMath.SKM.RhoUpwardKernel
