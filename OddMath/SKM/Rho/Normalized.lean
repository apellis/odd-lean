import OddMath.SKM.Rho.Adjunction

/-!
# Normalized for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoInversionKernel
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords RhoEvaluator
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

def homTransport {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {a b a' b' : C} (ha : a = a') (hb : b = b') : (a ⟶ b) ≃ₗ[k] (a' ⟶ b') := by
  subst a' b'
  exact LinearEquiv.refl k _

theorem homTransport_heq {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {a b a' b' : C} (ha : a = a') (hb : b = b') {f : a ⟶ b} {g : a' ⟶ b'}
    (h : HEq f g) : homTransport (k := k) ha hb f = g := by
  subst a' b'
  exact eq_of_heq h

def normLin (t : k) (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) :
    LinDiagram k (ob D μ s) (ob D μ r) →ₗ[k]
      ((pres D Sc).obj (ob D ν (rhoWord s)) ⟶ (pres D Sc).obj (ob D ν (rhoWord r))) :=
  (homTransport (congrArg (pres D Sc).obj (at_obj (sy := sy) (hc := hc) ν μ s hs))
    (congrArg (pres D Sc).obj (at_obj (sy := sy) (hc := hc) ν μ r hr))).toLinearMap.comp
    (rhoLin t ν μ hs hr)

theorem kernel_of_norm (t : k) (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (f : LinDiagram k (ob D μ s) (ob D μ r))
    (h : normLin (Sc := Sc) (sy := sy) (hc := hc) t ν μ hs hr f = 0) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hr f = 0 := by
  let e := homTransport (k := k)
    (congrArg (pres D Sc).obj (at_obj (sy := sy) (hc := hc) ν μ s hs))
    (congrArg (pres D Sc).obj (at_obj (sy := sy) (hc := hc) ν μ r hr))
  apply e.injective
  change normLin t ν μ hs hr f = e 0
  rw [h, map_zero]

theorem norm_dg (t : k) (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (L : List (LayerData I)) (h : SChain s L r) :
    normLin (Sc := Sc) (sy := sy) (hc := hc) t ν μ hs hr (dg D μ L h) =
      imageCoeff (D := D) t L • cl D Sc ν (rhoWord s) (rhoWord r) (imageLayers L) := by
  change homTransport (k := k)
    (congrArg (pres D Sc).obj (at_obj (sy := sy) (hc := hc) ν μ s hs))
    (congrArg (pres D Sc).obj (at_obj (sy := sy) (hc := hc) ν μ r hr))
    (rhoLin (sy := sy) (hc := hc) t ν μ hs hr (dg D μ L h)) = _
  rw [rhoLin_dg]
  exact homTransport_heq _ _ (raw_formula t ν μ L hs hr h)

theorem norm_idg (t : k) (ν μ : X) (s : List (Letter I)) (hs : wt D μ s = ν) :
    normLin (Sc := Sc) (sy := sy) (hc := hc) t ν μ hs hs (idg D μ s) = 𝟙 _ := by
  change homTransport (k := k)
    (congrArg (pres D Sc).obj (at_obj (sy := sy) (hc := hc) ν μ s hs))
    (congrArg (pres D Sc).obj (at_obj (sy := sy) (hc := hc) ν μ s hs))
    (rhoLin (sy := sy) (hc := hc) t ν μ hs hs (idg D μ s)) = _
  rw [rhoLin_idg]
  exact homTransport_heq _ _ (id_heq (congrArg (pres D Sc).obj (at_obj ν μ s hs)))

theorem imageLayers_append (A B : List (LayerData I)) :
    imageLayers (A ++ B) = imageLayers A ++ imageLayers B := by
  induction A with
  | nil => rfl
  | cons x A ih => simp only [List.cons_append, imageLayers, ih, List.append_assoc]

theorem imageCoeff_append (t : k) (A B : List (LayerData I)) :
    imageCoeff (D := D) t (A ++ B) = imageCoeff (D := D) t A * imageCoeff (D := D) t B := by
  induction A with
  | nil => simp only [List.nil_append, imageCoeff, one_mul]
  | cons x A ih => simp only [List.cons_append, imageCoeff, ih, mul_assoc]

theorem norm_append (t : k) (ν μ : X) {s m r : List (Letter I)}
    (hs : wt D μ s = ν) (hm : wt D μ m = ν) (hr : wt D μ r = ν)
    (A B : List (LayerData I)) (hA : SChain s A m) (hB : SChain m B r) :
    normLin (Sc := Sc) (sy := sy) (hc := hc) t ν μ hs hr (dg D μ (A ++ B) (hA.append hB)) =
      normLin (Sc := Sc) (sy := sy) (hc := hc) t ν μ hs hm (dg D μ A hA) ≫
      normLin (Sc := Sc) (sy := sy) (hc := hc) t ν μ hm hr (dg D μ B hB) := by
  rw [norm_dg, norm_dg, norm_dg, imageLayers_append, imageCoeff_append,
    Linear.smul_comp, Linear.comp_smul, smul_smul, cl_comp (image_chain hA) (image_chain hB)]

end OddMath.SKM.RhoInversionKernel
