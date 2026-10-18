import OddMath.SKM.Rho.Evaluations

/-!
# Envelope Evaluations for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoMates
open CategoryTheory StringDiagrams Presentation RhoWords RhoEvaluator RhoInversionKernel RhoTwo RhoExtension
  QPiSupercategory Envelope
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

local instance (a b : TwoSRev k (Uqπ D Sc sy hc)) : QPiSupercategory k (a ⟶ b) :=
  QPiTwoSupercategory.homQPiLeft a b

def returned (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (A : List (LayerData I)) :
    rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ rhoAt ν μ r hr :=
  show (pres D Sc).obj (rhoAt (sy := sy) (hc := hc) ν μ s hs).obj.obj.obj ⟶
    (pres D Sc).obj (rhoAt (sy := sy) (hc := hc) ν μ r hr).obj.obj.obj from
    eqToHom (congrArg (pres D Sc).obj (at_obj ν μ s hs)) ≫
      cl D Sc ν (rhoWord s) (rhoWord r) A ≫
        eqToHom (congrArg (pres D Sc).obj (at_obj ν μ r hr)).symm

theorem quotient_ddot_eq (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I)
    (h : wt D μ [dn i] = ν) :
    rhoQuotient (sy := sy) (hc := hc) t ht ν μ h h (cl D Sc μ [dn i] [dn i] (ddotL i)) =
      psiCoeff t (D.parity i) • returned (sy := sy) (hc := hc) ν μ h h (dotsL [] i [] 1) := by
  unfold returned
  rw [← Linear.comp_smul, ← Linear.smul_comp]
  exact (conj_eqToHom_iff_heq _ _
    (congrArg (pres D Sc).obj (at_obj (sy := sy) (hc := hc) ν μ [dn i] h))
    (congrArg (pres D Sc).obj (at_obj (sy := sy) (hc := hc) ν μ [dn i] h))).mpr
      (quotient_ddot (Sc := Sc) (sy := sy) (hc := hc) t ht ν μ i h)

theorem quotient_dcross_eq (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (hs : wt D μ [dn j, dn i] = ν) (hr : wt D μ [dn i, dn j] = ν) :
    rhoQuotient (sy := sy) (hc := hc) t ht ν μ hs hr
      (cl D Sc μ [dn j, dn i] [dn i, dn j] (dcrossL j i)) =
      psiCoeff t (D.parity i * D.parity j) •
        returned (sy := sy) (hc := hc) ν μ hs hr (crossL [] i j []) := by
  unfold returned
  rw [← Linear.comp_smul, ← Linear.smul_comp]
  exact (conj_eqToHom_iff_heq _ _
    (congrArg (pres D Sc).obj (at_obj (sy := sy) (hc := hc) ν μ [dn j, dn i] hs))
    (congrArg (pres D Sc).obj (at_obj (sy := sy) (hc := hc) ν μ [dn i, dn j] hr))).mpr
      (quotient_dcross (Sc := Sc) (sy := sy) (hc := hc) t ht ν μ i j hs hr)

theorem envelope_ddot (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I)
    (h : wt D μ [dn i] = ν) (m n : ℤ) :
    (rhoEnvelope (sy := sy) (hc := hc) t ht).map₂
      (show (⟨0, ⟨m, psiWordAt (Sc := Sc) ν μ [dn i] h⟩⟩ :
        (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩) ⟶
        ⟨0, ⟨n, psiWordAt ν μ [dn i] h⟩⟩ from cl D Sc μ [dn i] [dn i] (ddotL i)) =
      psiCoeff t (D.parity i) •
        ((σPow k m (rhoAt ν μ [dn i] h)).hom ≫
          returned (sy := sy) (hc := hc) ν μ h h (dotsL [] i [] 1) ≫
            (σPow k n (rhoAt ν μ [dn i] h)).inv) := by
  rw [rhoEnvelope_map₂]
  simp only [ζPow_zero, Iso.refl_hom, Iso.refl_inv, Category.comp_id]
  change 𝟙 _ ≫ ((σPow k m (rhoAt ν μ [dn i] h)).hom ≫
    rhoMap₂ t ht (psiWordAt ν μ [dn i] h) (psiWordAt ν μ [dn i] h)
      (cl D Sc μ [dn i] [dn i] (ddotL i)) ≫ (σPow k n (rhoAt ν μ [dn i] h)).inv) = _
  rw [Category.id_comp, rhoMap₂_wordAt]
  exact (congrArg (fun η : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [dn i] h ⟶
      rhoAt ν μ [dn i] h => (σPow k m (rhoAt ν μ [dn i] h)).hom ≫ η ≫
        (σPow k n (rhoAt ν μ [dn i] h)).inv)
      (quotient_ddot_eq t ht ν μ i h)).trans
        ((congrArg (fun η => (σPow k m (rhoAt ν μ [dn i] h)).hom ≫ η)
          (Linear.smul_comp _ _ _ _ _ _)).trans (Linear.comp_smul _ _ _ _ _ _))

theorem envelope_dcross (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (hs : wt D μ [dn j, dn i] = ν) (hr : wt D μ [dn i, dn j] = ν) (m n : ℤ) :
    (rhoEnvelope (sy := sy) (hc := hc) t ht).map₂
      (show (⟨0, ⟨m, psiWordAt (Sc := Sc) ν μ [dn j, dn i] hs⟩⟩ :
        (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩) ⟶
        ⟨0, ⟨n, psiWordAt ν μ [dn i, dn j] hr⟩⟩ from
          cl D Sc μ [dn j, dn i] [dn i, dn j] (dcrossL j i)) =
      psiCoeff t (D.parity i * D.parity j) •
        ((σPow k m (rhoAt ν μ [dn j, dn i] hs)).hom ≫
          returned (sy := sy) (hc := hc) ν μ hs hr (crossL [] i j []) ≫
            (σPow k n (rhoAt ν μ [dn i, dn j] hr)).inv) := by
  rw [rhoEnvelope_map₂]
  simp only [ζPow_zero, Iso.refl_hom, Iso.refl_inv, Category.comp_id]
  change 𝟙 _ ≫ ((σPow k m (rhoAt ν μ [dn j, dn i] hs)).hom ≫
    rhoMap₂ t ht (psiWordAt ν μ [dn j, dn i] hs) (psiWordAt ν μ [dn i, dn j] hr)
      (cl D Sc μ [dn j, dn i] [dn i, dn j] (dcrossL j i)) ≫
        (σPow k n (rhoAt ν μ [dn i, dn j] hr)).inv) = _
  rw [Category.id_comp, rhoMap₂_wordAt]
  exact (congrArg (fun η : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [dn j, dn i] hs ⟶
      rhoAt ν μ [dn i, dn j] hr => (σPow k m (rhoAt ν μ [dn j, dn i] hs)).hom ≫ η ≫
        (σPow k n (rhoAt ν μ [dn i, dn j] hr)).inv)
      (quotient_dcross_eq t ht ν μ i j hs hr)).trans
        ((congrArg (fun η => (σPow k m (rhoAt ν μ [dn j, dn i] hs)).hom ≫ η)
          (Linear.smul_comp _ _ _ _ _ _)).trans (Linear.comp_smul _ _ _ _ _ _))

end OddMath.SKM.RhoMates
