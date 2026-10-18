import OddMath.SKM.Rho.Context
import OddMath.SKM.PsiDescent

/-!
# Placement for ρ

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

abbrev rhoAt (ν μ : X) (s : List (Letter I)) (h : wt D μ s = ν) :=
  rhoMap (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ s h)

theorem at_comp (ν ξ μ : X) (s t : List (Letter I))
    (hs : wt D ξ s = ν) (ht : wt D μ t = ξ) :
    rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ≫ rhoAt ξ μ t ht =
      rhoAt ν μ (s ++ t) (by rw [wt_append, ht, hs]) := by
  rw [← rhoMap_comp, psiWordAt_comp_eq]

theorem at_congr (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (h : s = r) :
    rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs = rhoAt ν μ r hr := by
  cases h
  rfl

private theorem transport_parity {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {a b a' b' : C} (ha : a = a') (hb : b' = b) {p : ZMod 2}
    {η : a' ⟶ b'} (hη : η ∈ parity (R := k) _ _ p) :
    eqToHom ha ≫ η ≫ eqToHom hb ∈ parity (R := k) _ _ p := by
  subst a' b'
  simpa using hη

private theorem transport_degree {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] [GradedSupercategory k C]
    {a b a' b' : C} (ha : a = a') (hb : b' = b) {n : ℤ}
    {η : a' ⟶ b'} (hη : η ∈ GradedSupercategory.degree (R := k) _ _ n) :
    eqToHom ha ≫ η ≫ eqToHom hb ∈ GradedSupercategory.degree (R := k) _ _ n := by
  subst a' b'
  simpa using hη

def place (Ω ν ξ μ : X) (u v : List (Letter I)) {s r : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν)
    (η : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ rhoAt ν ξ r hr) :
    rhoAt (Sc := Sc) (sy := sy) (hc := hc) Ω μ (u ++ s ++ v)
        (by rw [wt_append, wt_append, hv, hs, hu]) ⟶
      rhoAt Ω μ (u ++ r ++ v) (by rw [wt_append, wt_append, hv, hr, hu]) :=
  eqToHom (by
    rw [at_comp, at_comp]
    exact at_congr Ω μ _ _ (List.append_assoc u s v)) ≫
  (rhoAt Ω ν u hu ◁ (η ▷ rhoAt ξ μ v hv)) ≫
  eqToHom (by
    rw [at_comp, at_comp]
    exact at_congr Ω μ _ _ (List.append_assoc u r v).symm)

theorem place_parity (Ω ν ξ μ : X) (u v : List (Letter I)) {s r : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν)
    {p : ZMod 2} {η : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ rhoAt ν ξ r hr}
    (hη : η ∈ parity (R := k) _ _ p) :
    place Ω ν ξ μ u v hu hv hs hr η ∈ parity (R := k) _ _ p := by
  apply transport_parity
  apply TwoSupercategory.whiskerLeft_mem (R := k) (B := TwoSRev k (Uqπ D Sc sy hc))
  exact TwoSupercategory.whiskerRight_mem (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)) _ hη

theorem place_degree (Ω ν ξ μ : X) (u v : List (Letter I)) {s r : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν)
    {n : ℤ} {η : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ rhoAt ν ξ r hr}
    (hη : η ∈ GradedSupercategory.degree (R := k) _ _ n) :
    place Ω ν ξ μ u v hu hv hs hr η ∈ GradedSupercategory.degree (R := k) _ _ n := by
  apply transport_degree
  apply GradedTwoSupercategory.whiskerLeft_mem_degree (R := k) (B := TwoSRev k (Uqπ D Sc sy hc))
  exact GradedTwoSupercategory.whiskerRight_mem_degree (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)) _ hη

theorem place_comp (Ω ν ξ μ : X) (u v : List (Letter I)) {s r q : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ)
    (hs : wt D ξ s = ν) (hr : wt D ξ r = ν) (hq : wt D ξ q = ν)
    (η : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ rhoAt ν ξ r hr)
    (θ : rhoAt ν ξ r hr ⟶ rhoAt ν ξ q hq) :
    place Ω ν ξ μ u v hu hv hs hq (η ≫ θ) =
      place Ω ν ξ μ u v hu hv hs hr η ≫ place Ω ν ξ μ u v hu hv hr hq θ := by
  simp [place, TwoSupercategory.whiskerLeft_comp (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    TwoSupercategory.comp_whiskerRight (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)), Category.assoc]

def placeLinear (Ω ν ξ μ : X) (u v : List (Letter I)) {s r : List (Letter I)}
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν) :
    (rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ rhoAt ν ξ r hr) →ₗ[k]
      (rhoAt (Sc := Sc) (sy := sy) (hc := hc) Ω μ (u ++ s ++ v)
          (by rw [wt_append, wt_append, hv, hs, hu]) ⟶
        rhoAt Ω μ (u ++ r ++ v) (by rw [wt_append, wt_append, hv, hr, hu])) where
  toFun := place Ω ν ξ μ u v hu hv hs hr
  map_add' η θ := by
      simp [place,
      TwoSupercategory.whiskerLeft_add (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)), TwoSupercategory.add_whiskerRight (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
      Preadditive.add_comp, Preadditive.comp_add]
  map_smul' a η := by
      simp [place,
      TwoSupercategory.whiskerLeft_smul (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)), TwoSupercategory.smul_whiskerRight (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
      Linear.smul_comp, Linear.comp_smul]

theorem place_id (Ω ν ξ μ : X) (u v s : List (Letter I))
    (hu : wt D ν u = Ω) (hv : wt D μ v = ξ) (hs : wt D ξ s = ν) :
    place (Sc := Sc) (sy := sy) (hc := hc) Ω ν ξ μ u v hu hv hs hs (𝟙 _) = 𝟙 _ := by
  simp [place,
    TwoSupercategory.whiskerLeft_id (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)), TwoSupercategory.id_whiskerRight (R := k) (B := TwoSRev k (Uqπ D Sc sy hc))]

end OddMath.SKM.RhoEvaluator
