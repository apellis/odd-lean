import OddMath.SKM.Rho.Placement

/-!
# Coherence for ρ

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

private theorem eq_underlying {ν μ : X}
    {a b : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ} (h : a = b) :
    eqToHom h = eqToHom (congrArg (fun x => (pres D Sc).obj x.obj.obj.obj) h) := by
  cases h
  rfl

private theorem rev_associator {Ω ν ξ μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) Ω ⟶ rhoObj ν)
    (b : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj ξ)
    (c : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ξ ⟶ rhoObj μ)
    (h : (a ≫ b) ≫ c = a ≫ b ≫ c) :
    (associator a b c).hom = eqToHom h := by
  rw [eq_underlying]
  rfl

private theorem rev_associator_inv {Ω ν ξ μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) Ω ⟶ rhoObj ν)
    (b : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj ξ)
    (c : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ξ ⟶ rhoObj μ)
    (h : (a ≫ b) ≫ c = a ≫ b ≫ c) :
    (associator a b c).inv = eqToHom h.symm := by
  rw [eq_underlying]
  rfl

private theorem rev_assoc {Ω ν ξ μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) Ω ⟶ rhoObj ν)
    (b : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj ξ)
    (c : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ξ ⟶ rhoObj μ) :
    (a ≫ b) ≫ c = a ≫ b ≫ c := by
  apply Envelope.ext
  · exact (add_assoc _ _ _).symm
  · apply QEnvelope.ext
    · exact (add_assoc _ _ _).symm
    · apply Presentation.Bicat.Hom.ext
      apply Obj.ext
      · rfl
      · exact (List.append_assoc _ _ _).symm

private theorem revWhiskerLeft_congr {Ω ν μ : X}
    {a b : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) (Ω) ⟶ rhoObj (ν)}
    (h : a = b) {s r : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) (ν) ⟶ rhoObj (μ)}
    (η : s ⟶ r) :
    b ◁ η = eqToHom (congrArg (· ≫ s) h.symm) ≫ (a ◁ η) ≫
      eqToHom (congrArg (· ≫ r) h) := by
  cases h
  simp
private theorem revWhiskerRight_congr {Ω ν μ : X}
    {a b : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) (ν) ⟶ rhoObj (μ)}
    (h : a = b) {s r : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) (Ω) ⟶ rhoObj (ν)}
    (η : s ⟶ r) :
    η ▷ b = eqToHom (congrArg (s ≫ ·) h.symm) ≫ (η ▷ a) ≫
      eqToHom (congrArg (r ≫ ·) h) := by
  cases h
  simp

theorem place_place (Δ Ω ν ξ ζ μ : X) (a b u v : List (Letter I))
    {s r : List (Letter I)} (ha : wt D Ω a = Δ) (hb : wt D μ b = ζ)
    (hu : wt D ν u = Ω) (hv : wt D ζ v = ξ) (hs : wt D ξ s = ν) (hr : wt D ξ r = ν)
    (η : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν ξ s hs ⟶ rhoAt ν ξ r hr) :
    place Δ Ω ζ μ a b ha hb
        (by rw [wt_append, wt_append, hv, hs, hu])
        (by rw [wt_append, wt_append, hv, hr, hu])
        (place Ω ν ξ ζ u v hu hv hs hr η) =
      eqToHom (at_congr Δ μ _ _ (by simp [List.append_assoc])) ≫
        place Δ ν ξ μ (a ++ u) (v ++ b)
          (by rw [wt_append, hu, ha]) (by rw [wt_append, hb, hv]) hs hr η ≫
        eqToHom (at_congr Δ μ _ _ (by simp [List.append_assoc])) := by
  subst ζ ξ
  simp only [place,
    TwoSupercategory.whiskerLeft_comp (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)), TwoSupercategory.comp_whiskerRight (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    TwoSupercategory.whiskerLeft_eqToHom k, TwoSupercategory.eqToHom_whiskerRight k,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  rw [revWhiskerLeft_congr (at_comp Δ Ω ν a u ha hu)]
  rw [revWhiskerRight_congr (at_comp (wt D (wt D μ b) v) (wt D μ b) μ v b rfl rfl)]
  rw [TwoSupercategory.comp_whiskerLeft (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    TwoSupercategory.whiskerRight_comp (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)), TwoSupercategory.whisker_assoc (R := k) (B := TwoSRev k (Uqπ D Sc sy hc))]
  simp only [rev_associator _ _ _ (rev_assoc _ _ _),
    rev_associator_inv _ _ _ (rev_assoc _ _ _),
    TwoSupercategory.whiskerLeft_comp (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)), TwoSupercategory.whiskerLeft_eqToHom k,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

theorem at_nil (μ : X) :
    rhoAt (Sc := Sc) (sy := sy) (hc := hc) μ μ [] rfl = 𝟙 (rhoObj μ) :=
  rhoMap_id ⟨μ⟩

private theorem rev_leftUnitor {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : 𝟙 _ ≫ a = a) : (leftUnitor a).hom = eqToHom h := by
  rw [eq_underlying]
  rfl

private theorem rev_leftUnitor_inv {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : 𝟙 _ ≫ a = a) : (leftUnitor a).inv = eqToHom h.symm := by
  rw [eq_underlying]
  rfl

private theorem rev_rightUnitor {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : a ≫ 𝟙 _ = a) : (rightUnitor a).hom = eqToHom h := by
  rw [eq_underlying]
  rfl

private theorem rev_rightUnitor_inv {ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (h : a ≫ 𝟙 _ = a) : (rightUnitor a).inv = eqToHom h.symm := by
  rw [eq_underlying]
  rfl

private theorem at_id_comp (ν μ : X) (s : List (Letter I)) (hs : wt D μ s = ν) :
    𝟙 _ ≫ rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs = rhoAt ν μ s hs := by
  rw [← at_nil, at_comp]
  rfl

private theorem at_comp_id (ν μ : X) (s : List (Letter I)) (hs : wt D μ s = ν) :
    rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ≫ 𝟙 _ = rhoAt ν μ s hs := by
  rw [← at_nil, at_comp]
  exact at_congr ν μ _ _ (List.append_nil s)

theorem place_nil (ν μ : X) (s r : List (Letter I))
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (η : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ rhoAt ν μ r hr) :
    place ν ν μ μ [] [] rfl rfl hs hr η =
      eqToHom (at_congr ν μ _ hs (by simp)) ≫ η ≫
        eqToHom (at_congr ν μ hr _ (by simp)) := by
  unfold place
  change eqToHom _ ≫ (𝟙 _ ◁ (η ▷ 𝟙 _)) ≫ eqToHom _ = _
  rw [TwoSupercategory.whiskerRight_id (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    rev_rightUnitor _ (at_comp_id ν μ s hs), rev_rightUnitor_inv _ (at_comp_id ν μ r hr)]
  simp only [TwoSupercategory.whiskerLeft_comp (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    TwoSupercategory.whiskerLeft_eqToHom k]
  rw [TwoSupercategory.id_whiskerLeft (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    rev_leftUnitor _ (at_id_comp ν μ s hs), rev_leftUnitor_inv _ (at_id_comp ν μ r hr)]
  simp [Category.assoc]

end OddMath.SKM.RhoEvaluator
