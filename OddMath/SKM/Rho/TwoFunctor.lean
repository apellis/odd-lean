import OddMath.SKM.Rho.TargetCoherence
import OddMath.SKM.Rho.QuotientMaps
import StringDiagrams.Super.TwoFunctorStrict

/-!
# Two Functor for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoTwo
open CategoryTheory StringDiagrams Presentation BicategoryStruct RhoWords RhoEvaluator
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

theorem rhoMap₂_eqToHom (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} {f g : a ⟶ b} (e : f = g) :
    rhoMap₂ t ht f g (eqToHom e) = eqToHom (congrArg rhoMap e) := by
  subst g
  exact rhoMap₂_id t ht f

theorem rhoMap₂_associator (t : k) (ht : t ^ 2 = -1)
    {a b c d : UGr D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    HEq (rhoMap₂ t ht _ _ (associator f g h).hom)
      (associator (rhoMap f) (rhoMap g) (rhoMap h)).hom := by
  rw [source_assoc_hom, rhoMap₂_eqToHom, rev_associator (rhoMap f) (rhoMap g) (rhoMap h) (target_assoc f g h)]
  apply (conj_eqToHom_iff_heq _ _
    ((rhoMap_comp (f ≫ g) h).trans (congrArg (· ≫ rhoMap h) (rhoMap_comp f g)))
    ((rhoMap_comp f (g ≫ h)).trans (congrArg (rhoMap f ≫ ·) (rhoMap_comp g h)))).mp
  simp

theorem rhoMap₂_leftUnitor (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    HEq (rhoMap₂ t ht _ _ (leftUnitor f).hom) (leftUnitor (rhoMap f)).hom := by
  rw [source_left_hom, rhoMap₂_eqToHom, rev_leftUnitor (rhoMap f) (target_left f)]
  apply (conj_eqToHom_iff_heq _ _
    ((rhoMap_comp (𝟙 a) f).trans (congrArg (· ≫ rhoMap f) (rhoMap_id a))) rfl).mp
  simp

theorem rhoMap₂_rightUnitor (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    HEq (rhoMap₂ t ht _ _ (rightUnitor f).hom) (rightUnitor (rhoMap f)).hom := by
  rw [source_right_hom, rhoMap₂_eqToHom, rev_rightUnitor (rhoMap f) (target_right f)]
  apply (conj_eqToHom_iff_heq _ _
    ((rhoMap_comp f (𝟙 b)).trans (congrArg (rhoMap f ≫ ·) (rhoMap_id b))) rfl).mp
  simp

private theorem place_left_heq (Ω ν μ : X) (u s r : List (Letter I))
    (hu : wt D ν u = Ω) (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (η : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ rhoAt ν μ r hr) :
    HEq (place Ω ν μ μ u [] hu rfl hs hr η) (rhoAt Ω ν u hu ◁ η) := by
  unfold place
  change HEq (eqToHom _ ≫ (rhoAt Ω ν u hu ◁ (η ▷ 𝟙 _)) ≫ eqToHom _) _
  rw [TwoSupercategory.whiskerRight_id (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    rev_rightUnitor _ (target_right _), rev_rightUnitor_inv _ (target_right _)]
  simp only [TwoSupercategory.whiskerLeft_comp (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    TwoSupercategory.whiskerLeft_eqToHom k, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

private theorem place_right_heq (ν μ : X) (s r v : List (Letter I))
    (hs : wt D (wt D μ v) s = ν) (hr : wt D (wt D μ v) r = ν)
    (η : rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν (wt D μ v) s hs ⟶
      rhoAt ν (wt D μ v) r hr) :
    HEq (place ν ν (wt D μ v) μ [] v rfl rfl hs hr η)
      (η ▷ rhoAt (wt D μ v) μ v rfl) := by
  unfold place
  change HEq (eqToHom _ ≫ (𝟙 _ ◁ (η ▷ rhoAt (wt D μ v) μ v rfl)) ≫ eqToHom _) _
  have es : 𝟙 _ ≫ (rhoAt ν (wt D μ v) s hs ≫ rhoAt (wt D μ v) μ v rfl) =
      rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν (wt D μ v) s hs ≫ rhoAt (wt D μ v) μ v rfl := by
    rw [← rhoMap_comp]
    exact target_left _
  have er : 𝟙 _ ≫ (rhoAt ν (wt D μ v) r hr ≫ rhoAt (wt D μ v) μ v rfl) =
      rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν (wt D μ v) r hr ≫ rhoAt (wt D μ v) μ v rfl := by
    rw [← rhoMap_comp]
    exact target_left _
  rw [TwoSupercategory.id_whiskerLeft (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    rev_leftUnitor _ es, rev_leftUnitor_inv _ er]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

private theorem map₂_heq (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} {f g f' g' : a ⟶ b} (ef : f = f') (eg : g = g')
    {η : f ⟶ g} {η' : f' ⟶ g'} (e : HEq η η') :
    HEq (rhoMap₂ t ht f g η) (rhoMap₂ t ht f' g' η') := by
  subst f' g'
  cases e
  rfl

private theorem source_left_place (μ : X) (u s r : List (Letter I))
    (hst : wt D μ r = wt D μ s) (x : LinDiagram k (ob D μ s) (ob D μ r)) :
    HEq (BicategoryStruct.whiskerLeft (B := UGr D Sc sy hc)
      (psiWordAt (Sc := Sc) (wt D (wt D μ s) u) (wt D μ s) u rfl)
      (show psiWordAt (Sc := Sc) (wt D μ s) μ s rfl ⟶
        psiWordAt (wt D μ s) μ r hst from (pres D Sc).lin x))
      ((pres D Sc).lin
        (LinDiagram.cast (LinDiagram.whisker x (ob D (wt D μ s) u) (wd D μ [])
          (whiskerOK_ob D μ u [] s))
          (ob_whisker D μ u [] s s rfl) (ob_whisker D μ u [] s r hst))) := by
  change HEq ((pres D Sc).wL (ob D (wt D μ s) u) ((pres D Sc).lin x)) _
  erw [Presentation.lin_cast]
  simp only [Presentation.wL, Presentation.whisk_lin,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff, heq_eqToHom_comp_iff,
    heq_comp_eqToHom_iff]
  erw [LinDiagram.whisk_of_ok _ (whiskerOK_ob D μ u [] s)]
  rfl

theorem rhoMap₂_whiskerLeft (t : k) (ht : t ^ 2 = -1)
    {a b c : UGr D Sc sy hc} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    HEq (rhoMap₂ t ht _ _ (f ◁ η)) (rhoMap f ◁ rhoMap₂ t ht g h η) := by
  obtain ⟨u, hu, rfl⟩ := exists_psiWordAt f
  obtain ⟨s, hs, rfl⟩ := exists_psiWordAt g
  obtain ⟨r, hr, rfl⟩ := exists_psiWordAt h
  rcases a with ⟨Ω⟩
  rcases b with ⟨ν⟩
  rcases c with ⟨μ⟩
  change X at Ω ν μ
  dsimp only at hu hs hr
  subst ν Ω
  obtain ⟨x, rfl⟩ := (pres D Sc).lin_surjective η
  have ef : psiWordAt (Sc := Sc) (wt D (wt D μ s) u) (wt D μ s) u rfl ≫
      psiWordAt (wt D μ s) μ s rfl =
      psiWordAt (wt D (wt D μ s) u) μ (u ++ s ++ [])
        (by rw [List.append_nil, wt_append]) := by
    simpa only [List.append_nil] using
      psiWordAt_comp_eq (Sc := Sc) (wt D (wt D μ s) u) (wt D μ s) μ u s rfl rfl
  have eg : psiWordAt (Sc := Sc) (wt D (wt D μ s) u) (wt D μ s) u rfl ≫
      psiWordAt (wt D μ s) μ r hr =
      psiWordAt (wt D (wt D μ s) u) μ (u ++ r ++ [])
        (by rw [List.append_nil, wt_append, hr]) := by
    simpa only [List.append_nil] using
      psiWordAt_comp_eq (Sc := Sc) (wt D (wt D μ s) u) (wt D μ s) μ u r rfl hr
  have H := map₂_heq (sy := sy) (hc := hc) t ht ef eg
    (source_left_place (sy := sy) (hc := hc) μ u s r hr x)
  apply H.trans
  erw [rhoMap₂_lin, rhoMap₂_lin]
  erw [rhoLin_place]
  exact place_left_heq _ _ _ _ _ _ rfl rfl hr _

private theorem source_right_place (μ : X) (s r v : List (Letter I))
    (hst : wt D (wt D μ v) r = wt D (wt D μ v) s)
    (x : LinDiagram k (ob D (wt D μ v) s) (ob D (wt D μ v) r)) :
    HEq (BicategoryStruct.whiskerRight (B := UGr D Sc sy hc)
      (show psiWordAt (Sc := Sc) (wt D (wt D μ v) s) (wt D μ v) s rfl ⟶
        psiWordAt (wt D (wt D μ v) s) (wt D μ v) r hst from (pres D Sc).lin x)
      (psiWordAt (Sc := Sc) (wt D μ v) μ v rfl))
      ((pres D Sc).lin
        (LinDiagram.cast (LinDiagram.whisker x (ob D (wt D (wt D μ v) s) []) (wd D μ v)
          (whiskerOK_ob D μ [] v s))
          (ob_whisker D μ [] v s s rfl) (ob_whisker D μ [] v s r hst))) := by
  change HEq ((pres D Sc).wRAt (show X from wt D (wt D μ v) s) ((pres D Sc).lin x)
    (ob D μ v) rfl hst) _
  erw [Presentation.lin_cast]
  simp only [Presentation.wRAt, Presentation.whisk_lin,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff, heq_eqToHom_comp_iff,
    heq_comp_eqToHom_iff]
  erw [LinDiagram.whisk_of_ok _ (whiskerOK_ob D μ [] v s)]

theorem rhoMap₂_whiskerRight (t : k) (ht : t ^ 2 = -1)
    {a b c : UGr D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    HEq (rhoMap₂ t ht _ _ (η ▷ h)) (rhoMap₂ t ht f g η ▷ rhoMap h) := by
  obtain ⟨s, hs, rfl⟩ := exists_psiWordAt f
  obtain ⟨r, hr, rfl⟩ := exists_psiWordAt g
  obtain ⟨v, hv, rfl⟩ := exists_psiWordAt h
  rcases a with ⟨ν⟩
  rcases b with ⟨ξ⟩
  rcases c with ⟨μ⟩
  change X at ν ξ μ
  dsimp only at hs hr hv
  subst ξ ν
  obtain ⟨x, rfl⟩ := (pres D Sc).lin_surjective η
  have ef := psiWordAt_comp_eq (Sc := Sc) (wt D (wt D μ v) s) (wt D μ v) μ s v rfl rfl
  have eg := psiWordAt_comp_eq (Sc := Sc) (wt D (wt D μ v) s) (wt D μ v) μ r v hr rfl
  have H := map₂_heq (sy := sy) (hc := hc) t ht ef eg
    (source_right_place (sy := sy) (hc := hc) μ s r v hr x)
  apply H.trans
  erw [rhoMap₂_lin, rhoMap₂_lin]
  erw [rhoLin_place]
  exact place_right_heq _ _ _ _ _ rfl hr _

def rhoStrictCore (t : k) (ht : t ^ 2 = -1) :
    TwoSuperfunctor.StrictCore k (UGr D Sc sy hc) (TwoSRev k (Uqπ D Sc sy hc)) where
  obj a := rhoObj a.region
  map := rhoMap
  map₂ {a b f g} := rhoMap₂ (a := a) (b := b) t ht f g
  map₂_id := rhoMap₂_id t ht
  map₂_comp := rhoMap₂_comp t ht
  map₂_add := rhoMap₂_add t ht
  map₂_smul := rhoMap₂_smul t ht
  map₂_mem := rhoMap₂_mem_parity t ht
  map_comp := rhoMap_comp
  map_id := rhoMap_id
  map₂_whiskerLeft := rhoMap₂_whiskerLeft t ht
  map₂_whiskerRight := rhoMap₂_whiskerRight t ht
  map₂_associator := rhoMap₂_associator t ht
  map₂_leftUnitor := rhoMap₂_leftUnitor t ht
  map₂_rightUnitor := rhoMap₂_rightUnitor t ht

def rhoTwo (t : k) (ht : t ^ 2 = -1) :
    TwoSuperfunctor k (UGr D Sc sy hc) (TwoSRev k (Uqπ D Sc sy hc)) :=
  (rhoStrictCore t ht).toTwoSuperfunctor

theorem rhoTwo_isStrict (t : k) (ht : t ^ 2 = -1) :
    (rhoTwo (sy := sy) (hc := hc) t ht).IsStrict :=
  (rhoStrictCore t ht).isStrict

private theorem eqToHom_degree {R : Type*} [CommRing R] {C : Type*} [Category C]
    [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C]
    {A B : C} (p : A = B) : eqToHom p ∈ GradedSupercategory.degree (R := R) A B 0 := by
  subst B
  exact GradedSupercategory.id_mem_degree A

theorem rhoTwo_isGraded (t : k) (ht : t ^ 2 = -1) :
    (rhoTwo (sy := sy) (hc := hc) t ht).IsGraded where
  map₂_mem_degree h := rhoMap₂_mem_degree t ht h
  mapComp_hom_mem_degree f g := by
    change eqToHom (rhoMap_comp f g).symm ∈ _
    exact eqToHom_degree _
  mapId_hom_mem_degree a := by
    change eqToHom (rhoMap_id a).symm ∈ _
    exact eqToHom_degree _
end OddMath.SKM.RhoTwo