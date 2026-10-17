/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PsiQuotient
import StringDiagrams.Super.TwoFunctorStrict

/-!
# The strict graded 2-superfunctor ψ

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 9.4, the strict graded functor constructed in its proof:
`psiTwo : TwoSuperfunctor k (UGr D Sc sy hc) (TwoSOp k (Uqπ D Sc sy hc))`.
It uses the established weight and word assignments and the homwise quotient
maps descended from the presentation ideal. Both whiskering laws hold for
arbitrary quotient 2-morphisms; their signed content is `psiLin_place`.
The associator and unitors are transported through equality morphisms.

The hypotheses are a purely even commutative coefficient ring, homogeneous
parameters, a symmetrizer, compatible `CScalars`, and `t² = -1`. No preservation
or coherence assumption is imposed. `psiTwo_isStrict` and `psiTwo_isGraded`
certify the comparison maps and the integer grading. The extension to the
shifted source and the inverse asserted in Proposition 9.4 are not constructed
in this module.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

private theorem psiTwo_eq_underlying {a b : UGr D Sc sy hc}
    {f g : psiObj a ⟶ psiObj b} (e : f = g) :
    SOp.unsop (eqToHom e) = eqToHom
      (congrArg (fun x => (pres D Sc).obj (SOp.unop x).obj.obj.obj) e.symm) := by
  cases e
  rfl

private theorem psiMap_leftUnitor {a b : UGr D Sc sy hc} (f : a ⟶ b)
    (e : 𝟙 (psiObj a) ≫ psiMap f = psiMap f) :
    (leftUnitor (psiMap f)).hom = eqToHom e := by
  apply SOp.hom_ext
  rw [psiTwo_eq_underlying]
  rfl

private theorem psiMap_rightUnitor {a b : UGr D Sc sy hc} (f : a ⟶ b)
    (e : psiMap f ≫ 𝟙 (psiObj b) = psiMap f) :
    (rightUnitor (psiMap f)).hom = eqToHom e := by
  apply SOp.hom_ext
  rw [psiTwo_eq_underlying]
  rfl

private theorem psiMap_associator {a b c d : UGr D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    (e : (psiMap f ≫ psiMap g) ≫ psiMap h = psiMap f ≫ psiMap g ≫ psiMap h) :
    (associator (psiMap f) (psiMap g) (psiMap h)).hom = eqToHom e := by
  apply SOp.hom_ext
  rw [psiTwo_eq_underlying]
  rfl

private theorem source_assoc {a b c d : UGr D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : (f ≫ g) ≫ h = f ≫ g ≫ h :=
  Presentation.Bicat.Hom.ext (Obj.tensor_assoc f.obj g.obj h.obj)
private theorem source_left {a b : UGr D Sc sy hc} (f : a ⟶ b) : 𝟙 a ≫ f = f :=
  Presentation.Bicat.Hom.ext (Obj.nil_tensor f.start_eq)
private theorem source_right {a b : UGr D Sc sy hc} (f : a ⟶ b) : f ≫ 𝟙 b = f :=
  Presentation.Bicat.Hom.ext (Obj.tensor_nil f.obj b.region)

private theorem target_assoc {a b c d : UGr D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (psiMap f ≫ psiMap g) ≫ psiMap h = psiMap f ≫ psiMap g ≫ psiMap h := by
  rw [← psiMap_comp, ← psiMap_comp, ← psiMap_comp, ← psiMap_comp, source_assoc]
private theorem target_left {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    𝟙 (psiObj a) ≫ psiMap f = psiMap f := by
  rw [← psiMap_id, ← psiMap_comp, source_left]
private theorem target_right {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    psiMap f ≫ 𝟙 (psiObj b) = psiMap f := by
  rw [← psiMap_id, ← psiMap_comp, source_right]

private theorem source_assoc_hom {a b c d : UGr D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (associator f g h).hom = eqToHom (source_assoc f g h) := by
  have he : associator f g h = eqToIso (source_assoc f g h) :=
    Presentation.Bicat.isoOfEq_eq_eqToIso (Obj.tensor_assoc f.obj g.obj h.obj) _
  exact congrArg (fun x => x.hom) he
private theorem source_left_hom {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    (leftUnitor f).hom = eqToHom (source_left f) := by
  have he : leftUnitor f = eqToIso (source_left f) :=
    Presentation.Bicat.isoOfEq_eq_eqToIso (a := 𝟙 a ≫ f) (b := f)
      (Obj.nil_tensor f.start_eq) _
  exact congrArg (fun x => x.hom) he
private theorem source_right_hom {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    (rightUnitor f).hom = eqToHom (source_right f) := by
  have he : rightUnitor f = eqToIso (source_right f) :=
    Presentation.Bicat.isoOfEq_eq_eqToIso (Obj.tensor_nil f.obj b.region) _
  exact congrArg (fun x => x.hom) he

/-- ψ sends source equality morphisms to the induced target equality morphisms. -/
theorem psiMap₂_eqToHom (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    {a b : UGr D Sc sy hc} {f g : a ⟶ b} (e : f = g) :
    psiMap₂ t ht cs f g (eqToHom e) = eqToHom (congrArg psiMap e) := by
  subst g
  exact psiMap₂_id t ht cs f

/-- ψ preserves the associator up to its composition equalities. -/
theorem psiMap₂_associator (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    {a b c d : UGr D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    HEq (psiMap₂ t ht cs _ _ (associator f g h).hom)
      (associator (psiMap f) (psiMap g) (psiMap h)).hom := by
  rw [source_assoc_hom, psiMap₂_eqToHom, psiMap_associator f g h (target_assoc f g h)]
  apply (conj_eqToHom_iff_heq _ _
    ((psiMap_comp (f ≫ g) h).trans (congrArg (· ≫ psiMap h) (psiMap_comp f g)))
    ((psiMap_comp f (g ≫ h)).trans (congrArg (psiMap f ≫ ·) (psiMap_comp g h)))).mp
  simp

/-- ψ preserves the left unitor up to its identity and composition equalities. -/
theorem psiMap₂_leftUnitor (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    HEq (psiMap₂ t ht cs _ _ (leftUnitor f).hom) (leftUnitor (psiMap f)).hom := by
  rw [source_left_hom, psiMap₂_eqToHom, psiMap_leftUnitor f (target_left f)]
  apply (conj_eqToHom_iff_heq _ _
    ((psiMap_comp (𝟙 a) f).trans (congrArg (· ≫ psiMap f) (psiMap_id a))) rfl).mp
  simp

/-- ψ preserves the right unitor up to its identity and composition equalities. -/
theorem psiMap₂_rightUnitor (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    HEq (psiMap₂ t ht cs _ _ (rightUnitor f).hom) (rightUnitor (psiMap f)).hom := by
  rw [source_right_hom, psiMap₂_eqToHom, psiMap_rightUnitor f (target_right f)]
  apply (conj_eqToHom_iff_heq _ _
    ((psiMap_comp f (𝟙 b)).trans (congrArg (psiMap f ≫ ·) (psiMap_id b))) rfl).mp
  simp

private theorem place_left_heq (Ω ν μ : X) (u s r : List (Letter I))
    (hu : wt D ν u = Ω) (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (η : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ psiAt ν μ r hr) :
    HEq (psiPlace Ω ν μ μ u [] hu rfl hs hr η) (psiAt Ω ν u hu ◁ η) := by
  simp only [psiPlace, psiWhiskerRight_nil, psiWhiskerLeft,
    TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.whiskerLeft_eqToHom k,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

private theorem place_right_heq (ν μ : X) (s r v : List (Letter I))
    (hs : wt D (wt D μ v) s = ν) (hr : wt D (wt D μ v) r = ν)
    (η : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν (wt D μ v) s hs ⟶
      psiAt ν (wt D μ v) r hr) :
    HEq (psiPlace ν ν (wt D μ v) μ [] v rfl rfl hs hr η)
      (η ▷ psiAt (wt D μ v) μ v rfl) := by
  simp only [psiPlace, psiWhiskerLeft_nil, psiWhiskerRight,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

private theorem map₂_heq (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    {a b : UGr D Sc sy hc} {f g f' g' : a ⟶ b} (ef : f = f') (eg : g = g')
    {η : f ⟶ g} {η' : f' ⟶ g'} (e : HEq η η') :
    HEq (psiMap₂ t ht cs f g η) (psiMap₂ t ht cs f' g' η') := by
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

/-- ψ preserves left whiskering on arbitrary quotient 2-morphisms. -/
theorem psiMap₂_whiskerLeft (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    {a b c : UGr D Sc sy hc} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    HEq (psiMap₂ t ht cs _ _ (f ◁ η)) (psiMap f ◁ psiMap₂ t ht cs g h η) := by
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
  have H := map₂_heq (sy := sy) (hc := hc) t ht cs ef eg
    (source_left_place (sy := sy) (hc := hc) μ u s r hr x)
  apply H.trans
  erw [psiMap₂_lin, psiMap₂_lin]
  erw [psiLin_place]
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

/-- ψ preserves right whiskering on arbitrary quotient 2-morphisms. -/
theorem psiMap₂_whiskerRight (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    {a b c : UGr D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    HEq (psiMap₂ t ht cs _ _ (η ▷ h)) (psiMap₂ t ht cs f g η ▷ psiMap h) := by
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
  have H := map₂_heq (sy := sy) (hc := hc) t ht cs ef eg
    (source_right_place (sy := sy) (hc := hc) μ s r v hr x)
  apply H.trans
  erw [psiMap₂_lin, psiMap₂_lin]
  erw [psiLin_place]
  exact place_right_heq _ _ _ _ _ rfl hr _

/-- Strict data for ψ on the graded presentation and its shifted super-opposite. -/
def psiStrictCore (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) :
    TwoSuperfunctor.StrictCore k (UGr D Sc sy hc) (TwoSOp k (Uqπ D Sc sy hc)) where
  obj := psiObj
  map := psiMap
  map₂ {a b f g} := psiMap₂ (a := a) (b := b) t ht cs f g
  map₂_id := psiMap₂_id t ht cs
  map₂_comp := psiMap₂_comp t ht cs
  map₂_add := psiMap₂_add t ht cs
  map₂_smul := psiMap₂_smul t ht cs
  map₂_mem := psiMap₂_mem_parity t ht cs
  map_comp := psiMap_comp
  map_id := psiMap_id
  map₂_whiskerLeft := psiMap₂_whiskerLeft t ht cs
  map₂_whiskerRight := psiMap₂_whiskerRight t ht cs
  map₂_associator := psiMap₂_associator t ht cs
  map₂_leftUnitor := psiMap₂_leftUnitor t ht cs
  map₂_rightUnitor := psiMap₂_rightUnitor t ht cs

/-- The 2-superfunctor ψ from the graded presentation to its shifted super-opposite. -/
def psiTwo (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) :
    TwoSuperfunctor k (UGr D Sc sy hc) (TwoSOp k (Uqπ D Sc sy hc)) :=
  (psiStrictCore t ht cs).toTwoSuperfunctor

/-- ψ has equality isomorphisms as its composition and identity comparisons. -/
theorem psiTwo_isStrict (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) :
    (psiTwo (sy := sy) (hc := hc) t ht cs).IsStrict :=
  (psiStrictCore t ht cs).isStrict

private theorem eqToHom_degree {R : Type*} [CommRing R] {C : Type*} [Category C]
    [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C]
    {A B : C} (p : A = B) : eqToHom p ∈ GradedSupercategory.degree (R := R) A B 0 := by
  subst B
  exact GradedSupercategory.id_mem_degree A

/-- ψ preserves integer degrees and its comparisons have degree zero. -/
theorem psiTwo_isGraded (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) :
    (psiTwo (sy := sy) (hc := hc) t ht cs).IsGraded where
  map₂_mem_degree h := psiMap₂_mem_degree t ht cs h
  mapComp_hom_mem_degree f g := by
    change eqToHom (psiMap_comp f g).symm ∈ _
    exact eqToHom_degree _
  mapId_hom_mem_degree a := by
    change eqToHom (psiMap_id a).symm ∈ _
    exact eqToHom_degree _
end OddMath.SKM