import OddMath.SKM.RouquierHomMixedInterchange
import OddMath.SKM.RouquierShiftedAdjunction
import OddMath.SKM.RouquierNormalizedHomAdjunction

/-!
# The dotless distinct-colour mixed mate `V₀` of the swapped Hom action

Formalizes `docs/Nondegeneracy/SwappedDistinctMixedMates.md` (3), the `V₀`
line of (7), and (9), i.e. the dotless part of the `V_ij` entry of
`SwappedActionAssembly.md` (A14). Here postcomposition by an edge `E'` is
fixed, with the shifts `t` (source side) and `u` (target side), and the
mate is taken with respect to a precomposition adjunction
`homPre E ⊣ homPre F ⋙ S_σ` whose unit and counit are the normalized
words (3) built from a shifted left adjunction `F ⊣ E` of parity `σ`.
These two component formulas are hypotheses of the computation; for the
content adjunction they are `homContentPreAdjunction_unit_app` and the
counit formula of `RouquierNormalizedHomAdjunction.lean`.

The mate of the prescribed comparison `J = homMixedInterchange E E' t u`
is the literal unit–`J`–counit word (`homDistinctMixedPreMate`). Its
coordinate formula (9) is `homDistinctMixedPreMate_eq`: up to the sign
`(-1)^(σu)` it is the even associator between the shift removals.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section Coherence
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c d : B}
include k

private theorem coh_lambda_post (V : b ⟶ c) (E' : c ⟶ d) :
    (leftUnitor (V ≫ E')).inv ≫ (associator (𝟙 b) V E').inv = (leftUnitor V).inv ▷ E' := by
  have h : (Bicategory.leftUnitor (Underlying2.hom1 (R := k) V ≫
        Underlying2.hom1 (R := k) E')).inv ≫
      (Bicategory.associator (𝟙 _) (Underlying2.hom1 (R := k) V)
        (Underlying2.hom1 (R := k) E')).inv =
      Bicategory.whiskerRight (Bicategory.leftUnitor (Underlying2.hom1 (R := k) V)).inv
        (Underlying2.hom1 (R := k) E') := by
    bicategory
  exact congrArg Subtype.val h

private theorem coh_pentagon_post {e : B} (F : b ⟶ a) (E : a ⟶ b) (V : b ⟶ c) (E' : c ⟶ e) :
    (associator (F ≫ E) V E').hom ≫ (associator F E (V ≫ E')).hom ≫
      F ◁ (associator E V E').inv =
    (associator F E V).hom ▷ E' ≫ (associator F (E ≫ V) E').hom := by
  have h : (Bicategory.associator (Underlying2.hom1 (R := k) F ≫ Underlying2.hom1 (R := k) E)
        (Underlying2.hom1 (R := k) V) (Underlying2.hom1 (R := k) E')).hom ≫
      (Bicategory.associator (Underlying2.hom1 (R := k) F) (Underlying2.hom1 (R := k) E)
        (Underlying2.hom1 (R := k) V ≫ Underlying2.hom1 (R := k) E')).hom ≫
      Bicategory.whiskerLeft (Underlying2.hom1 (R := k) F)
        (Bicategory.associator (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) V)
          (Underlying2.hom1 (R := k) E')).inv =
      Bicategory.whiskerRight (Bicategory.associator (Underlying2.hom1 (R := k) F)
          (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) V)).hom
          (Underlying2.hom1 (R := k) E') ≫
        (Bicategory.associator (Underlying2.hom1 (R := k) F)
          (Underlying2.hom1 (R := k) E ≫ Underlying2.hom1 (R := k) V)
          (Underlying2.hom1 (R := k) E')).hom := by
    bicategory
  exact congrArg Subtype.val h

end Coherence

section Slides
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c d : B} {F : b ⟶ a} {E : a ⟶ b} {σ : ZMod 2}
  (A : ShiftedSuperAdjunction (k := k) F E σ)

/-- A homogeneous map of parity `q` slides from below the unit of a shifted left
adjunction of parity `σ` to above it, with the Koszul sign `(-1)^(σq)`. -/
theorem ShiftedSuperAdjunction.unit_slide {x : B} {Y Y' : b ⟶ x} {q : ZMod 2}
    {f : Y ⟶ Y'} (hf : f ∈ parity (R := k) Y Y' q) {Q : b ⟶ x}
    (ι : F ≫ E ≫ Y' ⟶ Q) :
    (leftUnitor Y).inv ≫ A.unit ▷ Y ≫ (associator F E Y).hom ≫ F ◁ E ◁ f ≫ ι =
      sign k (σ * q) •
        (f ≫ (leftUnitor Y').inv ≫ A.unit ▷ Y' ≫ (associator F E Y').hom ≫ ι) := by
  rw [← TwoSupercategory.associator_naturality_right_assoc (R := k) F E f,
    TwoSupercategory.super_interchange_assoc (R := k) A.unit_mem hf, Linear.comp_smul,
    ← TwoSupercategory.leftUnitor_inv_naturality_assoc (R := k) f, koszulSign_smul (R := k)]

/-- The zigzag on `F`, whiskered by `H` and then by a post edge `E'`, in the form
in which it occurs in the mate `V₀`: it is the associator `(F ≫ H) ≫ E' ≅ F ≫ (H ≫ E')`. -/
theorem ShiftedSuperAdjunction.left_triangle_post (H : a ⟶ c) (E' : c ⟶ d) :
    (leftUnitor ((F ≫ H) ≫ E')).inv ≫ A.unit ▷ ((F ≫ H) ≫ E') ≫
      (associator F E ((F ≫ H) ≫ E')).hom ≫ F ◁ (associator E (F ≫ H) E').inv ≫
      F ◁ ((associator E F H).inv ▷ E') ≫ F ◁ ((A.counit ▷ H) ▷ E') ≫
      F ◁ ((leftUnitor H).hom ▷ E') =
    (associator F H E').hom := by
  have hΓ := congrArg (fun t => t ▷ E' ≫ (associator F H E').hom)
    (A.left_triangle_whiskerRight H)
  simp only [TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.id_whiskerRight (R := k), Category.id_comp, Category.assoc] at hΓ
  refine Eq.trans ?_ hΓ
  simp only [TwoSupercategory.associator_naturality_middle_assoc (R := k),
    TwoSupercategory.associator_naturality_middle (R := k)]
  rw [TwoSupercategory.whiskerRight_comp (R := k) A.unit (F ≫ H) E']
  simp only [Category.assoc]
  rw [reassoc_of% (coh_lambda_post (k := k) (F ≫ H) E'),
    reassoc_of% (coh_pentagon_post (k := k) F E (F ≫ H) E')]

end Slides

section Mate
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} {F : b ⟶ a} (E : a ⟶ b) (E' : c ⟶ d) {σ : ZMod 2} (t u : ZMod 2)
  (adjd : homPre (k := k) (c := d) E ⊣ homPre (k := k) F ⋙ homParityShift (k := k) σ)
  (adjc : homPre (k := k) (c := c) E ⊣ homPre (k := k) F ⋙ homParityShift (k := k) σ)

/-- The mate `V₀ = M(J)` of (7): the target pre unit, `J`, and the post-whiskered
source pre counit, each with its own shift. -/
def homDistinctMixedPreMate (H : a ⟶ c) :
    (homParityShift (k := k) t).obj ((homParityShift (k := k) σ).obj (F ≫ H) ≫ E') ⟶
      (homParityShift (k := k) σ).obj (F ≫ (homParityShift (k := k) u).obj (H ≫ E')) :=
  adjd.unit.app ((homParityShift (k := k) t).obj
      ((homParityShift (k := k) σ).obj (F ≫ H) ≫ E')) ≫
    (homPre (k := k) F ⋙ homParityShift (k := k) σ).map
      ((homMixedInterchange (k := k) E E' t u
          ((homParityShift (k := k) σ).obj (F ≫ H))).hom ≫
        (homParityShift (k := k) u).map (adjc.counit.app H ▷ E'))

variable {E E' t u adjd adjc}

/-- The coordinate formula (9), solved for `V₀`: the two endpoint shift removals
around the even associator, with the residual sign `(-1)^(σu)`. The unit and
counit of the two precomposition adjunctions are the normalized words (3) of
the shifted left adjunction `A`. -/
theorem homDistinctMixedPreMate_eq (A : ShiftedSuperAdjunction (k := k) F E σ)
    (hunit : ∀ Y : b ⟶ d, adjd.unit.app Y = (leftUnitor Y).inv ≫ A.unit ▷ Y ≫
      (associator F E Y).hom ≫ ((homParityShiftDatum (k := k) σ).iso (F ≫ E ≫ Y)).inv)
    (hcounit : ∀ H : a ⟶ c, adjc.counit.app H = koszulSign σ σ •
      (E ◁ ((homParityShiftDatum (k := k) σ).iso (F ≫ H)).hom ≫
        (associator E F H).inv ≫ A.counit ▷ H ≫ (leftUnitor H).hom))
    (H : a ⟶ c) :
    homDistinctMixedPreMate E E' t u adjd adjc H = sign k (σ * u) •
      (((homParityShiftDatum (k := k) t).iso
          ((homParityShift (k := k) σ).obj (F ≫ H) ≫ E')).hom ≫
        ((homParityShiftDatum (k := k) σ).iso (F ≫ H)).hom ▷ E' ≫
        (associator F H E').hom ≫
        F ◁ ((homParityShiftDatum (k := k) u).iso (H ≫ E')).inv ≫
        ((homParityShiftDatum (k := k) σ).iso
          (F ≫ (homParityShift (k := k) u).obj (H ≫ E'))).inv) := by
  set Z := (homParityShift (k := k) σ).obj (F ≫ H) with hZ
  set φ := ((homParityShiftDatum (k := k) σ).iso (F ≫ H)).hom with hφ
  obtain ⟨ε, hε⟩ : ∃ ε : E ≫ Z ⟶ H, adjc.counit.app H = ε := ⟨_, rfl⟩
  -- the counit, with the scalar written in `k`
  have hε' : ε = sign k (σ * σ) •
      (E ◁ φ ≫ (associator E F H).inv ≫ A.counit ▷ H ≫ (leftUnitor H).hom) := by
    rw [← hε, hcounit, koszulSign_smul (R := k)]
  have hεmem : ε ∈ parity (R := k) _ _ 0 := by
    rw [hε']
    apply Submodule.smul_mem
    have h := comp_mem (comp_mem (comp_mem
      (TwoSupercategory.whiskerLeft_mem E
        ((homParityShiftDatum (k := k) σ).hom_mem (F ≫ H)))
      (inv_mem (associator E F H) (TwoSupercategory.associator_hom_mem (R := k) E F H)))
      (TwoSupercategory.whiskerRight_mem H A.counit_mem))
      (TwoSupercategory.leftUnitor_hom_mem (R := k) H)
    simp only [add_zero, zmod2_add_self] at h
    simpa only [Category.assoc] using h
  -- `J` followed by the shifted counit
  have hg : (homMixedInterchange (k := k) E E' t u Z).hom ≫
      (homParityShift (k := k) u).map (ε ▷ E') =
      E ◁ ((homParityShiftDatum (k := k) t).iso (Z ≫ E')).hom ≫ (associator E Z E').inv ≫
        ε ▷ E' ≫ ((homParityShiftDatum (k := k) u).iso (H ≫ E')).inv := by
    have hn := (homParityShiftDatum (k := k) u).inv_naturality
      (TwoSupercategory.whiskerRight_mem E' hεmem)
    rw [mul_zero, sign_zero, one_smul] at hn
    simp only [homMixedInterchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, homPre,
      Category.assoc]
    rw [hn]
  have hgmem : E ◁ ((homParityShiftDatum (k := k) t).iso (Z ≫ E')).hom ≫
      (associator E Z E').inv ≫ ε ▷ E' ≫
        ((homParityShiftDatum (k := k) u).iso (H ≫ E')).inv ∈
      parity (R := k) _ _ (t + u) := by
    have h := comp_mem (comp_mem (comp_mem
      (TwoSupercategory.whiskerLeft_mem E ((homParityShiftDatum (k := k) t).hom_mem (Z ≫ E')))
      (inv_mem (associator E Z E') (TwoSupercategory.associator_hom_mem (R := k) E Z E')))
      (TwoSupercategory.whiskerRight_mem E' hεmem))
      ((homParityShiftDatum (k := k) u).inv_mem (H ≫ E'))
    simp only [add_zero] at h
    simpa only [Category.assoc] using h
  -- removal of the final output shift through `R(J)`
  have hδ := (homParityShiftDatum (k := k) σ).inv_naturality
    (TwoSupercategory.whiskerLeft_mem F hgmem)
  have hδ' : ((homParityShiftDatum (k := k) σ).iso
      (F ≫ E ≫ (homParityShift (k := k) t).obj (Z ≫ E'))).inv ≫
      (homParityShift (k := k) σ).map (F ◁ (E ◁ ((homParityShiftDatum (k := k) t).iso
        (Z ≫ E')).hom ≫ (associator E Z E').inv ≫ ε ▷ E' ≫
          ((homParityShiftDatum (k := k) u).iso (H ≫ E')).inv)) =
      sign k (σ * (t + u)) • (F ◁ (E ◁ ((homParityShiftDatum (k := k) t).iso
        (Z ≫ E')).hom ≫ (associator E Z E').inv ≫ ε ▷ E' ≫
          ((homParityShiftDatum (k := k) u).iso (H ≫ E')).inv) ≫
        ((homParityShiftDatum (k := k) σ).iso
          (F ≫ (homParityShift (k := k) u).obj (H ≫ E'))).inv) := by
    rw [hδ, smul_smul, sign_mul_self, one_smul]
  -- the middle associator, moved past the source shift removal
  have hmid : F ◁ (associator E Z E').inv ≫ F ◁ ((E ◁ φ) ▷ E') =
      F ◁ E ◁ (φ ▷ E') ≫ F ◁ (associator E (F ≫ H) E').inv := by
    rw [← TwoSupercategory.whiskerLeft_comp (R := k),
      ← TwoSupercategory.whiskerLeft_comp (R := k),
      TwoSupercategory.associator_inv_naturality_middle (R := k)]
  have hφmem : φ ▷ E' ∈ parity (R := k) _ _ σ :=
    TwoSupercategory.whiskerRight_mem E'
      ((homParityShiftDatum (k := k) σ).hom_mem (F ≫ H))
  unfold homDistinctMixedPreMate
  rw [hunit, hε]
  show (_ ≫ _ ≫ _ ≫ _) ≫ (homParityShift (k := k) σ).map (F ◁ _) = _
  simp only [Category.assoc]
  rw [hg, hδ']
  simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc, Linear.comp_smul]
  rw [A.unit_slide ((homParityShiftDatum (k := k) t).hom_mem (Z ≫ E'))]
  rw [hε']
  simp only [TwoSupercategory.smul_whiskerRight (R := k),
    TwoSupercategory.whiskerLeft_smul (R := k), Linear.comp_smul, Linear.smul_comp,
    TwoSupercategory.comp_whiskerRight (R := k), TwoSupercategory.whiskerLeft_comp (R := k),
    Category.assoc]
  rw [reassoc_of% hmid, A.unit_slide hφmem, reassoc_of% (A.left_triangle_post H E')]
  simp only [smul_smul, Linear.comp_smul]
  congr 1
  simp only [← sign_add]
  congr 1
  rcases parity_eq_zero_or_one σ with hσ | hσ <;>
    rcases parity_eq_zero_or_one t with ht | ht <;>
    rcases parity_eq_zero_or_one u with hu | hu <;>
    · rw [hσ, ht, hu]; decide

end Mate

section Content
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (W : X → B)
  (i : I) (muM : X) {muP nuP : X} (h : -nuP + D.α i = -muP)

/-- The counit of the content-shifted precomposition adjunction for arbitrary shifted
left adjunctions: the signed counit word (3). For `T.leftAdjoints` this is
`homContentPreAdjunction_leftAdjoints_counit_app`. -/
theorem homContentPreAdjunction_counit_app (L : RouquierLeftAdjoints (k := k) T)
    (Z : homWeightSector T.obj W nuP muM) :
    (homContentPreAdjunction T W L i muM h).counit.app Z =
      koszulSign (leftAdjParity D i (-nuP)) (leftAdjParity D i (-nuP)) •
        (T.E i h ◁ ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).iso
          (T.F i h ≫ Z)).hom ≫
          (associator (T.E i h) (T.F i h) Z).inv ≫
          (L.adjL i h).counit ▷ Z ≫ (leftUnitor Z).hom) := by
  let p := leftAdjParity D i (-nuP)
  let P := homParityShiftDatum (k := k) (C := T.obj (-nuP) ⟶ W muM) p
  let S := homParityShift (k := k) (C := T.obj (-nuP) ⟶ W muM) p
  let A := L.adjL i h
  have hexp : (homContentPreAdjunction T W L i muM h).counit.app Z =
      T.E i h ◁ (homParityShiftCommute (homPre (k := k) (T.F i h)) p).hom.app Z ≫
        (homParityShiftSquare (k := k) p).inv.app (T.E i h ≫ T.F i h ≫ S.obj Z) ≫
        S.map (homPreShiftCounitApp A P (S.obj Z)) ≫
        (homParityShiftSquare (k := k) p).hom.app Z := by
    simp only [homContentPreAdjunction, Adjunction.ofNatIsoRight, Adjunction.ofNatIsoLeft,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Adjunction.comp_counit_app]
    dsimp only [homContentPreE, homContentPreF, homWeightSector]
    simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.rightUnitor_inv_app,
      Category.id_comp, Functor.comp_obj, Iso.symm_inv]
    change _ ≫ (_ ≫ 𝟙 _) ≫ _ ≫ _ = _
    rw [Category.comp_id, homParityShiftAdjunction_counit_app]
    rfl
  rw [hexp]
  rw [homParityShiftSquare_inv_map_even p _ Z _ (homPreShiftCounitApp_mem A P _)]
  have hn := (homPreShiftCounit A P).naturality (P.iso Z).hom
  change S.map (T.E i h ◁ T.F i h ◁ (P.iso Z).hom) ≫ homPreShiftCounitApp A P Z =
    homPreShiftCounitApp A P (S.obj Z) ≫ (P.iso Z).hom at hn
  rw [← hn]
  unfold homPreShiftCounitApp
  rw [reassoc_of% (P.hom_naturality
    (TwoSupercategory.whiskerLeft_mem (T.E i h)
      (TwoSupercategory.whiskerLeft_mem (T.F i h) (P.hom_mem Z))))]
  dsimp only [P]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [homParityShiftCommute_hom_app]
  simp only [homPre, TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
  rw [← Category.assoc (T.E i h ◁ T.F i h ◁ _),
    ← TwoSupercategory.whiskerLeft_comp (R := k),
    ← TwoSupercategory.whiskerLeft_comp (R := k), Iso.inv_hom_id,
    TwoSupercategory.whiskerLeft_id (R := k), TwoSupercategory.whiskerLeft_id (R := k),
    Category.id_comp]
  rw [koszulSign_smul (R := k)]

/-- The coordinate formula (9) for the content-shifted precomposition adjunctions of a
factor family, at an arbitrary post edge `E'` with shifts `t`, `u`. -/
theorem homContentDistinctMixedPreMate_eq (L : RouquierLeftAdjoints (k := k) T)
    {muM' : X} (E' : W muM ⟶ W muM') (t u : ZMod 2)
    (H : homWeightSector T.obj W nuP muM) :
    homDistinctMixedPreMate (T.E i h) E' t u (homContentPreAdjunction T W L i muM' h)
        (homContentPreAdjunction T W L i muM h) H =
      sign k (leftAdjParity D i (-nuP) * u) •
        (((homParityShiftDatum (k := k) t).iso
            ((homParityShift (k := k) (leftAdjParity D i (-nuP))).obj (T.F i h ≫ H) ≫
              E')).hom ≫
          ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).iso
            (T.F i h ≫ H)).hom ▷ E' ≫
          (associator (T.F i h) H E').hom ≫
          T.F i h ◁ ((homParityShiftDatum (k := k) u).iso (H ≫ E')).inv ≫
          ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).iso
            (T.F i h ≫ (homParityShift (k := k) u).obj (H ≫ E'))).inv) :=
  homDistinctMixedPreMate_eq (L.adjL i h)
    (fun Y => homContentPreAdjunction_unit_app T W i muM' h L Y)
    (fun Z => homContentPreAdjunction_counit_app T W i muM h L Z) H

end Content
end OddMath.SKM
