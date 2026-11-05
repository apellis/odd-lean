import OddMath.QuiverHecke.SwappedAssembly.Sigma.ProbeFactorCoordinates

/-! # The reservoir-to-probe central bend -/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

private theorem postE_obj_heq_parameters (T : X → B)
    (W : RouquierFamily (k := k) (B := B) D) (i : I)
    {β β' : I →₀ ℕ} {a a' m m' n n' : X}
    (eβ : β = β') (ea : a = a') (em : m = m') (en : n = n')
    (h : m + D.α i = n) (h' : m' + D.α i = n')
    (U : homWeightSector T W.obj a m) (U' : homWeightSector T W.obj a' m')
    (hU : HEq U U') :
    HEq ((homContentPostE T W i β a h).obj U)
      ((homContentPostE T W i β' a' h').obj U') := by
  subst eβ ea em en
  obtain rfl := eq_of_heq hU
  rfl

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
private theorem preE_obj_heq_parameters
    (T : RouquierFamily (k := k) (B := B) D) (W : X → B) (i : I)
    {a a' b b' r r' : X} (ea : a = a') (eb : b = b') (er : r = r')
    (h : -b + D.α i = -a) (h' : -b' + D.α i = -a')
    (U : homWeightSector T.obj W a r) (U' : homWeightSector T.obj W a' r')
    (hU : HEq U U') :
    HEq ((homContentPreE T W i r h).obj U) ((homContentPreE T W i r' h').obj U') := by
  subst ea eb er
  obtain rfl := eq_of_heq hU
  rfl

private theorem postF_obj_heq_parameters (T : X → B)
    (W : RouquierFamily (k := k) (B := B) D) (i : I)
    {β β' : I →₀ ℕ} {a a' m m' n n' : X}
    (eβ : β = β') (ea : a = a') (em : m = m') (en : n = n')
    (h : m + D.α i = n) (h' : m' + D.α i = n')
    (U : homWeightSector T W.obj a n) (U' : homWeightSector T W.obj a' n')
    (hU : HEq U U') :
    HEq ((homContentPostF T W i β a h).obj U)
      ((homContentPostF T W i β' a' h').obj U') := by
  subst eβ ea em en
  obtain rfl := eq_of_heq hU
  rfl

section Transport
variable (T W : RouquierFamily (k := k) (B := B) D) (i : I)
  {β β' : I →₀ ℕ} {a a' b m n : X}
  (hR : m + D.α i = n) (hP : -b + D.α i = -a) (hP' : -b + D.α i = -a')
local notation "HA" r:max => homWeightSector T.obj W.obj a r
local notation "HA'" r:max => homWeightSector T.obj W.obj a' r
local notation "HB" r:max => homWeightSector T.obj W.obj b r
local notation "EP" => homContentPreE T W.obj i n hP
local notation "FP" => homContentPreF T W.obj i n hP
local notation "AP" => homContentPreAdjunction T W.obj T.leftAdjoints i n hP
local notation "EP'" => homContentPreE T W.obj i n hP'
local notation "ER" => homContentPostE T.obj W i β a hR
local notation "FR" => homContentPostF T.obj W i β a hR
local notation "AR" => homContentPostAdjunction T.obj W i β a hR
local notation "ER'" => homContentPostE T.obj W i β' a' hR

private theorem reservoirProbe_of_eq (eβ : β = β') (ea : a = a')
    (C : ∀ U : HA' m, End ((EP').obj ((ER').obj U)))
    (J : HA n ⥤ HA' n) (hJ : HEq J (𝟭 (HA n)))
    {S A1 Y A5 Tg : HA n} {U : HB n} {W₀ U₀ : HA' m}
    {V Y₂ Z₉ : HA n} {V₁ : HA m}
    (x₁ : S = A1) (x₂ : A1 = Y) (x₃ : (EP).obj Y = U)
    (x₄ : (FP).obj U = A5) (x₅ : A5 = (FP).obj ((EP').obj ((ER').obj W₀)))
    (x₆ : (FP).obj ((EP').obj ((ER').obj W₀)) = (FP).obj ((EP').obj (J.obj V)))
    (x₇ : V = (ER).obj V₁) (x₈ : V₁ = (FR).obj Y₂) (x₉ : Y₂ = Z₉)
    (x₁₀ : (FP).obj ((EP').obj (J.obj Z₉)) = Tg)
    (hY : HEq Y ((ER').obj W₀)) (hW : HEq W₀ ((FR).obj Z₉))
    (hU : HEq U₀ ((FR).obj Z₉))
    (q : (EP').obj ((ER').obj U₀) = (EP).obj ((ER).obj ((FR).obj Z₉)))
    (s : S = (ER).obj ((FR).obj Z₉)) (t : Tg = (FP).obj ((EP).obj Z₉)) :
    eqToHom x₁ ≫ eqToHom x₂ ≫ (AP).unit.app Y ≫
      (FP).map (eqToHom x₃) ≫ eqToHom x₄ ≫ eqToHom x₅ ≫
      (FP).map (C W₀) ≫ eqToHom x₆ ≫
      (FP).map ((EP').map (J.map
        (eqToHom x₇ ≫ (ER).map (eqToHom x₈) ≫ (AR).counit.app Y₂ ≫ eqToHom x₉))) ≫
      eqToHom x₁₀ =
    eqToHom s ≫ (AP).unit.app ((ER).obj ((FR).obj Z₉)) ≫
      (FP).map ((eqToIso q).inv ≫ C U₀ ≫ (eqToIso q).hom) ≫
      (FP).map ((EP).map ((AR).counit.app Z₉)) ≫ eqToHom t.symm := by
  cases eβ
  cases ea
  obtain rfl := eq_of_heq hJ
  obtain rfl := eq_of_heq hY
  obtain rfl := eq_of_heq hW
  obtain rfl := eq_of_heq hU
  subst x₁ x₂ x₃ x₄ x₉ x₈ x₇ x₁₀
  simp only [Functor.id_obj, Functor.id_map, eqToHom_refl, eqToIso_refl,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
  rw [(FP).map_id, (ER).map_id]
  let Y := (ER).obj ((FR).obj Y₂)
  let V := (FP).obj ((EP).obj Y)
  let Z := (FP).obj ((EP).obj Y₂)
  let f : Y ⟶ V := (AP).unit.app Y
  let g : End V := (FP).map (C ((FR).obj Y₂))
  let qcap : Y ⟶ Y₂ := (AR).counit.app Y₂
  let h : V ⟶ Z := (FP).map ((EP).map qcap)
  let h' : V ⟶ Z := (FP).map ((EP).map ((𝟙 Y) ≫ qcap))
  change f ≫ (𝟙 V) ≫ g ≫ h' = f ≫ g ≫ h
  have hh : h' = h := by
    dsimp only [h', h]
    rw [Category.id_comp]
  rw [hh]
  simp only [Category.id_comp]

end Transport

namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}

private theorem reservoirToProbeCoefficient_eq (i : I) (t : Sector I)
    (hb : StepValid (false, i) true t) (hc : StepValid (true, i) false t)
    (U : P.H (nextSector (true, i) false t)) :
    P.prObj i i (nextSector (false, i) true t) hc
      ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ U) =
    (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).obj
      ((homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hc)).obj U) := by
  let tP := nextSector (true, i) true (nextSector (false, i) true t)
  let er := congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)
  have ea : P.muP tP = P.muP t := congrArg P.muP (SPath.next_dnUp_true_true hb)
  have eβ : tP.1 = t.1 := congrArg Prod.fst (SPath.next_dnUp_true_true hb)
  have hp := postE_obj_heq_parameters P.T.obj P.W i eβ ea rfl rfl
    (P.muM_postE i hc) (P.muM_postE i hc)
    (er.symm ▸ U : P.H (nextSector (true, i) false tP)) U (eqRec_heq _ _)
  have he := preE_obj_heq_parameters P.T P.W.obj i ea rfl rfl
    (P.muP_preE i (nextSector (false, i) true t)) (P.muP_preF i hb) _ _ hp
  apply eq_of_heq
  simpa only [prObj, step, tP, er, nextSector, muM] using he

/-- The PR coefficient object in its computed pre/post chart. -/
def reservoirToProbeCoefficientIso (i : I) (t : Sector I)
    (hb : StepValid (false, i) true t) (hc : StepValid (true, i) false t)
    (U : P.H (nextSector (true, i) false t)) :
    P.prObj i i (nextSector (false, i) true t) hc
      ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ U) ≅
    (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).obj
      ((homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hc)).obj U) :=
  eqToIso (reservoirToProbeCoefficient_eq i t hb hc U)

/-- The coefficient data in the PR diagonal crossing, retaining its minus
and its prescribed mixed-interchange conjugation. -/
def reservoirToProbeCoefficient (c : P.CrossCoeff) (i : I) (t : Sector I)
    (hb : StepValid (false, i) true t) (hc : StepValid (true, i) false t)
    (U : P.H (nextSector (true, i) false t)) :
    End ((homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).obj
      ((homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hc)).obj U)) :=
  let U' := (congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ U
  let J := P.mixedJ i i (nextSector (false, i) true t) hc U'
  let γ := reservoirToProbeCoefficientIso i t hb hc U
  γ.inv ≫ (-(J.hom ≫ c.a i (nextSector (false, i) true t) hc U' ≫ J.inv)) ≫ γ.hom

/-- The prescribed RP coefficient object compared to the pre/post object,
including the mixed interchange and the computed return chart. -/
def reservoirToProbeCoefficientChart (i : I) (t : Sector I)
    (hb : StepValid (false, i) true t) (hc : StepValid (true, i) false t)
    (U : P.H (nextSector (true, i) false t)) :
    P.rpObj i i (nextSector (false, i) true t) hc
      ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ U) ≅
    (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).obj
      ((homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hc)).obj U) :=
  (P.mixedJ i i (nextSector (false, i) true t) hc
    ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ U)).symm ≪≫
      reservoirToProbeCoefficientIso i t hb hc U

/-- The PR diagonal is the negative of the given RP coefficient under
its prescribed conjugation. This fixes the sign for coefficient expansion. -/
theorem reservoirToProbeCoefficient_eq_neg (c : P.CrossCoeff) (i : I) (t : Sector I)
    (hb : StepValid (false, i) true t) (hc : StepValid (true, i) false t)
    (U : P.H (nextSector (true, i) false t)) :
    reservoirToProbeCoefficient c i t hb hc U =
      -((reservoirToProbeCoefficientChart i t hb hc U).inv ≫
        c.a i (nextSector (false, i) true t) hc
          ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ U) ≫
        (reservoirToProbeCoefficientChart i t hb hc U).hom) := by
  simp only [reservoirToProbeCoefficient, reservoirToProbeCoefficientChart,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]

/-- The XR-to-YP bend uses the canonical probe unit, the PR diagonal
coefficient, and the reservoir counit. -/
def reservoirToProbeBend (c : P.CrossCoeff) (i : I) (t : Sector I)
    (hb : StepValid (false, i) true t) (hc : StepValid (true, i) false t) (Z : P.H t) :
    (homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hc)).obj
      ((homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hc)).obj Z) ⟶
    (homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).obj
      ((homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).obj Z) :=
  (homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i (P.muM t)
    (P.muP_preF i hb)).unit.app _ ≫
    (homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).map
      (reservoirToProbeCoefficient c i t hb hc
        ((homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hc)).obj Z)) ≫
    (homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).map
      ((homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).map
        ((homContentPostAdjunction P.T.obj P.W i t.1 (P.muP t)
          (P.muM_postE i hc)).counit.app Z))

private theorem pathFunctor_functor_heq_of_nil {a b : Sector I}
    (p : SPath ([] : List (Col I X)) a b) : HEq (P.pathFunctor p) (𝟭 (P.H b)) := by
  cases p
  rfl

attribute [local irreducible] Finsupp.zipWith Finsupp.single Finsupp.onFinset homContentShift contentWeight

/-- The XR-to-YP principal entry is the pre/post bend in its computed
factor charts, for every full Hom object. -/
theorem sigmaEntry_reservoirToProbe (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (hb : StepValid (false, i) true t) (hc : StepValid (true, i) false t) (Z : P.H t) :
    P.sigmaEntry c i i ν
      (SPath.two false false hc (by trivial) (SPath.next_upDn_false_false hc))
      (SPath.two true true hb (by trivial) (SPath.next_dnUp_true_true hb)) Z =
    (reservoirCapFactorIso i ν hc (by trivial) (SPath.next_upDn_false_false hc) Z).hom ≫
      reservoirToProbeBend c i t hb hc Z ≫
      (probeCupFactorIso i ν hb (by trivial) (SPath.next_dnUp_true_true hb) Z).inv := by
  let p : SPath (wd D ν [up i, dn i]) t t :=
    SPath.two false false hc (by trivial) (SPath.next_upDn_false_false hc)
  let tD := nextSector (false, i) true t
  let tP := nextSector (true, i) true tD
  let q : SPath (wd D ν [dn i, up i]) t t :=
    SPath.two true true hb (by trivial) (SPath.next_dnUp_true_true hb)
  let qg₁ : SPath ((SKM.sig D).cod (sigL₁ (D := D) i i ν).gen) t t :=
    SPath.two true true hb (by trivial) (SPath.next_dnUp_true_true hb)
  let m₁ : SPath (sigL₁ (D := D) i i ν).cod.word t t := ((SPath.nil t).append qg₁).append p
  let x := nextSector (true, i) false tP
  have hx : nextSector (false, i) false x = t := by
    have ep := SPath.next_dnUp_true_true hb
    have ec := SPath.next_upDn_false_false hc
    change nextSector (false, i) false (nextSector (true, i) false tP) = t
    rw [show tP = t from ep]
    exact ec
  let pu₂ : SPath (sigL₂ (D := D) i i ν).left t tD := .cons _ true t hb (.nil _)
  let pg₂ : SPath ((SKM.sig D).dom (sigL₂ (D := D) i i ν).gen) tD x :=
    .cons _ true tD trivial (.cons _ false _ hc (.nil _))
  let qg₂ : SPath ((SKM.sig D).cod (sigL₂ (D := D) i i ν).gen) tD x := pg₂
  let pv₂ : SPath (sigL₂ (D := D) i i ν).right x t :=
    .cons _ false x trivial ((SPath.nil _).castTgt hx)
  let m₂ : SPath (sigL₂ (D := D) i i ν).cod.word t t := (pu₂.append qg₂).append pv₂
  rw [sigmaEntry_eq_sigmaTerm (m₁ := m₁) (m₂ := m₂) (p₁ := false) (p₂ := false)
    (q₁ := true) (q₂ := true) (hp := SPath.sides_two _ _ _ _ _)
    (hq := SPath.sides_two _ _ _ _ _)
    (hm₁ := by simp [m₁, p, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides])
    (hm₂ := by simp [m₂, pu₂, qg₂, pg₂, pv₂, SPath.sides_append, SPath.sides])]
  let pg₃ : SPath ((SKM.sig D).dom (sigL₃ (D := D) i i ν).gen) t t :=
    SPath.two false false hc (by trivial) (SPath.next_upDn_false_false hc)
  let pu₃ : SPath (sigL₃ (D := D) i i ν).left t t :=
    SPath.two true true hb (by trivial) (SPath.next_dnUp_true_true hb)
  rw [sigmaTerm_eq_of_paths _ i i ν _ _ m₁ m₂ (.nil t) (.nil t) qg₁ p
    (SPath.eq_of_sides _ _ (by simp [p, SPath.sides_append, SPath.sides_two, SPath.sides]))
    (SPath.eq_of_sides _ _ (by simp [m₁, p, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides]))
    pu₂ pg₂ qg₂ pv₂
    (SPath.eq_of_sides _ _ (by simp [m₁, p, qg₁, pu₂, pg₂, pv₂, SPath.sides_append,
      SPath.sides_two, SPath.sides]))
    (SPath.eq_of_sides _ _ (by simp [m₂, pu₂, qg₂, pg₂, pv₂, SPath.sides_append, SPath.sides]))
    pu₃ pg₃ (.nil t) (.nil t)
    (SPath.eq_of_sides _ _ (by simp [m₂, pu₂, qg₂, pg₂, pv₂, pu₃, pg₃,
      SPath.sides_append, SPath.sides_two, SPath.sides]))
    (SPath.eq_of_sides _ _ (by simp [pu₃, SPath.sides_cast, SPath.sides_append, SPath.sides_two, SPath.sides]))]
  simp only [upwardGens, Generators.image, sigL₁, sigL₂, sigL₃, SKM.lay,
    crossImage, dite_eq_left, cupImage, capImage]
  have hcross : ∀ Y, P.twoTwo _ _ _ _ (P.crossSameEntry c i _ _ _ _) pg₂ qg₂ rfl Y =
      -((P.mixedJ i i tD hc Y).hom ≫ c.a i tD hc Y ≫ (P.mixedJ i i tD hc Y).inv) := fun _ => rfl
  erw [hcross]
  simp only [qg₁, pg₃]
  rw [zeroTwo_two (Z' := (SPath.next_dnUp_true_true hb).symm ▸ _) (hZ := eqRec_heq _ _)]
  rw [twoZero_two (Z' := (SPath.next_upDn_false_false hc).symm ▸ _) (hZ := eqRec_heq _ _)]
  simp only [cupEntry, capEntry, preCup, postCap, preAdjAt]
  simp only [pu₂, pu₃, SPath.two, pathFunctor_cons, pathFunctor_nil, Functor.comp_map, Functor.id_map]
  let J : homWeightSector P.T.obj P.W.obj (P.muP t) (P.muM t) ⥤
      homWeightSector P.T.obj P.W.obj (P.muP tP) (P.muM t) :=
    P.pathFunctor ((SPath.nil _).castTgt (SPath.next_dnUp_true_true hb))
  have ea : P.muP t = P.muP tP := congrArg P.muP (SPath.next_dnUp_true_true hb).symm
  have eβ : t.1 = tP.1 := congrArg Prod.fst (SPath.next_dnUp_true_true hb).symm
  conv_rhs =>
    simp only [reservoirCapFactorIso, probeCupFactorIso, twoPathEndpointIso,
      twoPathReturnIso, reservoirToProbeBend, reservoirToProbeCoefficient,
      reservoirToProbeCoefficientIso, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, eqToIso.hom, eqToIso.inv,
      eqToHom_map, eqToHom_trans, Category.assoc]
  simp only [Category.assoc]
  dsimp only [step]
  apply reservoirProbe_of_eq P.T P.W i (P.muM_postE i hc) (P.muP_preF i hb)
    (P.muP_preE i tD) eβ ea
    (fun U => -((P.mixedJ i i tD hc U).hom ≫ c.a i tD hc U ≫ (P.mixedJ i i tD hc U).inv)) J
  · exact pathFunctor_functor_heq_of_nil _
  · refine (eqRec_heq _ _).trans ((eqRec_heq _ _).trans ?_)
    exact pathFunctor_two_obj_heq (P := P)
      (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩)
      (SPath.next_dnUp_true_true hb).symm false false
      hc (by trivial) (SPath.next_upDn_false_false hc)
      hc pv₂ (by
        change false :: _ = [false]
        rw [(SPath.sides_of_nil _).1]) Z
  · have em : P.muM x = P.muM (nextSector (true, i) false t) := rfl
    have en : P.muM (nextSector (false, i) false x) = P.muM t := congrArg P.muM hx
    have he := postF_obj_heq_parameters P.T.obj P.W i eβ.symm ea.symm em en
      (P.muM_postF i x) (P.muM_postE i hc)
      ((P.pathFunctor ((SPath.nil _).castTgt hx)).obj Z) Z (pathFunctor_obj_heq_of_nil _ Z)
    simpa only [pv₂, pathFunctor_cons, Functor.comp_obj, Functor.id_obj, step,
      x, tP, tD, nextSector, muP, muM] using he
  · simp only [Functor.id_obj]
    exact eqRec_heq_iff.mpr HEq.rfl
  · simpa only [prObj, step, tD, tP, nextSector, muM, Functor.id_obj] using
      (reservoirToProbeCoefficient_eq (P := P) i t hb hc
        ((homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hc)).obj Z))
  · have he := preE_obj_heq_parameters P.T P.W.obj i ea.symm rfl rfl
      (P.muP_preE i tD) (P.muP_preF i hb)
      ((P.pathFunctor ((SPath.nil _).castTgt (SPath.next_dnUp_true_true hb))).obj Z) Z
      (pathFunctor_obj_heq_of_nil _ Z)
    have hh := congrArg
      ((homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).obj) (eq_of_heq he)
    simpa only [Functor.comp_obj, Functor.id_obj, SPath.castTgt, tD, tP, nextSector, muM] using hh

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
