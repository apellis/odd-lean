import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirPrincipal

/-! # The actual central probe-to-reservoir bend -/
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
omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
private theorem preE_obj_heq_reservoir
    (T : RouquierFamily (k := k) (B := B) D) (W : X → B) (i : I)
    {a b r r' : X} (h : -b + D.α i = -a) (er : r = r')
    (U : homWeightSector T.obj W a r) (U' : homWeightSector T.obj W a r')
    (hU : HEq U U') :
    HEq ((homContentPreE T W i r h).obj U) ((homContentPreE T W i r' h).obj U') := by
  subst er
  obtain rfl := eq_of_heq hU
  rfl

private theorem preF_obj_heq_weights
    (T : RouquierFamily (k := k) (B := B) D) (W : X → B) (i : I)
    {a a' b b' r r' : X} (ea : a = a') (eb : b = b') (er : r = r')
    (h : -b + D.α i = -a) (h' : -b' + D.α i = -a')
    (U : homWeightSector T.obj W b r) (U' : homWeightSector T.obj W b' r')
    (hU : HEq U U') :
    HEq ((homContentPreF T W i r h).obj U) ((homContentPreF T W i r' h').obj U') := by
  subst ea eb er
  obtain rfl := eq_of_heq hU
  rfl

private theorem postE_obj_heq_weights (T : X → B)
    (W : RouquierFamily (k := k) (B := B) D) (i : I) (β : I →₀ ℕ) (μ : X)
    {m m' n n' : X} (em : m = m') (en : n = n')
    (h : m + D.α i = n) (h' : m' + D.α i = n')
    (U : homWeightSector T W.obj μ m) (U' : homWeightSector T W.obj μ m')
    (hU : HEq U U') :
    HEq ((homContentPostE T W i β μ h).obj U) ((homContentPostE T W i β μ h').obj U') := by
  subst em en
  obtain rfl := eq_of_heq hU
  rfl

section Transport
variable (T W : RouquierFamily (k := k) (B := B) D) (i : I) (β : I →₀ ℕ)
  {a b : X} (hP : -b + D.α i = -a)
local notation "HA" r:max => homWeightSector T.obj W.obj a r
local notation "HB" r:max => homWeightSector T.obj W.obj b r
local notation "EP" r:max => homContentPreE T W.obj i r hP
local notation "FP" r:max => homContentPreF T W.obj i r hP
local notation "AP" r:max => homContentPreAdjunction T W.obj T.leftAdjoints i r hP
local notation "ER" h:max => homContentPostE T.obj W i β b h
local notation "FR" h:max => homContentPostF T.obj W i β b h
local notation "AR" h:max => homContentPostAdjunction T.obj W i β b h

private theorem probeReservoir_of_eq {n n' p : X} (en : n = n')
    (hR : n + D.α i = p) (hR' : n' + D.α i = p)
    (C : ∀ U : HA n', End ((ER hR').obj ((EP n').obj U)))
    (J : HB n ⥤ HB n') (hJ : HEq J (𝟭 (HB n)))
    {S A1 Y A5 Tg : HB n} {U : HB p} {W₀ U₀ : HA n'}
    {V Y₂ Z₉ : HB n} {V₁ : HA n}
    (x₁ : S = A1) (x₂ : A1 = Y) (x₃ : (ER hR).obj Y = U)
    (x₄ : (FR hR).obj U = A5)
    (x₅ : A5 = (FR hR).obj ((ER hR').obj ((EP n').obj W₀)))
    (x₆ : (FR hR).obj ((ER hR').obj ((EP n').obj W₀)) = (FR hR).obj ((ER hR').obj (J.obj V)))
    (x₇ : V = (EP n).obj V₁) (x₈ : V₁ = (FP n).obj Y₂) (x₉ : Y₂ = Z₉)
    (x₁₀ : (FR hR).obj ((ER hR').obj (J.obj Z₉)) = Tg)
    (hY : HEq Y ((EP n').obj W₀)) (hW : HEq W₀ ((FP n).obj Z₉))
    (hU : HEq U₀ ((FP n).obj Z₉))
    (q : (ER hR').obj ((EP n').obj U₀) = (ER hR).obj ((EP n).obj ((FP n).obj Z₉)))
    (s : S = (EP n).obj ((FP n).obj Z₉)) (t : Tg = (FR hR).obj ((ER hR).obj Z₉)) :
    eqToHom x₁ ≫ eqToHom x₂ ≫ (AR hR).unit.app Y ≫
      (FR hR).map (eqToHom x₃) ≫ eqToHom x₄ ≫ eqToHom x₅ ≫
      (FR hR).map (C W₀) ≫ eqToHom x₆ ≫
      (FR hR).map ((ER hR').map (J.map
        (eqToHom x₇ ≫ (EP n).map (eqToHom x₈) ≫ (AP n).counit.app Y₂ ≫ eqToHom x₉))) ≫
      eqToHom x₁₀ =
    eqToHom s ≫ (AR hR).unit.app ((EP n).obj ((FP n).obj Z₉)) ≫
      (FR hR).map ((eqToIso q).inv ≫ C U₀ ≫ (eqToIso q).hom) ≫
      (FR hR).map ((ER hR).map ((AP n).counit.app Z₉)) ≫ eqToHom t.symm := by
  subst en
  obtain rfl : hR' = hR := rfl
  obtain rfl := eq_of_heq hJ
  obtain rfl := eq_of_heq hY
  obtain rfl := eq_of_heq hW
  obtain rfl := eq_of_heq hU
  subst x₁ x₂ x₃ x₄ x₉ x₈ x₇ x₁₀
  simp only [Functor.id_obj, Functor.id_map, eqToHom_refl, eqToIso_refl,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
  rw [(FR hR').map_id, (EP n).map_id]
  let Y := (EP n).obj ((FP n).obj Y₂)
  let V := (FR hR').obj ((ER hR').obj Y)
  let Z := (FR hR').obj ((ER hR').obj Y₂)
  let f : Y ⟶ V := (AR hR').unit.app Y
  let g : End V := (FR hR').map (C ((FP n).obj Y₂))
  let qcap : Y ⟶ Y₂ := (AP n).counit.app Y₂
  let h : V ⟶ Z := (FR hR').map ((ER hR').map qcap)
  let h' : V ⟶ Z := (FR hR').map ((ER hR').map ((𝟙 Y) ≫ qcap))
  change f ≫ (𝟙 V) ≫ g ≫ h' = f ≫ g ≫ h
  have hh : h' = h := by
    dsimp only [h', h]
    rw [Category.id_comp]
  rw [hh]
  simp only [Category.id_comp]

end Transport

namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}

/-- The computed probe cap-path chart uses the canonical inverse-defined
left adjunction of the given probe family. -/
def probeCapFactorIso (i : I) (ν : X) {t : Sector I}
    (hw : StepValid (false, i) true (nextSector (true, i) true t))
    (e : nextSector (false, i) true (nextSector (true, i) true t) = t) (Z : P.H t) :
    (P.pathFunctor (SPath.two (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩)
      (c₂ := ⟨dn i, ν⟩) true true (by trivial) hw e)).obj Z ≅
    (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj
      ((homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj Z) :=
  twoPathEndpointIso true true (by trivial) hw e Z ≪≫
    (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)).mapIso
      (eqToIso (eq_of_heq (P.preF_obj_heq i e.symm (P.muP_preE i t)
        (P.muP_preF i hw) (e.symm ▸ Z)).symm)) ≪≫
    (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)).mapIso
      ((homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)).mapIso
        (twoPathReturnIso true true e Z))

private theorem capImage_probe_endpoint (i : I) (ν : X) {t : Sector I}
    (hw : StepValid (false, i) true (nextSector (true, i) true t))
    (e : nextSector (false, i) true (nextSector (true, i) true t) = t) (Z : P.H t) :
    P.capImage i ν (SPath.two true true (by trivial) hw e) (.nil t) Z =
      (twoPathEndpointIso (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩)
        true true (by trivial) hw e Z).hom ≫
      P.preCap i t (by trivial) hw e.symm (e.symm ▸ Z) ≫
      (twoPathReturnIso true true e Z).hom := by
  unfold capImage
  rw [P.twoZero_two (Z' := e.symm ▸ Z) (hZ := eqRec_heq _ _)]
  rfl

/-- The RP coefficient object after a reservoir cup, compared to its
native post/pre composite. The full formal right sector is transported. -/
private theorem probeToReservoirCoefficient_eq (i : I) (t : Sector I)
    (U : P.H (nextSector (true, i) true t)) :
    P.rpObj i i (nextSector (false, i) false t) (by simp [StepValid, nextSector])
      ((congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)).symm ▸ U) =
    (homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).obj
      ((homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj U) := by
  let tR := nextSector (true, i) false (nextSector (false, i) false t)
  let er := congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)
  have en : P.muM tR = P.muM t := congrArg P.muM (SPath.next_dnUp_false_false (i := i) t)
  have hpre := preE_obj_heq_reservoir P.T P.W.obj i (P.muP_preE i t) en
    (er.symm ▸ U : P.H (nextSector (true, i) true tR)) U (eqRec_heq _ _)
  have hpost := postE_obj_heq_weights P.T.obj P.W i t.1 (P.muP t) en rfl
    (P.muM_postE i (by simp [StepValid, nextSector] :
      StepValid (true, i) false (nextSector (false, i) false t))) (P.muM_postF i t)
    _ _ hpre
  apply eq_of_heq
  simpa only [rpObj, step, tR, er, nextSector, muP] using hpost

def probeToReservoirCoefficientIso (i : I) (t : Sector I)
    (U : P.H (nextSector (true, i) true t)) :
    P.rpObj i i (nextSector (false, i) false t) (by simp [StepValid, nextSector])
      ((congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)).symm ▸ U) ≅
    (homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).obj
      ((homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj U) :=
  eqToIso (probeToReservoirCoefficient_eq i t U)

/-- The native coefficient used by the XP-to-YR bend. This transports
actual coefficient data; it imposes no inverse or bend identity. -/
def probeToReservoirCoefficient (c : P.CrossCoeff) (i : I) (t : Sector I)
    (U : P.H (nextSector (true, i) true t)) :
    End ((homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).obj
      ((homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj U)) :=
  (probeToReservoirCoefficientIso i t U).inv ≫
    c.a i (nextSector (false, i) false t) (by simp [StepValid, nextSector])
      ((congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)).symm ▸ U) ≫
    (probeToReservoirCoefficientIso i t U).hom

/-- The native XP-to-YR bend. Both adjunctions and the actual RP
coefficient data are fixed by the construction. -/
def probeToReservoirBend (c : P.CrossCoeff) (i : I) (t : Sector I) (Z : P.H t) :
    (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj
      ((homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj Z) ⟶
    (homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).obj
      ((homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).obj Z) :=
  (homContentPostAdjunction P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).unit.app _ ≫
    (homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).map
      (probeToReservoirCoefficient c i t
        ((homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj Z)) ≫
    (homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).map
      ((homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).map
        ((homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i (P.muM t)
          (P.muP_preE i t)).counit.app Z))

private theorem pathFunctor_functor_heq_of_nil {a b : Sector I}
    (p : SPath ([] : List (Col I X)) a b) : HEq (P.pathFunctor p) (𝟭 (P.H b)) := by
  cases p
  rfl

attribute [local irreducible] Finsupp.zipWith Finsupp.single Finsupp.onFinset homContentShift contentWeight

/-- The actual XP-to-YR principal-matrix entry is the native mixed
bend on every sector and every full Hom object. -/
theorem sigmaEntry_probeToReservoir (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I) (Z : P.H t) :
    P.sigmaEntry c i i ν
      (SPath.two true true (by trivial) (by simp [StepValid, nextSector])
        (SPath.next_upDn_true_true t))
      (SPath.two false false (by trivial) (by simp [StepValid, nextSector])
        (SPath.next_dnUp_false_false (i := i) t)) Z =
    (probeCapFactorIso i ν (by simp [StepValid, nextSector]) (SPath.next_upDn_true_true t) Z).hom ≫
      probeToReservoirBend c i t Z ≫
      (reservoirCupFactorIso i ν (by trivial) (by simp [StepValid, nextSector])
        (SPath.next_dnUp_false_false (i := i) t) Z).inv := by
  let p : SPath (wd D ν [up i, dn i]) t t :=
    SPath.two true true (by trivial) (by simp [StepValid, nextSector]) (SPath.next_upDn_true_true t)
  let tU := nextSector (false, i) false t
  let tR := nextSector (true, i) false tU
  have hR : StepValid (true, i) false tU := by simp [tU, StepValid, nextSector]
  let q : SPath (wd D ν [dn i, up i]) t t :=
    SPath.two false false (by trivial) hR (SPath.next_dnUp_false_false (i := i) t)
  let qg₁ : SPath ((SKM.sig D).cod (sigL₁ (D := D) i i ν).gen) t t :=
    SPath.two false false (by trivial) hR (SPath.next_dnUp_false_false (i := i) t)
  let m₁ : SPath (sigL₁ (D := D) i i ν).cod.word t t := ((SPath.nil t).append qg₁).append p
  let x := nextSector (true, i) true tR
  have hxv : StepValid (false, i) true x := by simp [x, tR, tU, StepValid, nextSector]
  have hx : nextSector (false, i) true x = t := by
    simp only [x, tR, tU, nextSector, add_tsub_cancel_right]
  let pu₂ : SPath (sigL₂ (D := D) i i ν).left t tU := .cons _ false t trivial (.nil _)
  let pg₂ : SPath ((SKM.sig D).dom (sigL₂ (D := D) i i ν).gen) tU x :=
    .cons _ false tU hR (.cons _ true _ trivial (.nil _))
  let qg₂ : SPath ((SKM.sig D).cod (sigL₂ (D := D) i i ν).gen) tU x := pg₂
  let pv₂ : SPath (sigL₂ (D := D) i i ν).right x t :=
    .cons _ true x hxv ((SPath.nil _).castTgt hx)
  let m₂ : SPath (sigL₂ (D := D) i i ν).cod.word t t := (pu₂.append qg₂).append pv₂
  rw [sigmaEntry_eq_sigmaTerm (m₁ := m₁) (m₂ := m₂) (p₁ := true) (p₂ := true)
    (q₁ := false) (q₂ := false) (hp := SPath.sides_two _ _ _ _ _)
    (hq := SPath.sides_two _ _ _ _ _)
    (hm₁ := by simp [m₁, p, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides])
    (hm₂ := by simp [m₂, pu₂, qg₂, pg₂, pv₂, SPath.sides_append, SPath.sides])]
  let pg₃ : SPath ((SKM.sig D).dom (sigL₃ (D := D) i i ν).gen) t t :=
    SPath.two true true (by trivial) (by simp [StepValid, nextSector]) (SPath.next_upDn_true_true t)
  let pu₃ : SPath (sigL₃ (D := D) i i ν).left t t :=
    SPath.two false false (by trivial) hR (SPath.next_dnUp_false_false (i := i) t)
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
      c.a i tU hR Y := fun _ => rfl
  erw [hcross]
  simp only [qg₁, pg₃]
  rw [zeroTwo_two (Z' := (SPath.next_dnUp_false_false (i := i) t).symm ▸ _)
    (hZ := eqRec_heq _ _)]
  rw [twoZero_two (Z' := (SPath.next_upDn_true_true (i := i) t).symm ▸ _)
    (hZ := eqRec_heq _ _)]
  simp only [cupEntry, capEntry, postCup, preCap]
  simp only [pu₂, pu₃, SPath.two, pathFunctor_cons, pathFunctor_nil, Functor.comp_map, Functor.id_map]
  let J : P.H t ⥤ P.H tR :=
    P.pathFunctor ((SPath.nil _).castTgt (SPath.next_dnUp_false_false (i := i) t))
  have en : P.muM t = P.muM tR := congrArg P.muM (SPath.next_dnUp_false_false (i := i) t).symm
  conv_rhs =>
    simp only [probeCapFactorIso, reservoirCupFactorIso, twoPathEndpointIso,
      twoPathReturnIso, probeToReservoirBend, probeToReservoirCoefficient,
      probeToReservoirCoefficientIso, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, eqToIso.hom, eqToIso.inv,
      eqToHom_map, eqToHom_trans, Category.assoc]
  simp only [Category.assoc]
  dsimp only [step]
  apply probeReservoir_of_eq P.T P.W i t.1 (P.muP_preE i t) en
    (P.muM_postF i t) (P.muM_postE i hR) (fun U => c.a i tU hR U) J
  · exact pathFunctor_functor_heq_of_nil _
  · refine (eqRec_heq _ _).trans ((eqRec_heq _ _).trans ?_)
    exact pathFunctor_two_obj_heq (P := P)
      (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩)
      (SPath.next_dnUp_false_false (i := i) t).symm true true
      (by trivial) (by simp [StepValid, nextSector]) (SPath.next_upDn_true_true (i := i) t)
      (by trivial) pv₂ (by
        change true :: _ = [true]
        rw [(SPath.sides_of_nil _).1]) Z
  · have ea : P.muP x = P.muP (nextSector (true, i) true t) := rfl
    have eb : P.muP (nextSector (false, i) true x) = P.muP t := congrArg P.muP hx
    have er : P.muM x = P.muM t := by
      change P.muM tR = P.muM t
      exact en.symm
    have hh := preF_obj_heq_weights P.T P.W.obj i ea eb er
      (P.muP_preF i hxv) (P.muP_preE i t)
      ((P.pathFunctor ((SPath.nil _).castTgt hx)).obj Z) Z (pathFunctor_obj_heq_of_nil _ Z)
    simpa only [pv₂, pathFunctor_cons, Functor.comp_obj, Functor.id_obj, step,
      x, tR, tU, nextSector, muP, muM] using hh
  · simp only [Functor.id_obj]
    exact eqRec_heq_iff.mpr HEq.rfl
  · simpa only [rpObj, step, tU, tR, nextSector, muP, Functor.id_obj] using
      (probeToReservoirCoefficient_eq (P := P) i t
        ((homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj Z))
  · have hh := postE_obj_heq_weights P.T.obj P.W i t.1 (P.muP t)
      en.symm rfl (P.muM_postE i hR) (P.muM_postF i t)
      ((P.pathFunctor ((SPath.nil _).castTgt (SPath.next_dnUp_false_false (i := i) t))).obj Z) Z
      (pathFunctor_obj_heq_of_nil _ Z)
    have he := congrArg
      ((homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).obj)
      (eq_of_heq hh)
    simpa only [Functor.comp_obj, Functor.id_obj, SPath.castTgt, tU, tR, nextSector, muP] using he

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
