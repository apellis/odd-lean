import OddMath.QuiverHecke.SwappedAssembly.Sigma.ProbeFactorCoordinates
import OddMath.SKM.RouquierHomPreCoordinates

/-! # The probe principal block in factor coordinates

Brundan–Ellis, Definition 1.5, (1.13)–(1.14): the pure probe entry of the
constructed sideways crossing is the prescribed precomposition mate.
Its factor chart retains the negative leftward crossing and the exceptional
height-zero normalization coefficient.
-/
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
section Transport
variable (T : RouquierFamily (k := k) (B := B) D) (W : X → B) (i : I)
  (μ : X)
local notation "H" a:max => homWeightSector T.obj W a μ
local notation "E" h:max => homContentPreE T W i μ h
local notation "F" h:max => homContentPreF T W i μ h
local notation "A" h:max => homContentPreAdjunction T W T.leftAdjoints i μ h

private theorem prePrincipal_of_eq {m m' n n' p : X} (em : m = m') (en : n = n')
    (hl : -n + D.α i = -m) (hl' : -n' + D.α i = -m')
    (hu : -p + D.α i = -n) (hu' : -p + D.α i = -n')
    (J : H n ⥤ H n') (hJ : HEq J (𝟭 (H n)))
    {S A1 Y A5 Tg : H n} {U : H p} {W₀ : H m'}
    {V Y₂ Z₉ : H n} {V₁ : H m}
    (x₁ : S = A1) (x₂ : A1 = Y) (x₃ : (E hu).obj Y = U)
    (x₄ : (F hu).obj U = A5)
    (x₅ : A5 = (F hu).obj ((E hu').obj ((E hl').obj W₀)))
    (x₆ : (F hu).obj ((E hu').obj ((E hl').obj W₀)) = (F hu).obj ((E hu').obj (J.obj V)))
    (x₇ : V = (E hl).obj V₁) (x₈ : V₁ = (F hl).obj Y₂) (x₉ : Y₂ = Z₉)
    (x₁₀ : (F hu).obj ((E hu').obj (J.obj Z₉)) = Tg)
    (hY : HEq Y ((E hl').obj W₀)) (hW : HEq W₀ ((F hl).obj Z₉))
    (s : S = (E hl).obj ((F hl).obj Z₉)) (t : Tg = (F hu).obj ((E hu).obj Z₉)) :
    eqToHom x₁ ≫ eqToHom x₂ ≫ (A hu).unit.app Y ≫
      (F hu).map (eqToHom x₃) ≫ eqToHom x₄ ≫ eqToHom x₅ ≫
      (F hu).map ((homContentCrossing T W i μ hl' hu').app (D.parity i) W₀) ≫ eqToHom x₆ ≫
      (F hu).map ((E hu').map (J.map
        (eqToHom x₇ ≫ (E hl).map (eqToHom x₈) ≫ (A hl).counit.app Y₂ ≫ eqToHom x₉))) ≫
      eqToHom x₁₀ =
    eqToHom s ≫
      (rouquierMate (homContentSuperAdjunction T W i μ hl)
        (homContentSuperAdjunction T W i μ hu)
        (homContentCrossing T W i μ hl hu)).app (D.parity i) Z₉ ≫ eqToHom t.symm := by
  subst em en
  obtain rfl : hl' = hl := rfl
  obtain rfl : hu' = hu := rfl
  obtain rfl := eq_of_heq hJ
  obtain rfl := eq_of_heq hY
  obtain rfl := eq_of_heq hW
  subst x₁ x₂ x₃ x₄ x₉ x₈ x₇ x₁₀
  simp only [Functor.id_obj, Functor.id_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [homContentSuperAdjunction_mate_app]
  rw [(F hu').map_id, (E hl').map_id]
  let Y := (E hl').obj ((F hl').obj Y₂)
  let V := (F hu').obj ((E hu').obj Y)
  let Z := (F hu').obj ((E hu').obj Y₂)
  let f : Y ⟶ V := (A hu').unit.app Y
  let g : End V := (F hu').map
    ((homContentCrossing T W i μ hl' hu').app (D.parity i) ((F hl').obj Y₂))
  let q : Y ⟶ Y₂ := (A hl').counit.app Y₂
  let h : V ⟶ Z := (F hu').map ((E hu').map q)
  let h' : V ⟶ Z := (F hu').map ((E hu').map ((𝟙 Y) ≫ q))
  change f ≫ (𝟙 V) ≫ g ≫ h' = f ≫ g ≫ h
  have hh : h' = h := by
    dsimp only [h', h]
    rw [Category.id_comp]
  rw [hh]
  simp only [Category.id_comp]

private theorem preF_obj_heq_of_weights {m m' n n' : X}
    (em : m = m') (en : n = n') (h : -n + D.α i = -m) (h' : -n' + D.α i = -m')
    (Z : homWeightSector T.obj W n μ) (Z' : homWeightSector T.obj W n' μ)
    (hZ : HEq Z Z') : HEq ((F h).obj Z) ((F h').obj Z') := by
  subst em en
  obtain rfl := eq_of_heq hZ
  rfl

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
private theorem preE_obj_heq_of_weights {m m' n n' : X}
    (em : m = m') (en : n = n') (h : -n + D.α i = -m) (h' : -n' + D.α i = -m')
    (Z : homWeightSector T.obj W m μ) (Z' : homWeightSector T.obj W m' μ)
    (hZ : HEq Z Z') : HEq ((E h).obj Z) ((E h').obj Z') := by
  subst em en
  obtain rfl := eq_of_heq hZ
  rfl

end Transport

namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}

private theorem pathFunctor_functor_heq_of_nil {a b : Sector I}
    (p : SPath ([] : List (Col I X)) a b) : HEq (P.pathFunctor p) (𝟭 (P.H b)) := by
  cases p
  rfl

attribute [local irreducible] Finsupp.zipWith Finsupp.single Finsupp.onFinset homContentShift contentWeight

attribute [local irreducible] homContentCrossing homContentPreAdjunction
  homContentSuperAdjunction RouquierFamily.leftAdjoints rouquierMate

private def probePrincipalCapPath (i : I) (ν : X) (t : Sector I) :
    SPath (wd D ν [up i, dn i]) t t :=
  SPath.two true true (by trivial) (by simp [StepValid, nextSector]) (nextSector_dn_up t)

private def probePrincipalCupPath (i : I) (ν : X) (t : Sector I)
    (hv : StepValid (false, i) true t) : SPath (wd D ν [dn i, up i]) t t :=
  SPath.two true true hv (by trivial) (nextSector_up_dn hv)

private def probePrincipalFirstPath (i : I) (ν : X) (t : Sector I)
    (hv : StepValid (false, i) true t) : SPath (sigL₁ (D := D) i i ν).cod.word t t :=
  let qg : SPath ((SKM.sig D).cod (sigL₁ (D := D) i i ν).gen) t t :=
    SPath.two true true hv (by trivial) (nextSector_up_dn hv)
  ((SPath.nil t).append qg).append (probePrincipalCapPath (D := D) i ν t)

private def probePrincipalSecondPath (i : I) (ν : X) (t : Sector I)
    (hv : StepValid (false, i) true t) : SPath (sigL₂ (D := D) i i ν).cod.word t t := by
  let tU := nextSector (false, i) true t
  let x := nextSector (true, i) true (nextSector (true, i) true tU)
  have hx : nextSector (false, i) true x = t := by
    have hle : Finsupp.single i 1 ≤ t.1 := (Finsupp.single_le_iff).mpr hv
    simp only [x, tU, nextSector, tsub_add_cancel_of_le hle, add_tsub_cancel_right]
  let pu : SPath (sigL₂ (D := D) i i ν).left t tU := .cons _ true t hv (.nil _)
  let pg : SPath ((SKM.sig D).cod (sigL₂ (D := D) i i ν).gen) tU x :=
    .cons _ true tU (by trivial) (.cons _ true _ (by trivial) (.nil _))
  let pv : SPath (sigL₂ (D := D) i i ν).right x t :=
    .cons _ true x (by simp [x, StepValid, nextSector]) ((SPath.nil _).castTgt hx)
  exact (pu.append pg).append pv

private theorem sigmaTerm_probe_mate (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (hv : StepValid (false, i) true t) (Z : P.H t) :
    sigmaTerm (P.upwardGens c) i i ν
      (probePrincipalCapPath i ν t) (probePrincipalCupPath i ν t hv)
      (probePrincipalFirstPath i ν t hv) (probePrincipalSecondPath i ν t hv) Z =
    (probeCapFactorIso i ν (by simp [StepValid, nextSector]) (nextSector_dn_up t) Z).hom ≫
      (rouquierMate
        (homContentSuperAdjunction P.T P.W.obj i (P.muM t) (P.muP_preE i t))
        (homContentSuperAdjunction P.T P.W.obj i (P.muM t) (P.muP_preF i hv))
        (homContentCrossing P.T P.W.obj i (P.muM t)
          (P.muP_preE i t) (P.muP_preF i hv))).app (D.parity i) Z ≫
      (probeCupFactorIso i ν hv (by trivial) (nextSector_up_dn hv) Z).inv := by
  let p : SPath (wd D ν [up i, dn i]) t t :=
    SPath.two true true (by trivial) (by simp [StepValid, nextSector]) (nextSector_dn_up t)
  let tU := nextSector (false, i) true t
  have hU : StepValid (true, i) true tU := by trivial
  let q : SPath (wd D ν [dn i, up i]) t t :=
    SPath.two true true hv hU (nextSector_up_dn hv)
  let qg₁ : SPath ((SKM.sig D).cod (sigL₁ (D := D) i i ν).gen) t t :=
    SPath.two true true hv hU (nextSector_up_dn hv)
  let m₁ : SPath (sigL₁ (D := D) i i ν).cod.word t t :=
    ((SPath.nil t).append qg₁).append p
  let x := nextSector (true, i) true (nextSector (true, i) true tU)
  have hL : StepValid (true, i) true (nextSector (true, i) true tU) := by
    trivial
  have hx : nextSector (false, i) true x = t := by
    have hle : Finsupp.single i 1 ≤ t.1 := (Finsupp.single_le_iff).mpr hv
    simp only [x, tU, nextSector, tsub_add_cancel_of_le hle, add_tsub_cancel_right]
  let pu₂ : SPath (sigL₂ (D := D) i i ν).left t tU := .cons _ true t hv (.nil _)
  let pg₂ : SPath ((SKM.sig D).dom (sigL₂ (D := D) i i ν).gen) tU x :=
    .cons _ true tU hU (.cons _ true _ hL (.nil _))
  let qg₂ : SPath ((SKM.sig D).cod (sigL₂ (D := D) i i ν).gen) tU x := pg₂
  let pv₂ : SPath (sigL₂ (D := D) i i ν).right x t :=
    .cons _ true x (by simp [x, StepValid, nextSector]) ((SPath.nil _).castTgt hx)
  let m₂ : SPath (sigL₂ (D := D) i i ν).cod.word t t := (pu₂.append qg₂).append pv₂
  change sigmaTerm (P.upwardGens c) i i ν p q m₁ m₂ Z = _
  let pg₃ : SPath ((SKM.sig D).dom (sigL₃ (D := D) i i ν).gen) t t :=
    SPath.two true true (by trivial) (by simp [StepValid, nextSector]) (nextSector_dn_up t)
  let pu₃ : SPath (sigL₃ (D := D) i i ν).left t t :=
    SPath.two true true hv hU (nextSector_up_dn hv)
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
    (SPath.eq_of_sides _ _ (by simp [q, pu₃, SPath.sides_cast, SPath.sides_append, SPath.sides_two, SPath.sides]))]
  simp only [upwardGens, Generators.image, sigL₁, sigL₂, sigL₃, SKM.lay,
    crossImage, dite_eq_left, cupImage, capImage]
  have hcross : ∀ Y, P.twoTwo _ _ _ _ (P.crossSameEntry c i _ _ _ _) pg₂ qg₂ rfl Y =
      (homContentCrossing P.T P.W.obj i (P.muM t)
        (P.muP_preE i (nextSector (true, i) true tU)) (P.muP_preE i tU)).app (D.parity i) Y := by
    intro Y
    rw [homContentCrossing_app, ite_eq_left rfl]
    rfl
  erw [hcross]
  simp only [qg₁, pg₃]
  rw [zeroTwo_two (Z' := (nextSector_up_dn hv).symm ▸ _)
    (hZ := eqRec_heq _ _)]
  rw [twoZero_two (Z' := (nextSector_dn_up t).symm ▸ _)
    (hZ := eqRec_heq _ _)]
  simp only [cupEntry, capEntry, preCup, preCap, preAdjAt]
  simp only [pu₂, pu₃, SPath.two, pathFunctor_cons, pathFunctor_nil, Functor.comp_map, Functor.id_map]
  let J : homWeightSector P.T.obj P.W.obj (P.muP t) (P.muM t) ⥤
      homWeightSector P.T.obj P.W.obj (P.muP (nextSector (true, i) true tU)) (P.muM t) :=
    P.pathFunctor ((SPath.nil _).castTgt (nextSector_up_dn hv))
  have em : P.muP (nextSector (true, i) true t) = P.muP x := by
    simp only [muP, x, tU, nextSector, tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hv)]
  have en : P.muP t = P.muP (nextSector (true, i) true tU) :=
    congrArg P.muP (nextSector_up_dn hv).symm
  conv_rhs =>
    simp only [probeCapFactorIso, probeCupFactorIso, twoPathEndpointIso,
      twoPathReturnIso, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      eqToIso.hom, eqToIso.inv, eqToHom_map, eqToHom_trans, Category.assoc]
  simp only [Category.assoc]
  dsimp only [step]
  have ehl := P.muP_preE i t
  have ehl' := P.muP_preE i (nextSector (true, i) true tU)
  have ehu := P.muP_preF i hv
  have ehu' := P.muP_preE i tU
  dsimp +instances only [H, muM, nextSector, tU, x] at J em en ehl ehl' ehu ehu' ⊢
  apply prePrincipal_of_eq P.T P.W.obj i (-P.ΛR + contentWeight D t.2)
    em en ehl ehl' ehu ehu' J
  ·
    exact pathFunctor_functor_heq_of_nil _
  ·
    have hp := pathFunctor_two_obj_heq (P := P)
      (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩)
      (nextSector_up_dn hv).symm true true
      (by trivial) (by simp [StepValid, nextSector]) (nextSector_dn_up t) hL pv₂
      (by
        change true :: _ = [true]
        rw [(SPath.sides_of_nil _).1]) Z
    exact (eqRec_heq _ _).trans ((eqRec_heq _ _).trans hp)
  ·
    have hh := preF_obj_heq_of_weights P.T P.W.obj i (P.muM t)
      em.symm (congrArg P.muP hx) (P.muP_preF i (by simp [x, StepValid, nextSector] : StepValid (false, i) true x)) (P.muP_preE i t)
      ((P.pathFunctor ((SPath.nil _).castTgt hx)).obj Z) Z
      (pathFunctor_obj_heq_of_nil _ Z)
    simpa only [pv₂, pathFunctor_cons, Functor.comp_obj, Functor.id_obj, step, x, tU, nextSector, muM] using hh
  ·
    have hh := preE_obj_heq_of_weights P.T P.W.obj i (P.muM t)
      en.symm rfl (P.muP_preE i tU) (P.muP_preF i hv)
      ((P.pathFunctor ((SPath.nil _).castTgt (nextSector_up_dn hv))).obj Z) Z
      (pathFunctor_obj_heq_of_nil _ Z)
    have he := congrArg
      ((homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hv)).obj)
      (eq_of_heq hh)
    simpa only [q, SPath.two, pathFunctor_cons, pathFunctor_nil, step, Functor.comp_obj, Functor.id_obj, SPath.castTgt, tU, nextSector, muM] using he

/-- The pure probe principal entry is the mate for the
specified normalized precomposition adjunctions, in the computed path
charts. There is no condition on the unused mixed coefficient. -/
theorem sigmaEntry_probe_mate (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (hv : StepValid (false, i) true t) (Z : P.H t) :
    P.sigmaEntry c i i ν
      (SPath.two true true (by trivial) (by simp [StepValid, nextSector]) (nextSector_dn_up t))
      (SPath.two true true hv (by trivial) (nextSector_up_dn hv)) Z =
    (probeCapFactorIso i ν (by simp [StepValid, nextSector]) (nextSector_dn_up t) Z).hom ≫
      (rouquierMate
        (homContentSuperAdjunction P.T P.W.obj i (P.muM t) (P.muP_preE i t))
        (homContentSuperAdjunction P.T P.W.obj i (P.muM t) (P.muP_preF i hv))
        (homContentCrossing P.T P.W.obj i (P.muM t)
          (P.muP_preE i t) (P.muP_preF i hv))).app (D.parity i) Z ≫
      (probeCupFactorIso i ν hv (by trivial) (nextSector_up_dn hv) Z).inv := by
  let p := probePrincipalCapPath (D := D) i ν t
  let q := probePrincipalCupPath (D := D) i ν t hv
  let m₁ := probePrincipalFirstPath (D := D) i ν t hv
  let m₂ := probePrincipalSecondPath (D := D) i ν t hv
  change P.sigmaEntry c i i ν p q Z = _
  rw [sigmaEntry_eq_sigmaTerm (p := p) (q := q) (m₁ := m₁) (m₂ := m₂) (p₁ := true) (p₂ := true)
    (q₁ := true) (q₂ := true) (hp := SPath.sides_two _ _ _ _ _)
    (hq := SPath.sides_two _ _ _ _ _)
    (hm₁ := by simp [m₁, probePrincipalFirstPath,
      probePrincipalCapPath, SPath.sides_append, SPath.sides_two, SPath.sides])
    (hm₂ := by simp [m₂, probePrincipalSecondPath, SPath.sides_append, SPath.sides,
      SPath.sides_castTgt])]
  exact sigmaTerm_probe_mate c i ν t hv Z

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
