import OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingMate
import OddMath.QuiverHecke.SwappedAssembly.ReservoirDottedFactorCoordinates

/-! # The actual pure reservoir principal block -/
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
variable (T : X → B) (W : RouquierFamily (k := k) (B := B) D) (i : I)
  (β : I →₀ ℕ) (μ : X)
local notation "H" a:max => homWeightSector T W.obj μ a
local notation "E" h:max => homContentPostE T W i β μ h
local notation "F" h:max => homContentPostF T W i β μ h
local notation "A" h:max => homContentPostAdjunction T W i β μ h

private theorem postPrincipal_of_eq {m m' n n' p : X} (em : m = m') (en : n = n')
    (hl : m + D.α i = n) (hl' : m' + D.α i = n')
    (hu : n + D.α i = p) (hu' : n' + D.α i = p)
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
      (F hu).map (homContentPostCrossingApp T W i β μ hl' hu' W₀) ≫ eqToHom x₆ ≫
      (F hu).map ((E hu').map (J.map
        (eqToHom x₇ ≫ (E hl).map (eqToHom x₈) ≫ (A hl).counit.app Y₂ ≫ eqToHom x₉))) ≫
      eqToHom x₁₀ =
    eqToHom s ≫
      (rouquierMate (homContentPostSuperAdjunction T W i β μ hl)
        (homContentPostSuperAdjunction T W i β μ hu)
        (homContentPostCrossing T W i β μ hl hu)).app (D.parity i) Z₉ ≫ eqToHom t.symm := by
  subst em en
  obtain rfl : hl' = hl := rfl
  obtain rfl : hu' = hu := rfl
  obtain rfl := eq_of_heq hJ
  obtain rfl := eq_of_heq hY
  obtain rfl := eq_of_heq hW
  subst x₁ x₂ x₃ x₄ x₉ x₈ x₇ x₁₀
  simp only [Functor.id_obj, Functor.id_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [rouquierMate_scat_app]
  simp only [homContentPostSuperAdjunction, superAdjunctionOfEven, SuperNatTrans.ofNatTrans,
    homContentPostSuperE, homContentPostSuperF, Superfunctor.obj, Superfunctor.map,
    homContentPostCrossing_app, ↓reduceIte, homContentPostCrossingApp]
  rw [(F hu').map_id, (E hl').map_id]
  let Y := (E hl').obj ((F hl').obj Y₂)
  let V := (F hu').obj ((E hu').obj Y)
  let Z := (F hu').obj ((E hu').obj Y₂)
  let f : Y ⟶ V := (A hu').unit.app Y
  let g : End V := (F hu').map
    ((homContentPostWordIso T W i β μ hl' hu').hom.app ((F hl').obj Y₂) ≫
      (F hl').obj Y₂ ◁ W.cross i i hl' hu' hl' hu' ≫
      (homContentPostWordIso T W i β μ hl' hu').inv.app ((F hl').obj Y₂))
  let q : Y ⟶ Y₂ := (A hl').counit.app Y₂
  let h : V ⟶ Z := (F hu').map ((E hu').map q)
  let h' : V ⟶ Z := (F hu').map ((E hu').map ((𝟙 Y) ≫ q))
  change f ≫ (𝟙 V) ≫ g ≫ h' = f ≫ g ≫ h
  have hh : h' = h := by
    dsimp only [h', h]
    rw [Category.id_comp]
  rw [hh]
  simp only [Category.id_comp]

private theorem postF_obj_heq_of_weights {m m' n n' : X}
    (em : m = m') (en : n = n') (h : m + D.α i = n) (h' : m' + D.α i = n')
    (Z : homWeightSector T W.obj μ n) (Z' : homWeightSector T W.obj μ n')
    (hZ : HEq Z Z') : HEq ((F h).obj Z) ((F h').obj Z') := by
  subst em en
  obtain rfl := eq_of_heq hZ
  rfl

private theorem postE_obj_heq_of_weights {m m' n n' : X}
    (em : m = m') (en : n = n') (h : m + D.α i = n) (h' : m' + D.α i = n')
    (Z : homWeightSector T W.obj μ m) (Z' : homWeightSector T W.obj μ m')
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

/-- The actual pure reservoir principal entry is the mate for the
specified shifted postcomposition adjunctions, in the computed path
charts. There is no condition on the unused mixed coefficient. -/
theorem sigmaEntry_reservoir_mate (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (hv : StepValid (true, i) false t) (Z : P.H t) :
    P.sigmaEntry c i i ν
      (SPath.two false false hv (by trivial) (SPath.next_upDn_false_false hv))
      (SPath.two false false (by trivial) (by simp [StepValid, nextSector])
        (SPath.next_dnUp_false_false t)) Z =
    (reservoirCapFactorIso i ν hv (by trivial) (SPath.next_upDn_false_false hv) Z).hom ≫
      (rouquierMate
        (homContentPostSuperAdjunction P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv))
        (homContentPostSuperAdjunction P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t))
        (homContentPostCrossing P.T.obj P.W i t.1 (P.muP t)
          (P.muM_postE i hv) (P.muM_postF i t))).app (D.parity i) Z ≫
      (reservoirCupFactorIso i ν (by trivial) (by simp [StepValid, nextSector])
        (SPath.next_dnUp_false_false t) Z).inv := by
  let p : SPath (wd D ν [up i, dn i]) t t :=
    SPath.two false false hv (by trivial) (SPath.next_upDn_false_false hv)
  let tU := nextSector (false, i) false t
  have hU : StepValid (true, i) false tU := by simp [tU, StepValid, nextSector]
  let q : SPath (wd D ν [dn i, up i]) t t :=
    SPath.two false false (by trivial) hU (SPath.next_dnUp_false_false t)
  let qg₁ : SPath ((SKM.sig D).cod (sigL₁ (D := D) i i ν).gen) t t :=
    SPath.two false false (by trivial) hU (SPath.next_dnUp_false_false t)
  let m₁ : SPath (sigL₁ (D := D) i i ν).cod.word t t :=
    ((SPath.nil t).append qg₁).append p
  let x := nextSector (true, i) false (nextSector (true, i) false tU)
  have hL : StepValid (true, i) false (nextSector (true, i) false tU) := by
    simpa only [tU, nextSector, add_tsub_cancel_right] using hv
  have hx : nextSector (false, i) false x = t := by
    have hle : Finsupp.single i 1 ≤ t.2 := (Finsupp.single_le_iff).mpr hv
    simp only [x, tU, nextSector, add_tsub_cancel_right, tsub_add_cancel_of_le hle]
  let pu₂ : SPath (sigL₂ (D := D) i i ν).left t tU := .cons _ false t trivial (.nil _)
  let pg₂ : SPath ((SKM.sig D).dom (sigL₂ (D := D) i i ν).gen) tU x :=
    .cons _ false tU hU (.cons _ false _ hL (.nil _))
  let qg₂ : SPath ((SKM.sig D).cod (sigL₂ (D := D) i i ν).gen) tU x := pg₂
  let pv₂ : SPath (sigL₂ (D := D) i i ν).right x t :=
    .cons _ false x trivial ((SPath.nil _).castTgt hx)
  let m₂ : SPath (sigL₂ (D := D) i i ν).cod.word t t := (pu₂.append qg₂).append pv₂
  rw [sigmaEntry_eq_sigmaTerm (m₁ := m₁) (m₂ := m₂) (p₁ := false) (p₂ := false)
    (q₁ := false) (q₂ := false) (hp := SPath.sides_two _ _ _ _ _)
    (hq := SPath.sides_two _ _ _ _ _)
    (hm₁ := by simp [m₁, p, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides])
    (hm₂ := by simp [m₂, pu₂, qg₂, pg₂, pv₂, SPath.sides_append, SPath.sides])]
  let pg₃ : SPath ((SKM.sig D).dom (sigL₃ (D := D) i i ν).gen) t t :=
    SPath.two false false hv (by trivial) (SPath.next_upDn_false_false hv)
  let pu₃ : SPath (sigL₃ (D := D) i i ν).left t t :=
    SPath.two false false (by trivial) hU (SPath.next_dnUp_false_false t)
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
      P.postCrossSame i tU hU hL Y := fun _ => rfl
  erw [hcross]
  simp only [qg₁, pg₃]
  rw [zeroTwo_two (Z' := (SPath.next_dnUp_false_false t).symm ▸ _)
    (hZ := eqRec_heq _ _)]
  rw [twoZero_two (Z' := (SPath.next_upDn_false_false hv).symm ▸ _)
    (hZ := eqRec_heq _ _)]
  simp only [cupEntry, capEntry, postCup, postCap, postCrossSame]
  simp only [pu₂, pu₃, SPath.two, pathFunctor_cons, pathFunctor_nil, Functor.comp_map, Functor.id_map]
  let J : P.H t ⥤ P.H (nextSector (true, i) false tU) :=
    P.pathFunctor ((SPath.nil _).castTgt (SPath.next_dnUp_false_false t))
  have em : P.muM (nextSector (true, i) false t) = P.muM x := by
    simp only [muM, x, tU, nextSector, add_tsub_cancel_right]
  have en : P.muM t = P.muM (nextSector (true, i) false tU) :=
    congrArg P.muM (SPath.next_dnUp_false_false t).symm
  conv_rhs =>
    simp only [reservoirCapFactorIso, reservoirCupFactorIso, twoPathEndpointIso,
      twoPathReturnIso, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      eqToIso.hom, eqToIso.inv, eqToHom_map, eqToHom_trans, Category.assoc]
  simp only [Category.assoc]
  dsimp only [step]
  apply postPrincipal_of_eq P.T.obj P.W i t.1 (P.muP t) em en
    (P.muM_postE i hv) (P.muM_postE i hL) (P.muM_postF i t) (P.muM_postE i hU)
    J
  · exact pathFunctor_functor_heq_of_nil _
  · refine (eqRec_heq _ _).trans ((eqRec_heq _ _).trans ?_)
    exact pathFunctor_two_obj_heq (P := P)
      (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩)
      (SPath.next_dnUp_false_false t).symm false false
      hv (by trivial) (SPath.next_upDn_false_false hv) hL pv₂
      (by
        change false :: _ = [false]
        rw [(SPath.sides_of_nil _).1]) Z
  · have hh := postF_obj_heq_of_weights P.T.obj P.W i t.1 (P.muP t)
      em.symm (congrArg P.muM hx) (P.muM_postF i x) (P.muM_postE i hv)
      ((P.pathFunctor ((SPath.nil _).castTgt hx)).obj Z) Z
      (pathFunctor_obj_heq_of_nil _ Z)
    simpa only [pv₂, pathFunctor_cons, Functor.comp_obj, Functor.id_obj, step, x, tU, nextSector, muP] using hh
  · have hh := postE_obj_heq_of_weights P.T.obj P.W i t.1 (P.muP t)
      en.symm rfl (P.muM_postE i hU) (P.muM_postF i t)
      ((P.pathFunctor ((SPath.nil _).castTgt (SPath.next_dnUp_false_false t))).obj Z) Z
      (pathFunctor_obj_heq_of_nil _ Z)
    have he := congrArg
      ((homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).obj)
      (eq_of_heq hh)
    simpa only [Functor.comp_obj, Functor.id_obj, SPath.castTgt, tU, nextSector, muP] using he

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
