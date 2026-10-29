/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.Entry
import OddMath.SKM.RouquierHomDistinctMixedPostDotsIso

/-! # The sideways crossing on a probe/reservoir path -/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}


omit [AddCommGroup X] in
/-- A chain whose transports are endo-transports is invertible when the chain without
them is. -/
theorem isIso_eqToHom_chain {C : Type*} [Category C] {s a b c c' d t : C} (q1 : s = a)
    (u : a ⟶ b) (q2 : b = b) (g1 : b ⟶ c) (g2 : c ⟶ c') (q3 : c' = c') (h : c' ⟶ d)
    (q4 : d = t) (hiso : IsIso (u ≫ g1 ≫ g2 ≫ h)) :
    IsIso (eqToHom q1 ≫ u ≫ eqToHom q2 ≫ g1 ≫ g2 ≫ eqToHom q3 ≫ h ≫ eqToHom q4) := by
  subst q1 q4
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hiso

/-- The unit, the mixed crossing and the counit of a probe/reservoir path, joined by
transports, form the dotted mixed mate. Every transport is an `eqToHom` between possibly
different weights; once the reservoir weights `m₁ = m₀`, `n' = n` are identified the chain
collapses to `homDistinctMixedMateDot`. -/
theorem isIso_postCup_mixedCross_postCap (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
    (i : I) (β₀ β₁ : I →₀ ℕ) {μ₀ μ₁ : X} (E : T (-μ₀) ⟶ T (-μ₁))
    {m₀ m₁ n : X} (hm : m₁ = m₀) (h₀ : m₀ + D.α i = n) (h₁ : m₁ + D.α i = n)
    (C : T (-μ₁) ⟶ W.obj n)
    (Qf : ∀ Y : T (-μ₁) ⟶ W.obj m₁, End (E ≫ (homContentPostE T W i β₁ μ₁ h₁).obj Y))
    (hiso : IsIso (homDistinctMixedMateDot E (W.adj i h₁) (homContentShift D i β₁)
      (homContentShift D i β₀) C (Qf ((homContentPostF T W i β₁ μ₁ h₁).obj C))))
    (A : T (-μ₀) ⟶ W.obj m₀) (hA : A = E ≫ (homContentPostF T W i β₁ μ₁ h₀).obj C)
    (B' : T (-μ₁) ⟶ W.obj m₁) (hB : B' = (homContentPostF T W i β₁ μ₁ h₁).obj C)
    {S O1 O5 O6 O7 O13 O14 O15 O16 O22 O23 Tg : T (-μ₀) ⟶ W.obj m₀}
    {O4 O8 O12 : T (-μ₀) ⟶ W.obj n} {O17 O21 : T (-μ₁) ⟶ W.obj n}
    {O18 : T (-μ₁) ⟶ W.obj m₁}
    (p1 : S = O1) (f2 : O1 ⟶ A) (hf2 : ∃ p : O1 = A, f2 = eqToHom p)
    (p4 : (homContentPostE T W i β₀ μ₀ h₀).obj A = O4)
    (f5 : (homContentPostF T W i β₀ μ₀ h₀).obj O4 ⟶ O5)
    (hf5 : ∃ p : (homContentPostF T W i β₀ μ₀ h₀).obj O4 = O5, f5 = eqToHom p) (p6 : O5 = O6) (p7 : O6 = O7)
    (p8 : O7 = (homContentPostF T W i β₀ μ₀ h₀).obj O8)
    (p9 : O8 = (homParityShift (k := k) (homContentShift D i β₀)).obj ((E ≫ B') ≫ W.E i h₁))
    (p12 : E ≫ (homContentPostE T W i β₁ μ₁ h₁).obj B' = O12)
    (p13 : (homContentPostF T W i β₀ μ₀ h₀).obj O12 = O13) (p14 : O13 = O14) (p15 : O14 = O15)
    (p16 : O15 = O16) (p17 : O16 = (homContentPostF T W i β₀ μ₀ h₀).obj (E ≫ O17))
    (f18 : O17 ⟶ (homContentPostE T W i β₁ μ₁ h₁).obj O18)
    (hf18 : ∃ p : O17 = (homContentPostE T W i β₁ μ₁ h₁).obj O18, f18 = eqToHom p)
    (p19 : O18 = (homContentPostF T W i β₁ μ₁ h₁).obj C) (f21 : C ⟶ O21) (hf21 : ∃ p : C = O21, f21 = eqToHom p)
    (p22 : (homContentPostF T W i β₀ μ₀ h₀).obj (E ≫ O21) = O22) (p23 : O22 = O23)
    (p24 : O23 = Tg) :
    IsIso (eqToHom p1 ≫ f2 ≫
      (homContentPostAdjunction T W i β₀ μ₀ h₀).unit.app A ≫
      (homContentPostF T W i β₀ μ₀ h₀).map (eqToHom p4) ≫
      f5 ≫ eqToHom p6 ≫ eqToHom p7 ≫ eqToHom p8 ≫
      (homContentPostF T W i β₀ μ₀ h₀).map (eqToHom p9) ≫
      (homContentPostF T W i β₀ μ₀ h₀).map
        (homMixedInterchange (k := k) E (W.E i h₁) (homContentShift D i β₁)
          (homContentShift D i β₀) B').inv ≫
      (homContentPostF T W i β₀ μ₀ h₀).map (Qf B') ≫
      (homContentPostF T W i β₀ μ₀ h₀).map (eqToHom p12) ≫
      eqToHom p13 ≫ eqToHom p14 ≫ eqToHom p15 ≫ eqToHom p16 ≫ eqToHom p17 ≫
      (homContentPostF T W i β₀ μ₀ h₀).map (E ◁ f18) ≫
      (homContentPostF T W i β₀ μ₀ h₀).map
        (E ◁ (homContentPostE T W i β₁ μ₁ h₁).map (eqToHom p19)) ≫
      (homContentPostF T W i β₀ μ₀ h₀).map
        (E ◁ (homContentPostAdjunction T W i β₁ μ₁ h₁).counit.app C) ≫
      (homContentPostF T W i β₀ μ₀ h₀).map (E ◁ f21) ≫
      eqToHom p22 ≫ eqToHom p23 ≫ eqToHom p24) := by
  have hwl : ∀ {f g : T (-μ₁) ⟶ W.obj n} (p : f = g),
      E ◁ eqToHom p = eqToHom (congrArg (E ≫ ·) p) := by
    intro f g p
    subst p
    simp only [eqToHom_refl, TwoSupercategory.whiskerLeft_id (R := k)]
  obtain ⟨p2, rfl⟩ := hf2
  obtain ⟨p5, rfl⟩ := hf5
  obtain ⟨p18, rfl⟩ := hf18
  obtain ⟨p21, rfl⟩ := hf21
  simp only [eqToHom_map, hwl, eqToHom_trans, eqToHom_trans_assoc]
  subst hm hB hA
  obtain rfl : h₀ = h₁ := rfl
  have hR : homDistinctMixedMateDot E (W.adj i h₀) (homContentShift D i β₁)
      (homContentShift D i β₀) C (Qf ((homContentPostF T W i β₁ μ₁ h₀).obj C)) =
      (homContentPostAdjunction T W i β₀ μ₀ h₀).unit.app _ ≫
        (homContentPostF T W i β₀ μ₀ h₀).map
          ((homMixedInterchange (k := k) E (W.E i h₀) (homContentShift D i β₁)
            (homContentShift D i β₀) _).inv ≫ Qf _ ≫
            E ◁ (homContentPostAdjunction T W i β₁ μ₁ h₀).counit.app C) := rfl
  rw [hR, Functor.map_comp, Functor.map_comp] at hiso
  exact isIso_eqToHom_chain _ _ _ _ _ _ _ _ hiso

omit [AddCommGroup X] in
/-- Replace the three layers of a sideways composite by equal morphisms. -/
theorem isIso_comp_layers {C : Type*} [Category C] {a b c d e f : C} {L₁ A₁ : a ⟶ b}
    {L₂ A₂ : b ⟶ c} (q : c = d) {L₃ A₃ : d ⟶ e} (q' : e = f) (h₁ : L₁ = A₁) (h₂ : L₂ = A₂)
    (h₃ : L₃ = A₃) (h : IsIso (A₁ ≫ A₂ ≫ eqToHom q ≫ A₃ ≫ eqToHom q')) :
    IsIso (L₁ ≫ L₂ ≫ eqToHom q ≫ L₃ ≫ eqToHom q') := by
  subst h₁ h₂ h₃
  exact h

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The functor of an upward strand on the left whiskers by its generator. -/
theorem homContentPreE_map (T : RouquierFamily (k := k) (B := B) D) (W : X → B) (i : I)
    (muM : X) {muP nuP : X} (h : -nuP + D.α i = -muP)
    {f g : homWeightSector T.obj W muP muM} (η : f ⟶ g) :
    (homContentPreE T W i muM h).map η = T.E i h ◁ η := rfl

open Lean Elab Tactic Meta in
/-- Close a goal `∃ p, f = eqToHom p`, where `f` is `eqToHom h` or its image under functors
that act as the identity on it, with the witness `h`. Unification alone leaves
the witness unassigned, since proofs of the same proposition are definitionally equal. -/
elab "eqToHom_witness" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← whnfR (← g.getType))
  let some (_, body) := t.app2? ``Exists | throwError "eqToHom_witness: not an existential"
  let .lam _ _ e _ := body | throwError "eqToHom_witness: unexpected predicate"
  let some (_, lhs, _) := e.eq? | throwError "eqToHom_witness: not an equation"
  let lhs ← instantiateMVars lhs
  -- A transport may sit under functors acting as the identity on it.
  let mut inner := lhs
  while inner.isAppOf ``Prefunctor.map || inner.isAppOf ``CategoryTheory.Functor.map do
    inner := inner.appArg!
  unless inner.isAppOf ``CategoryTheory.eqToHom do
    throwError "eqToHom_witness: not a transport: {lhs}"
  let w := inner.appArg!
  let prf ← mkEqRefl lhs
  g.assign (← mkAppOptM ``Exists.intro #[none, some body, some w, some prf])
  replaceMainGoal []

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- The functor of an empty path acts as the identity on morphisms. -/
theorem pathFunctor_nil_map (s : Sector I) {Y Y' : P.H s} (f : Y ⟶ Y') :
    (P.pathFunctor (SPath.nil (X := X) s)).map f = f := rfl

/-- An entry of a layer at paths equal to given ones. -/
theorem compLayer_congr (gens : P.Generators) (L : Layer (SKM.sig D)) {s t : Sector I}
    {p p' : SPath L.dom.word s t} {q q' : SPath L.cod.word s t} (hp : p = p') (hq : q = q')
    (Z : P.H t) :
    compLayer gens L p q Z =
      eqToHom (by rw [hp]) ≫ compLayer gens L p' q' Z ≫ eqToHom (by rw [hq]) := by
  subst hp hq; simp

/-- The entry of a matrix between two two-letter words at the paths through given
summands. -/
theorem twoTwo_two (c₁ c₂ d₁ d₂ : Col I X) (f : P.TwoEntry c₁ c₂ d₁ d₂)
    {t s s' : Sector I} (σ₁ σ₂ τ₁ τ₂ : Bool) (hv₁ : StepValid c₁.l σ₁ t)
    (hv₂ : StepValid c₂.l σ₂ (nextSector c₁.l σ₁ t)) (hw₁ : StepValid d₁.l τ₁ t)
    (hw₂ : StepValid d₂.l τ₂ (nextSector d₁.l τ₁ t))
    (e : nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t) = s)
    (e' : nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t) = s') (hs : s = s') (Z : P.H s')
    (Z' : P.H (nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))) (hZ : HEq Z' Z) :
    P.twoTwo c₁ c₂ d₁ d₂ f (SPath.two σ₁ σ₂ hv₁ hv₂ e) (SPath.two τ₁ τ₂ hw₁ hw₂ e') hs Z =
      eqToHom (by subst e'; subst e; obtain rfl := eq_of_heq hZ; rfl) ≫
        f t σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ (e.trans (hs.trans e'.symm)) Z' ≫
        eqToHom (by subst e'; subst e; obtain rfl := eq_of_heq hZ; rfl) := by
  subst e'; subst e; obtain rfl := eq_of_heq hZ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

attribute [local irreducible] Finsupp.zipWith Finsupp.single Finsupp.onFinset in
example (c : P.CrossCoeff) {i j : I} (hij : i ≠ j) (ν : X) (t : Sector I)
    (q : SPath (wd D ν [dn i, up j]) t
      (nextSector (dn i) false (nextSector (up j) true t)))
    (Z : P.H (nextSector (dn i) false (nextSector (up j) true t))) :
    IsIso (P.sigmaEntry c i j ν
      (SPath.cons _ true t trivial (SPath.cons _ false _ trivial (SPath.nil _))) q Z) := by
  have hR : StepValid (up i) false (nextSector (dn i) false t) := by
    simp [StepValid, nextSector]
  have e₀ : nextSector (up i) false (nextSector (dn i) false t) = t := by
    simp only [nextSector]; ext <;> simp
  let cupPath : SPath (wd D (SKM.wt D ν [up j, dn i]) (SKM.Shape.cup i).cod) t t :=
    SPath.two false false trivial hR e₀
  let p : SPath (wd D ν [up j, dn i]) t (nextSector (dn i) false (nextSector (up j) true t)) :=
    SPath.cons _ true t trivial (SPath.cons _ false _ trivial (SPath.nil _))
  let m₁ : SPath (wd D ν [dn i, up i, up j, dn i]) t
      (nextSector (dn i) false (nextSector (up j) true t)) :=
    ((SPath.nil t).append cupPath).append p
  have hR' : StepValid (up i) false (nextSector (up j) true (nextSector (dn i) false t)) := by
    simp [StepValid, nextSector]
  have e₁ : nextSector (up j) true (nextSector (up i) false (nextSector (dn i) false t)) =
      nextSector (up j) true t := by rw [e₀]
  have e₂ : nextSector (up i) false (nextSector (up j) true (nextSector (dn i) false t)) =
      nextSector (up j) true t := by
    simp only [nextSector]; ext <;> simp
  let pu₂ : SPath (wd D (SKM.wt D ν ((SKM.Shape.cross i j).dom ++ [dn i])) [dn i]) t
      (nextSector (dn i) false t) := SPath.cons _ false t trivial (SPath.nil _)
  let pv₂ : SPath (wd D ν [dn i]) (nextSector (up j) true t)
      (nextSector (dn i) false (nextSector (up j) true t)) :=
    SPath.cons _ false _ trivial (SPath.nil _)
  let crossDom : SPath (wd D (SKM.wt D ν [dn i]) (SKM.Shape.cross i j).dom)
      (nextSector (dn i) false t) (nextSector (up j) true t) := SPath.two false true hR trivial e₁
  let crossCod : SPath (wd D (SKM.wt D ν [dn i]) (SKM.Shape.cross i j).cod)
      (nextSector (dn i) false t) (nextSector (up j) true t) := SPath.two true false trivial hR' e₂
  let m₂ : SPath (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]).cod.word t
      (nextSector (dn i) false (nextSector (up j) true t)) := (pu₂.append crossCod).append pv₂
  have hm₁ : m₁ = (pu₂.append crossDom).append pv₂ := SPath.eq_of_sides _ _ (by
    simp only [m₁, cupPath, p, pu₂, pv₂, crossDom, SPath.sides_append, SPath.sides_two]; rfl)
  rw [P.sigmaEntry_eq c hij ν _ q m₁ m₂ Z (a := true) (b := false) rfl (by
      simp only [m₁, cupPath, p, SPath.sides_append, SPath.sides_two]; rfl)
    (by simp only [m₂, pu₂, pv₂, crossCod, SPath.sides_append, SPath.sides_two]; rfl)]
  have h₁ : compLayer (P.upwardGens c) (SKM.lay D ν [] (Shape.cup i) [up j, dn i]) p m₁ Z = _ :=
    P.compLayer_eq (P.upwardGens c) (SKM.lay D ν [] (Shape.cup i) [up j, dn i])
      (SPath.nil t) (SPath.nil t) cupPath p Z
  have h₂ : compLayer (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i])
      ((pu₂.append crossDom).append pv₂) m₂ Z = _ :=
    P.compLayer_eq (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i])
      pu₂ crossDom crossCod pv₂ Z
  let t' := nextSector (dn i) false t
  let u := nextSector (dn i) false (nextSector (up j) true t)
  have hR'' : StepValid (up i) false u := by simp [u, StepValid, nextSector]
  have ecap : nextSector (dn i) false (nextSector (up i) false u) = u := by
    simp only [u, nextSector]; ext <;> simp
  let pu₃ : SPath (wd D (SKM.wt D ν ((SKM.Shape.cap i).dom ++ [])) [dn i, up j]) t u :=
    SPath.cons _ false t trivial (SPath.cons _ true t' trivial (SPath.nil _))
  let capPath : SPath (wd D (SKM.wt D ν []) (SKM.Shape.cap i).dom) u u :=
    SPath.two false false hR'' trivial ecap
  have hm₂ : m₂.cast (sigma_cross_cap_word i j ν) = (pu₃.append capPath).append (SPath.nil _) :=
    SPath.eq_of_sides _ _ (by
      simp only [SPath.sides_cast, m₂, pu₂, pv₂, crossCod, pu₃, capPath, SPath.sides_append,
        SPath.sides_two]; rfl)
  have hq : q.cast (sigma_cap_word i j ν) = (pu₃.append (SPath.nil _)).append (SPath.nil _) :=
    SPath.eq_of_sides _ _ (by
      have : Subsingleton (SPath (wd D ν [dn i, up j]) t u) := SPath.subsingleton_dnUp hij _ _ t u
      rw [Subsingleton.elim q (SPath.cons _ false t (by trivial) (SPath.cons _ true t'
        (by trivial) (SPath.nil _)))]
      simp only [SPath.sides_cast, pu₃, SPath.sides_append]; rfl)
  have h₃ := P.compLayer_eq (P.upwardGens c) (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) [])
      pu₃ capPath (SPath.nil _) (SPath.nil _) Z
  conv at h₁ =>
    rhs
    dsimp only [SKM.lay]
    simp only [Generators.image, upwardGens, cupImage]
    rw [P.zeroTwo_two (hZ := eqRec_heq e₀.symm _)]
    simp only [cupEntry]
    unfold postCup
    simp only [pathFunctor_cons, pathFunctor_nil_map, Functor.comp_map, Functor.id_map, dn, up, step,
      homContentPreE_map, Functor.map_comp, Category.assoc]
  conv at h₂ =>
    rhs
    dsimp only [SKM.lay]
    simp only [Generators.image, upwardGens, crossImage, dite_eq_right hij]
    rw [P.twoTwo_two (hZ := eqRec_heq e₂.symm _)]
    simp only [crossNeEntry]
    unfold mixedJ
    simp only [pu₂, pathFunctor_cons, pathFunctor_nil_map, Functor.comp_map, Functor.id_map, dn, up,
      step, homContentPreE_map, Functor.map_comp, Category.assoc]
  conv at h₃ =>
    rhs
    dsimp only [SKM.lay]
    simp only [Generators.image, upwardGens, capImage]
    rw [P.twoZero_two (hZ := eqRec_heq ecap.symm _)]
    simp only [capEntry]
    unfold postCap
    simp only [pu₃, pathFunctor_cons, pathFunctor_nil_map, Functor.comp_map, Functor.id_map, dn, up,
      step, homContentPreE_map, Functor.map_comp, Category.assoc]
  have h₂' := P.compLayer_congr (P.upwardGens c)
    (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]) hm₁ (rfl : m₂ = m₂) Z
  rw [h₂] at h₂'
  have h₃' := P.compLayer_congr (P.upwardGens c) (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) [])
    hm₂ hq Z
  rw [h₃] at h₃'
  refine isIso_comp_layers _ _ h₁ h₂' h₃' ?_
  simp only [Category.assoc]
  refine isIso_postCup_mixedCross_postCap P.T.obj P.W i _ _ _ ?hm _ _ _
    (fun Y => P.mixedQ j i t' hR' Y) ?hiso _ ?hA _ ?hB
    _ _ ?hf2 _ _ ?hf5 _ _ _ _ _ _ _ _ _ _ _ ?hf18 _ _ ?hf21 _ _ _
  case hf2 | hf5 | hf18 | hf21 => eqToHom_witness
  all_goals set_option pp.proofs false in trace_state
  all_goals sorry

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
