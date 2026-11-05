/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.Entry
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Cross
import OddMath.SKM.RouquierHomDistinctMixedPostDotsIso

/-! # The sideways crossing on a probe/reservoir path

For `i ≠ j`, the entry of the sideways crossing `σ : Eⱼ Fᵢ → Fᵢ Eⱼ` of Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, (1.11), in the swapped Hom construction,
from the summand path of `Eⱼ Fᵢ` with `Eⱼ` on the probe and `Fᵢ` on the reservoir. By
`sigmaEntry_eq` it is a cup, a distinct-colour mixed crossing `J⁻¹ ≫ Q_ji` and a cap; after
removing the path transports this is the dotted mixed mate of
`docs/Nondegeneracy/SwappedDistinctMixedMates.md` (13)–(15), which is invertible when the
probe dot is a unit and the reservoir dot is nilpotent.

## Main results

* `isIso_postCup_mixedCross_postCap`: the unit, mixed crossing and counit joined by
  transports form the dotted mixed mate.
* `isIso_homDistinctMixedMateDot_param`: the dotted mixed mate of the parameter polynomial is
  invertible for dots of any parity; odd dots enter only through even powers.
* `ProbeReservoir.isIso_sigmaEntry_probe_reservoir`: the `(P,R)` entry of `σ` is invertible.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory

universe u uB vB wB

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{wB, vB} B]
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
    (hf5 : ∃ p : (homContentPostF T W i β₀ μ₀ h₀).obj O4 = O5, f5 = eqToHom p) (p6 : O5 = O6)
    (p7 : O6 = O7)
    (p8 : O7 = (homContentPostF T W i β₀ μ₀ h₀).obj O8)
    (p9 : O8 = (homParityShift (k := k) (homContentShift D i β₀)).obj ((E ≫ B') ≫ W.E i h₁))
    (p12 : E ≫ (homContentPostE T W i β₁ μ₁ h₁).obj B' = O12)
    (p13 : (homContentPostF T W i β₀ μ₀ h₀).obj O12 = O13) (p14 : O13 = O14) (p15 : O14 = O15)
    (p16 : O15 = O16) (p17 : O16 = (homContentPostF T W i β₀ μ₀ h₀).obj (E ≫ O17))
    (f18 : O17 ⟶ (homContentPostE T W i β₁ μ₁ h₁).obj O18)
    (hf18 : ∃ p : O17 = (homContentPostE T W i β₁ μ₁ h₁).obj O18, f18 = eqToHom p)
    (p19 : O18 = (homContentPostF T W i β₁ μ₁ h₁).obj C) (f21 : C ⟶ O21)
    (hf21 : ∃ p : C = O21, f21 = eqToHom p)
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

/-- The right adjoint `homContentPostF` applied to heterogeneously equal objects, along equal
weights, gives heterogeneously equal objects. -/
theorem homContentPostF_obj_heq (T : X → B) (W : RouquierFamily (k := k) (B := B) D) (i : I)
    (β : I →₀ ℕ) (μ : X) {m m' n n' : X} (hm : m = m') (hn : n = n') (h : m + D.α i = n)
    (h' : m' + D.α i = n') {Z : homWeightSector T W.obj μ n} {Z' : homWeightSector T W.obj μ n'}
    (hZ : Z ≍ Z') :
    (homContentPostF T W i β μ h).obj Z ≍ (homContentPostF T W i β μ h').obj Z' := by
  subst hm hn
  obtain rfl := eq_of_heq hZ
  rfl

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
  let α ← inferType w
  g.assign (mkApp4 (.const ``Exists.intro [.zero]) α body w prf)
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

omit [AddCommGroup X] in
/-- A power `p` with `p a ≠ 1` in `ZMod 2` is a multiple of `2` when `a = 1`. -/
theorem dvd_of_mul_parity_ne_one {a : ZMod 2} {p : ℕ} (h : (p : ZMod 2) * a ≠ 1) :
    (if a = 1 then 2 else 1) ∣ p := by
  split_ifs with ha
  · subst ha
    rw [mul_one] at h
    rcases Nat.even_or_odd p with hp | hp
    · exact even_iff_two_dvd.mp hp
    · exact absurd (ZMod.natCast_eq_one_iff_odd.mpr hp) h
  · exact one_dvd p

omit [AddCommGroup X] in
theorem mul_parity_pow_eq_zero (a : ZMod 2) :
    (((if a = 1 then 2 else 1 : ℕ)) : ZMod 2) * a = 0 := by
  fin_cases a <;> decide

attribute [local irreducible] Finsupp.zipWith Finsupp.single Finsupp.onFinset homContentShift
  contentWeight in

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
