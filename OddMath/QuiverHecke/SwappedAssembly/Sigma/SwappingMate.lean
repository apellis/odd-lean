/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingEntries
import OddMath.SKM.RouquierHomDistinctMixedDots

/-! # The swapping block `W_A` of the same-colour sideways crossing is invertible

The entry `W_A` of `docs/Nondegeneracy/AugmentedSectorBlocks.md` §2 of the sideways crossing
`σ = sigmaL i i : Eᵢ Fᵢ → Fᵢ Eᵢ` of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5, (1.11), between the summand paths `[R, P]` and `[P, R]`,
is the mate of the mixed interchange `J` under the probe adjunction: unit, `J`, counit. Up to
the transport of objects along equalities of weights, this is `homDistinctMixedPreMate`, whose
inverse is the explicit word (15) of `OddMath.SKM.homDistinctMixedPreMate_inv_products`.

## Main results

* `OddMath.SKM.isIso_homContentDistinctMixedPreMate`: the mate of `J` for the content-shifted
  precomposition adjunctions is invertible.
* `OddMath.SKM.isIso_homContentDistinctMixedPreMate_of_eq`: the same, with the unit taken at a
  weight equal to that of the counit and the objects matched along equalities.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams

universe r u v w

section Mate
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (W : X → B) (L : RouquierLeftAdjoints (k := k) T)
  (i : I)

/-- The mate of the mixed interchange `J` for the content-shifted precomposition adjunctions
is invertible, with inverse the word (15). -/
theorem isIso_homContentDistinctMixedPreMate {muM muM' muP nuP : X}
    (h : -nuP + D.α i = -muP) (E' : W muM ⟶ W muM') (t u : ZMod 2)
    (H : homWeightSector T.obj W nuP muM) :
    IsIso (homDistinctMixedPreMate (T.E i h) E' t u (homContentPreAdjunction T W L i muM' h)
      (homContentPreAdjunction T W L i muM h) H) :=
  ⟨⟨_, homDistinctMixedPreMate_inv_products (L.adjL i h)
    (fun Y => homContentPreAdjunction_unit_app T W i muM' h L Y)
    (fun Z => homContentPreAdjunction_counit_app T W i muM h L Z) H⟩⟩

/-- The mate of `J` is invertible when the unit is taken at a weight `b'` equal to the weight
`b` of the counit, with all objects matched along equalities. -/
theorem isIso_homContentDistinctMixedPreMate_of_eq {nuP muM muM' b b' : X} (eb : b = b')
    (h : -nuP + D.α i = -b) (h' : -nuP + D.α i = -b') (E' : W muM ⟶ W muM')
    (tsh u : ZMod 2)
    {A0 A1 Y A5 A16 : homWeightSector T.obj W b' muM'}
    {U : homWeightSector T.obj W nuP muM'}
    {Zj V₁ : homWeightSector T.obj W b muM} {V Y₂ V' : homWeightSector T.obj W nuP muM}
    (J : (homContentPreE T W i muM' h).obj
        ((homPost (k := k) E' ⋙ homParityShift (k := k) tsh).obj Zj) ⟶
      (homPost (k := k) E' ⋙ homParityShift (k := k) u).obj
        ((homContentPreE T W i muM h).obj Zj))
    (hJ : J = (homMixedInterchange (k := k) (T.E i h) E' tsh u Zj).hom)
    (x₁ : A0 = A1) (x₂ : A1 = Y)
    (x₃ : (homContentPreE T W i muM' h').obj Y = U)
    (x₄ : (homContentPreF T W i muM' h').obj U = A5)
    (x₅ : A5 = (homContentPreF T W i muM' h').obj ((homContentPreE T W i muM' h).obj
        ((homPost (k := k) E' ⋙ homParityShift (k := k) tsh).obj Zj)))
    (x₆ : (homContentPreF T W i muM' h').obj
      ((homPost (k := k) E' ⋙ homParityShift (k := k) u).obj
        ((homContentPreE T W i muM h).obj Zj)) =
      (homContentPreF T W i muM' h').obj
        ((homPost (k := k) E' ⋙ homParityShift (k := k) u).obj V))
    (x₇ : V = (homContentPreE T W i muM h).obj V₁)
    (x₈ : V₁ = (homContentPreF T W i muM h).obj Y₂) (x₉ : Y₂ = V')
    (x₁₀ : (homContentPreF T W i muM' h').obj
      ((homPost (k := k) E' ⋙ homParityShift (k := k) u).obj V') = A16)
    (xY : HEq Y ((homPost (k := k) E' ⋙ homParityShift (k := k) tsh).obj Zj))
    (xZ : Zj = V₁) :
    IsIso (eqToHom x₁ ≫ eqToHom x₂ ≫
      (homContentPreAdjunction T W L i muM' h').unit.app Y ≫
      (homContentPreF T W i muM' h').map (eqToHom x₃) ≫ eqToHom x₄ ≫ eqToHom x₅ ≫
      (homContentPreF T W i muM' h').map J ≫ eqToHom x₆ ≫
      (homContentPreF T W i muM' h').map ((homPost (k := k) E' ⋙ homParityShift (k := k) u).map
        (eqToHom x₇ ≫ (homContentPreE T W i muM h).map (eqToHom x₈) ≫
          (homContentPreAdjunction T W L i muM h).counit.app Y₂ ≫ eqToHom x₉)) ≫
      eqToHom x₁₀) := by
  subst eb
  obtain rfl : h' = h := rfl
  obtain rfl := eq_of_heq xY
  subst hJ x₁ x₂ x₃ x₄ x₁₀ x₉ x₈ xZ x₇
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_id]
  rw [← Functor.map_comp]
  erw [Category.id_comp]
  exact isIso_homContentDistinctMixedPreMate T W L i h' E' tsh u Y₂

end Mate

end OddMath.SKM

namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM
universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}

/-- The single term of the sideways crossing along the intermediate paths `m₁`, `m₂`, with each
of its three layers written through a decomposition of its paths around the generator. -/
theorem sigmaTerm_eq_of_paths (gens : P.Generators) (i j : I) (ν : X)
    {t s x₁ y₁ x₂ y₂ x₃ y₃ : Sector I}
    (p : SPath (wd D ν [up j, dn i]) t s) (q : SPath (wd D ν [dn i, up j]) t s)
    (m₁ : SPath (sigL₁ (D := D) i j ν).cod.word t s)
    (m₂ : SPath (sigL₂ (D := D) i j ν).cod.word t s)
    (pu₁ : SPath (sigL₁ (D := D) i j ν).left t x₁)
    (pg₁ : SPath ((SKM.sig D).dom (sigL₁ (D := D) i j ν).gen) x₁ y₁)
    (qg₁ : SPath ((SKM.sig D).cod (sigL₁ (D := D) i j ν).gen) x₁ y₁)
    (pv₁ : SPath (sigL₁ (D := D) i j ν).right y₁ s)
    (hp₁ : (pu₁.append pg₁).append pv₁ = p.cast (sigL₁_dom i j ν))
    (hq₁ : (pu₁.append qg₁).append pv₁ = m₁)
    (pu₂ : SPath (sigL₂ (D := D) i j ν).left t x₂)
    (pg₂ : SPath ((SKM.sig D).dom (sigL₂ (D := D) i j ν).gen) x₂ y₂)
    (qg₂ : SPath ((SKM.sig D).cod (sigL₂ (D := D) i j ν).gen) x₂ y₂)
    (pv₂ : SPath (sigL₂ (D := D) i j ν).right y₂ s)
    (hp₂ : (pu₂.append pg₂).append pv₂ = m₁.cast (sigL₂_dom i j ν))
    (hq₂ : (pu₂.append qg₂).append pv₂ = m₂)
    (pu₃ : SPath (sigL₃ (D := D) i j ν).left t x₃)
    (pg₃ : SPath ((SKM.sig D).dom (sigL₃ (D := D) i j ν).gen) x₃ y₃)
    (qg₃ : SPath ((SKM.sig D).cod (sigL₃ (D := D) i j ν).gen) x₃ y₃)
    (pv₃ : SPath (sigL₃ (D := D) i j ν).right y₃ s)
    (hp₃ : (pu₃.append pg₃).append pv₃ = m₂.cast (sigL₃_dom i j ν))
    (hq₃ : (pu₃.append qg₃).append pv₃ = q.cast (sigL₃_cod i j ν)) (Z : P.H s) :
    sigmaTerm gens i j ν p q m₁ m₂ Z =
      eqToHom (by rw [← P.pathFunctor_append_append_obj, hp₁, pathFunctor_cast]) ≫
        (P.pathFunctor pu₁).map (gens.image _ pg₁ qg₁ ((P.pathFunctor pv₁).obj Z)) ≫
        eqToHom (by rw [← P.pathFunctor_append_append_obj, ← P.pathFunctor_append_append_obj,
          hq₁, hp₂, pathFunctor_cast]) ≫
        (P.pathFunctor pu₂).map (gens.image _ pg₂ qg₂ ((P.pathFunctor pv₂).obj Z)) ≫
        eqToHom (by rw [← P.pathFunctor_append_append_obj, ← P.pathFunctor_append_append_obj,
          hq₂, hp₃, pathFunctor_cast]) ≫
        (P.pathFunctor pu₃).map (gens.image _ pg₃ qg₃ ((P.pathFunctor pv₃).obj Z)) ≫
        eqToHom (by rw [← P.pathFunctor_append_append_obj, hq₃, pathFunctor_cast]) := by
  unfold sigmaTerm
  rw [compLayer_eq_of_path gens _ pu₁ pg₁ qg₁ pv₁ _ _ hp₁ hq₁,
    compLayer_eq_of_path gens _ pu₂ pg₂ qg₂ pv₂ _ _ hp₂ hq₂,
    compLayer_eq_of_path gens _ pu₃ pg₃ qg₃ pv₃ _ _ hp₃ hq₃]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]


/-- The probe mate of the mixed interchange at the sector `t`, written with the strand functors
of the sectors, is invertible. -/
theorem isIso_probeMixedMate (i : I) {t : Sector I} (hw₁ : StepValid (false, i) true t)
    (hv₁ : StepValid (true, i) false (nextSector (true, i) true (nextSector (false, i) true t)))
    (hw₂ : StepValid (true, i) false (nextSector (false, i) true t))
    (hs : -P.muP (nextSector (true, i) false (nextSector (false, i) true t)) + D.α i =
      -P.muP (nextSector (true, i) true (nextSector (true, i) false (nextSector (false, i) true t))))
    {A0 A1 Y A5 A16 : P.H t} {U : P.H (nextSector (false, i) true t)}
    {Zj : P.H (nextSector (true, i) false (nextSector (true, i) true (nextSector (false, i) true t)))}
    {V₁ : P.H (nextSector (true, i) true (nextSector (true, i) false (nextSector (false, i) true t)))}
    {V Y₂ V' : P.H (nextSector (true, i) false (nextSector (false, i) true t))}
    (x₁ : A0 = A1) (x₂ : A1 = Y)
    (x₃ : (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hw₁)).obj Y = U)
    (x₄ : (P.step (false, i) true t hw₁).obj U = A5)
    (x₅ : A5 = (P.step (false, i) true t hw₁).obj
      (P.prObj i i (nextSector (false, i) true t) hv₁ Zj))
    (x₆ : (P.step (false, i) true t hw₁).obj (P.rpObj i i (nextSector (false, i) true t) hv₁ Zj) =
      (P.step (false, i) true t hw₁).obj
        ((P.step (true, i) false (nextSector (false, i) true t) hw₂).obj V))
    (x₇ : V = (P.step (true, i) true _ trivial).obj V₁)
    (x₈ : V₁ = (homContentPreF P.T P.W.obj i
      (P.muM (nextSector (true, i) false (nextSector (false, i) true t))) hs).obj Y₂)
    (x₉ : Y₂ = V')
    (x₁₀ : (P.step (false, i) true t hw₁).obj
        ((P.step (true, i) false (nextSector (false, i) true t) hw₂).obj V') = A16)
    (xY : HEq Y ((P.step (true, i) false _ hv₁).obj Zj)) (xZ : HEq Zj V₁) :
    IsIso (eqToHom x₁ ≫ eqToHom x₂ ≫ (P.preAdjAt i hw₁).unit.app Y ≫
      (P.step (false, i) true t hw₁).map (eqToHom x₃) ≫ eqToHom x₄ ≫ eqToHom x₅ ≫
      (P.step (false, i) true t hw₁).map (P.mixedJ i i _ hv₁ Zj).hom ≫ eqToHom x₆ ≫
      (P.step (false, i) true t hw₁).map ((P.step (true, i) false _ hw₂).map
        (eqToHom x₇ ≫ (P.step (true, i) true _ trivial).map (eqToHom x₈) ≫
          (homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
            (P.muM (nextSector (true, i) false (nextSector (false, i) true t))) hs).counit.app Y₂ ≫
          eqToHom x₉)) ≫ eqToHom x₁₀) :=
  isIso_homContentDistinctMixedPreMate_of_eq P.T P.W.obj P.T.leftAdjoints i
    (nuP := P.muP (nextSector (false, i) true t))
    (muM := P.muM (nextSector (true, i) false (nextSector (false, i) true t)))
    (muM' := P.muM t) (b' := P.muP t)
    (b := P.muP (nextSector (true, i) true (nextSector (true, i) false (nextSector (false, i) true t))))
    (by simp [muP, nextSector, tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hw₁)])
    hs (P.muP_preF i hw₁) (P.W.E i (P.muM_postE i hw₂))
    (homContentShift D i ((nextSector (false, i) true t).1 + Finsupp.single i 1))
    (homContentShift D i (nextSector (false, i) true t).1)
    (P.mixedJ i i _ hv₁ Zj).hom rfl x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ xY (eq_of_heq xZ)



-- Comparisons of distinct sectors are decided on the sector expressions, not by computing with
-- finitely supported functions.
attribute [local irreducible] Finsupp.zipWith contentWeight

/-- A probe `Fᵢ` followed by a probe `Eᵢ` returns to the sector. -/
theorem nextSector_up_dn {i : I} {t : Sector I} (h : StepValid (false, i) true t) :
    nextSector (true, i) true (nextSector (false, i) true t) = t := by
  obtain ⟨a, b⟩ := t
  simp only [StepValid] at h
  simp only [nextSector, Prod.mk.injEq, and_true]
  exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h)

/-- A probe `Eᵢ` followed by a probe `Fᵢ` returns to the sector. -/
theorem nextSector_dn_up {i : I} (t : Sector I) :
    nextSector (false, i) true (nextSector (true, i) true t) = t := by
  obtain ⟨a, b⟩ := t
  simp only [nextSector, Prod.mk.injEq, and_true]
  exact add_tsub_cancel_right a _

/-- A probe `Fᵢ` cancels the probe `Eᵢ` across a reservoir `Eᵢ`. -/
theorem nextSector_dn_upR_up {i : I} (t : Sector I) :
    nextSector (false, i) true (nextSector (true, i) false (nextSector (true, i) true t)) =
      nextSector (true, i) false t := by
  obtain ⟨a, b⟩ := t
  simp only [nextSector, Prod.mk.injEq, and_true]
  exact add_tsub_cancel_right a _

/-- Transport of a path along an equality of its target sector. -/
def _root_.OddMath.QuiverHecke.SwappedAssembly.SPath.castTgt {w : List (Col I X)} {s t t' : Sector I}
    (h : t = t') (p : SPath w s t) : SPath w s t' := h ▸ p

omit [AddCommGroup X] in
/-- Transport along the target sector keeps the sides. -/
@[simp] theorem _root_.OddMath.QuiverHecke.SwappedAssembly.SPath.sides_castTgt
    {w : List (Col I X)} {s t t' : Sector I} (h : t = t') (p : SPath w s t) :
    (p.castTgt h).sides = p.sides := by subst h; rfl

set_option linter.unusedVariables false in
/-- The functor of an empty path is the identity, up to the type of its target. -/
theorem pathFunctor_obj_heq_of_nil {a b : Sector I} (p : SPath ([] : List (Col I X)) a b)
    (Z : P.H b) : HEq ((P.pathFunctor p).obj Z) Z := by
  cases p; rfl

/-- A strand functor at equal sectors on equal objects. -/
theorem step_obj_heq {l : Letter I} {side : Bool} {a a' : Sector I} (e : a = a')
    (hv : StepValid l side a) (hv' : StepValid l side a') {Z₁ : P.H (nextSector l side a)}
    {Z₂ : P.H (nextSector l side a')} (hZ : HEq Z₁ Z₂) :
    HEq ((P.step l side a hv).obj Z₁) ((P.step l side a' hv').obj Z₂) := by
  subst e; cases hZ; rfl

/-- A reservoir `Eᵢ` and a probe `Eᵢ` commute on sectors. -/
theorem nextSector_upR_upP {i : I} (t : Sector I) :
    nextSector (true, i) false (nextSector (true, i) true t) =
      nextSector (true, i) true (nextSector (true, i) false t) := by
  obtain ⟨a, b⟩ := t
  rfl

/-- The functor of a one-letter path is the strand functor of its letter. -/
theorem pathFunctor_one_obj_heq {c : Col I X} {a a' s : Sector I} (e : a = a') (τ : Bool)
    (pv : SPath [c] a s) (hpv : pv.sides = [τ]) (hv' : StepValid c.l τ a') (Z : P.H s)
    {W : P.H (nextSector c.l τ a')} (hW : HEq W Z) :
    HEq ((P.pathFunctor pv).obj Z) ((P.step c.l τ a' hv').obj W) := by
  subst e
  cases pv with
  | cons _ σ _ hw p =>
    simp only [SPath.sides, List.cons.injEq] at hpv
    obtain ⟨rfl, -⟩ := hpv
    exact step_obj_heq rfl _ _ ((pathFunctor_obj_heq_of_nil p Z).trans hW.symm)

/-- The functor of a two-letter path is the composite of the strand functors. -/
theorem pathFunctor_two_obj_heq {c₁ c₂ : Col I X} {a a' s : Sector I} (e : a = a')
    (τ₁ τ₂ : Bool) (hw₁ : StepValid c₁.l τ₁ a) (hw₂ : StepValid c₂.l τ₂ (nextSector c₁.l τ₁ a))
    (ep : nextSector c₂.l τ₂ (nextSector c₁.l τ₁ a) = s) (hv' : StepValid c₁.l τ₁ a')
    (pv : SPath [c₂] (nextSector c₁.l τ₁ a') s) (hpv : pv.sides = [τ₂]) (Z : P.H s) :
    HEq ((P.pathFunctor (SPath.two τ₁ τ₂ hw₁ hw₂ ep)).obj Z)
      ((P.step c₁.l τ₁ a' hv').obj ((P.pathFunctor pv).obj Z)) := by
  subst e
  refine step_obj_heq rfl _ _ ?_
  exact (pathFunctor_one_obj_heq rfl τ₂ pv hpv hw₂ Z
    ((pathFunctor_obj_heq_of_nil _ Z))).symm

/-- The swapping entry `W_A` of the same-colour sideways crossing, from the path `(R,P)` of
`Eᵢ Fᵢ` to the path `(P,R)` of `Fᵢ Eᵢ`, is invertible: it is the probe mate of the mixed
interchange `J`. -/
theorem isIso_sigmaEntry_probe (c : P.CrossCoeff) (i : I) (ν : X) {t s : Sector I}
    (p : SPath (wd D ν [up i, dn i]) t s) (q : SPath (wd D ν [dn i, up i]) t s)
    (hp : p.sides = [false, true]) (hq : q.sides = [true, false]) (Z : P.H s) :
    IsIso (P.sigmaEntry c i i ν p q Z) := by
  obtain ⟨τ₁, τ₂, hv₁, hv₂, ep, rfl⟩ := SPath.exists_eq_two p
  obtain ⟨σ₁, σ₂, hw₁, hw₂, eq, rfl⟩ := SPath.exists_eq_two q
  rw [SPath.sides_two] at hp hq
  simp only [List.cons.injEq, and_true] at hp hq
  obtain ⟨rfl, rfl⟩ := hp
  obtain ⟨rfl, rfl⟩ := hq
  subst eq
  -- the cup
  let qg₁ : SPath ((SKM.sig D).cod (sigL₁ (D := D) i i ν).gen) t t :=
    SPath.two true true hw₁ trivial (nextSector_up_dn hw₁)
  let m₁ : SPath (sigL₁ (D := D) i i ν).cod.word t _ :=
    ((SPath.nil t).append qg₁).append (SPath.two false true hv₁ hv₂ ep)
  -- the crossing
  let t' := nextSector (false, i) true t
  let x := nextSector (true, i) false (nextSector (true, i) true t')
  have hx : StepValid (false, i) true x := by
    simp [x, t', StepValid, nextSector]
  let pu₂ : SPath (sigL₂ (D := D) i i ν).left t t' := .cons _ true t hw₁ (.nil _)
  let pg₂ : SPath ((SKM.sig D).dom (sigL₂ (D := D) i i ν).gen) t' x :=
    .cons _ true t' trivial (.cons _ false _ hv₁ (.nil _))
  let qg₂ : SPath ((SKM.sig D).cod (sigL₂ (D := D) i i ν).gen) t' x :=
    .cons _ false t' hv₁ (.cons _ true _ trivial (.nil _))
  let pv₂ : SPath (sigL₂ (D := D) i i ν).right x (nextSector (true, i) false t') :=
    .cons _ true x hx ((SPath.nil _).castTgt (nextSector_dn_upR_up (i := i) t'))
  let m₂ : SPath (sigL₂ (D := D) i i ν).cod.word t _ := (pu₂.append qg₂).append pv₂
  rw [sigmaEntry_eq_sigmaTerm (m₁ := m₁) (m₂ := m₂) (p₁ := false) (p₂ := true) (q₁ := true) (q₂ := false)
    (hp := rfl) (hq := rfl) (hm₁ := by simp [m₁, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides]) (hm₂ := by simp [m₂, pu₂, qg₂, pv₂, SPath.sides_append, SPath.sides])]
  have sd := @SPath.sides_cast.{u}
  -- the cap
  let s₀ := nextSector (true, i) false t'
  have hd : StepValid (false, i) true (nextSector (true, i) true s₀) := by
    simp [StepValid, nextSector]
  let pu₃ : SPath (sigL₃ (D := D) i i ν).left t s₀ :=
    .cons _ true t hw₁ (.cons _ false _ hw₂ (.nil _))
  let pg₃ : SPath ((SKM.sig D).dom (sigL₃ (D := D) i i ν).gen) s₀ s₀ :=
    SPath.two true true trivial hd (nextSector_dn_up s₀)
  rw [sigmaTerm_eq_of_paths _ i i ν _ _ m₁ m₂ (SPath.nil t) (SPath.nil t) qg₁
      (SPath.two false true hv₁ hv₂ ep)
      (SPath.eq_of_sides _ _ (by simp [SPath.sides_append, SPath.sides_two, SPath.sides]))
      (SPath.eq_of_sides _ _ (by simp [m₁, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides]))
      pu₂ pg₂ qg₂ pv₂
      (SPath.eq_of_sides _ _ (by simp [m₁, qg₁, pu₂, pg₂, pv₂, SPath.sides_append, SPath.sides_two, SPath.sides]))
      (SPath.eq_of_sides _ _ (by simp [m₂, pu₂, qg₂, pv₂, SPath.sides_append, SPath.sides]))
      pu₃ pg₃ (SPath.nil s₀) (SPath.nil s₀)
      (SPath.eq_of_sides _ _ (by simp [m₂, pu₂, qg₂, pv₂, pu₃, pg₃, SPath.sides_append, SPath.sides_two, SPath.sides]))
      (SPath.eq_of_sides _ _ (by simp [pu₃, sd, SPath.sides_append, SPath.sides_two, SPath.sides]))]
  simp only [upwardGens, Generators.image, sigL₁, sigL₂, sigL₃, SKM.lay, crossImage, dite_eq_left,
    cupImage, capImage]
  have hcross : ∀ W, P.twoTwo _ _ _ _ (P.crossSameEntry c i _ _ _ _) pg₂ qg₂ rfl W =
      (P.mixedJ i i t' hv₁ W).hom := fun W => rfl
  erw [hcross]
  simp only [qg₁, pg₃]
  rw [zeroTwo_two (Z' := (nextSector_up_dn hw₁).symm ▸ _) (hZ := eqRec_heq _ _)]
  rw [twoZero_two (Z' := (nextSector_dn_up s₀).symm ▸ _) (hZ := eqRec_heq _ _)]
  simp only [cupEntry, capEntry, preCup, preCap]
  simp only [pu₂, pu₃, pathFunctor_cons, pathFunctor_nil, Functor.comp_map, Functor.id_map]
  simp only [Category.assoc]
  apply isIso_probeMixedMate i hw₁ hv₁ hw₂
  · refine (eqRec_heq _ _).trans ?_
    refine (eqRec_heq _ _).trans ?_
    exact pathFunctor_two_obj_heq (nextSector_up_dn hw₁).symm false true hv₁ hv₂ ep hv₁ pv₂
      (congrArg (List.cons true) (SPath.sides_castTgt _ _)) Z
  · exact pathFunctor_one_obj_heq (nextSector_upR_upP t') true pv₂ (congrArg (List.cons true) (SPath.sides_castTgt _ _))
      hd Z ((eqRec_heq _ _).trans (pathFunctor_obj_heq_of_nil _ Z))
/-- Between distinct sectors, the paths of `Eᵢ Fᵢ` and `Fᵢ Eᵢ` are `(R,P)` and `(P,R)`, or
`(P,R)` and `(R,P)`. -/
theorem sides_upDn_dnUp_of_ne {i : I} {ν : X} {t s : Sector I} (hts : t ≠ s)
    (p : SPath (wd D ν [up i, dn i]) t s) (q : SPath (wd D ν [dn i, up i]) t s) :
    (p.sides = [false, true] ∧ q.sides = [true, false]) ∨
      (p.sides = [true, false] ∧ q.sides = [false, true]) := by
  obtain ⟨a, b, hv₁, hv₂, ep, rfl⟩ := SPath.exists_eq_two p
  obtain ⟨a', b', hw₁, hw₂, eq, rfl⟩ := SPath.exists_eq_two q
  simp only [SPath.sides_two]
  have key := congrArg (fun x : Sector I => x.1 i) (ep.trans eq.symm)
  rcases SPath.upDn_sides_of_ne hts a b hv₁ hv₂ ep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases SPath.dnUp_sides_of_ne hts a' b' hw₁ hw₂ eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [nextSector, StepValid] at key hw₁; omega
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · simp [nextSector] at key hv₂

/-- The swapping entries `W_B` of the same-colour sideways crossing, from the path `(P,R)` of
`Eᵢ Fᵢ` to the path `(R,P)` of `Fᵢ Eᵢ`, are invertible. This is the reservoir mate of
`-(a;a;J⁻¹)`; it is a hypothesis here. -/
def SwappingReservoirInvertible (P : ProbeReservoir k B D Sc) (c : P.CrossCoeff) : Prop :=
  ∀ (i : I) (ν : X) (t s : Sector I) (p : SPath (wd D ν [up i, dn i]) t s)
    (q : SPath (wd D ν [dn i, up i]) t s), p.sides = [true, false] → q.sides = [false, true] →
    ∀ Z : P.H s, IsIso (P.sigmaEntry c i i ν p q Z)

/-- The swapping entries are invertible once the reservoir entries `W_B` are. -/
theorem swappingInvertible_of_reservoir (c : P.CrossCoeff)
    (h : P.SwappingReservoirInvertible c) : P.SwappingInvertible c := by
  intro i ν t s hts p q Z
  rcases sides_upDn_dnUp_of_ne hts p q with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact isIso_sigmaEntry_probe c i ν p q hp hq Z
  · exact h i ν t s p q hp hq Z
end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
