/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingMate

/-! # The sideways crossing on a reservoir/probe path for distinct colours

For `i ≠ j`, the entry of the sideways crossing `σ : Eⱼ Fᵢ → Fᵢ Eⱼ` of Brundan–Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5, (1.11), in the swapped
Hom construction, from the summand path `(R,P)` of `Eⱼ Fᵢ` (the letter `Eⱼ` on the reservoir,
`Fᵢ` on the probe) to the path `(P,R)` of `Fᵢ Eⱼ`. The cup and the cap are on the probe, and
the upward crossing contributes the mixed interchange `J` alone, without the polynomial `Q`.
So the entry is the probe mate of `J`, which is invertible with the explicit inverse (15) of
`OddMath.SKM.homDistinctMixedPreMate_inv_products`; no hypothesis on dots is needed. This is
the distinct-colour analogue of `ProbeReservoir.isIso_sigmaEntry_probe`.

## Main results

* `ProbeReservoir.isIso_probeMixedMateNe`: the probe mate of the mixed interchange of
  `Eᵢ Eⱼ`, written with the strand functors of the sectors, is invertible.
* `ProbeReservoir.isIso_sigmaEntry_reservoir_probe`: the entry of `σ` from `(R,P)` to `(P,R)`
  is an isomorphism.
-/

noncomputable section

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

/-- The probe mate of the mixed interchange of `Eᵢ Eⱼ` at the sector `t`, written with the
strand functors of the sectors, is invertible. -/
theorem isIso_probeMixedMateNe (i j : I) {t : Sector I} (hw₁ : StepValid (false, i) true t)
    (hv₁ : StepValid (true, j) false (nextSector (true, i) true (nextSector (false, i) true t)))
    (hw₂ : StepValid (true, j) false (nextSector (false, i) true t))
    (hs : -P.muP (nextSector (true, j) false (nextSector (false, i) true t)) + D.α i =
      -P.muP (nextSector (true, i) true (nextSector (true, j) false (nextSector (false, i) true t))))
    {A0 A1 Y A5 A16 : P.H t} {U : P.H (nextSector (false, i) true t)}
    {Zj : P.H (nextSector (true, j) false (nextSector (true, i) true (nextSector (false, i) true t)))}
    {V₁ : P.H (nextSector (true, i) true (nextSector (true, j) false (nextSector (false, i) true t)))}
    {V Y₂ V' : P.H (nextSector (true, j) false (nextSector (false, i) true t))}
    (x₁ : A0 = A1) (x₂ : A1 = Y)
    (x₃ : (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hw₁)).obj Y = U)
    (x₄ : (P.step (false, i) true t hw₁).obj U = A5)
    (x₅ : A5 = (P.step (false, i) true t hw₁).obj
      (P.prObj i j (nextSector (false, i) true t) hv₁ Zj))
    (x₆ : (P.step (false, i) true t hw₁).obj (P.rpObj j i (nextSector (false, i) true t) hv₁ Zj) =
      (P.step (false, i) true t hw₁).obj
        ((P.step (true, j) false (nextSector (false, i) true t) hw₂).obj V))
    (x₇ : V = (P.step (true, i) true _ trivial).obj V₁)
    (x₈ : V₁ = (homContentPreF P.T P.W.obj i
      (P.muM (nextSector (true, j) false (nextSector (false, i) true t))) hs).obj Y₂)
    (x₉ : Y₂ = V')
    (x₁₀ : (P.step (false, i) true t hw₁).obj
        ((P.step (true, j) false (nextSector (false, i) true t) hw₂).obj V') = A16)
    (xY : HEq Y ((P.step (true, j) false _ hv₁).obj Zj)) (xZ : HEq Zj V₁) :
    IsIso (eqToHom x₁ ≫ eqToHom x₂ ≫ (P.preAdjAt i hw₁).unit.app Y ≫
      (P.step (false, i) true t hw₁).map (eqToHom x₃) ≫ eqToHom x₄ ≫ eqToHom x₅ ≫
      (P.step (false, i) true t hw₁).map (P.mixedJ i j _ hv₁ Zj).hom ≫ eqToHom x₆ ≫
      (P.step (false, i) true t hw₁).map ((P.step (true, j) false _ hw₂).map
        (eqToHom x₇ ≫ (P.step (true, i) true _ trivial).map (eqToHom x₈) ≫
          (homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i
            (P.muM (nextSector (true, j) false (nextSector (false, i) true t))) hs).counit.app Y₂ ≫
          eqToHom x₉)) ≫ eqToHom x₁₀) :=
  isIso_homContentDistinctMixedPreMate_of_eq P.T P.W.obj P.T.leftAdjoints i
    (nuP := P.muP (nextSector (false, i) true t))
    (muM := P.muM (nextSector (true, j) false (nextSector (false, i) true t)))
    (muM' := P.muM t) (b' := P.muP t)
    (b := P.muP (nextSector (true, i) true (nextSector (true, j) false (nextSector (false, i) true t))))
    (by simp [muP, nextSector, tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hw₁)])
    hs (P.muP_preF i hw₁) (P.W.E j (P.muM_postE j hw₂))
    (homContentShift D j ((nextSector (false, i) true t).1 + Finsupp.single i 1))
    (homContentShift D j (nextSector (false, i) true t).1)
    (P.mixedJ i j _ hv₁ Zj).hom rfl x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ xY (eq_of_heq xZ)

-- Comparisons of distinct sectors are decided on the sector expressions, not by computing with
-- finitely supported functions.
attribute [local irreducible] Finsupp.zipWith contentWeight

/-- A probe `Fᵢ` cancels the probe `Eᵢ` across a reservoir `Eⱼ`. -/
theorem nextSector_dn_resUp_up {i j : I} (t : Sector I) :
    nextSector (false, i) true (nextSector (true, j) false (nextSector (true, i) true t)) =
      nextSector (true, j) false t := by
  obtain ⟨a, b⟩ := t
  simp only [nextSector, Prod.mk.injEq, and_true]
  exact add_tsub_cancel_right a _

/-- A reservoir `Eⱼ` and a probe `Eᵢ` commute on sectors. -/
theorem nextSector_resUp_probeUp {i j : I} (t : Sector I) :
    nextSector (true, j) false (nextSector (true, i) true t) =
      nextSector (true, i) true (nextSector (true, j) false t) := by
  obtain ⟨a, b⟩ := t
  rfl

/-- **The sideways crossing entry on a reservoir/probe path is invertible.** For `i ≠ j`,
the entry of `σ : Eⱼ Fᵢ → Fᵢ Eⱼ` (Brundan–Ellis, arXiv:1701.04133v2, (1.11)) from the path
`(R,P)` of `Eⱼ Fᵢ` to the path `(P,R)` of `Fᵢ Eⱼ` is the probe mate of the mixed
interchange `J`. -/
theorem isIso_sigmaEntry_reservoir_probe (c : P.CrossCoeff) {i j : I} (hij : i ≠ j) (ν : X)
    {t s : Sector I} (p : SPath (wd D ν [up j, dn i]) t s) (q : SPath (wd D ν [dn i, up j]) t s)
    (hp : p.sides = [false, true]) (hq : q.sides = [true, false]) (Z : P.H s) :
    IsIso (P.sigmaEntry c i j ν p q Z) := by
  obtain ⟨τ₁, τ₂, hv₁, hv₂, ep, rfl⟩ := SPath.exists_eq_two p
  obtain ⟨σ₁, σ₂, hw₁, hw₂, eq, rfl⟩ := SPath.exists_eq_two q
  rw [SPath.sides_two] at hp hq
  simp only [List.cons.injEq, and_true] at hp hq
  obtain ⟨rfl, rfl⟩ := hp
  obtain ⟨rfl, rfl⟩ := hq
  subst eq
  -- the cup
  let qg₁ : SPath ((SKM.sig D).cod (sigL₁ (D := D) i j ν).gen) t t :=
    SPath.two true true hw₁ trivial (nextSector_up_dn hw₁)
  let m₁ : SPath (sigL₁ (D := D) i j ν).cod.word t _ :=
    ((SPath.nil t).append qg₁).append (SPath.two false true hv₁ hv₂ ep)
  -- the crossing
  let t' := nextSector (false, i) true t
  let x := nextSector (true, j) false (nextSector (true, i) true t')
  have hx : StepValid (false, i) true x := by
    simp [x, t', StepValid, nextSector]
  let pu₂ : SPath (sigL₂ (D := D) i j ν).left t t' := .cons _ true t hw₁ (.nil _)
  let pg₂ : SPath ((SKM.sig D).dom (sigL₂ (D := D) i j ν).gen) t' x :=
    .cons _ true t' trivial (.cons _ false _ hv₁ (.nil _))
  let qg₂ : SPath ((SKM.sig D).cod (sigL₂ (D := D) i j ν).gen) t' x :=
    .cons _ false t' hv₁ (.cons _ true _ trivial (.nil _))
  let pv₂ : SPath (sigL₂ (D := D) i j ν).right x (nextSector (true, j) false t') :=
    .cons _ true x hx ((SPath.nil _).castTgt (nextSector_dn_resUp_up (i := i) (j := j) t'))
  let m₂ : SPath (sigL₂ (D := D) i j ν).cod.word t _ := (pu₂.append qg₂).append pv₂
  rw [sigmaEntry_eq_sigmaTerm (m₁ := m₁) (m₂ := m₂) (p₁ := false) (p₂ := true) (q₁ := true)
    (q₂ := false) (hp := rfl) (hq := rfl)
    (hm₁ := by simp [m₁, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides])
    (hm₂ := by simp [m₂, pu₂, qg₂, pv₂, SPath.sides_append, SPath.sides])]
  have sd := @SPath.sides_cast.{u}
  -- the cap
  let s₀ := nextSector (true, j) false t'
  have hd : StepValid (false, i) true (nextSector (true, i) true s₀) := by
    simp [s₀, StepValid, nextSector]
  let pu₃ : SPath (sigL₃ (D := D) i j ν).left t s₀ :=
    .cons _ true t hw₁ (.cons _ false _ hw₂ (.nil _))
  let pg₃ : SPath ((SKM.sig D).dom (sigL₃ (D := D) i j ν).gen) s₀ s₀ :=
    SPath.two true true trivial hd (nextSector_dn_up s₀)
  rw [sigmaTerm_eq_of_paths _ i j ν _ _ m₁ m₂ (SPath.nil t) (SPath.nil t) qg₁
      (SPath.two false true hv₁ hv₂ ep)
      (SPath.eq_of_sides _ _ (by simp [SPath.sides_append, SPath.sides_two, SPath.sides]))
      (SPath.eq_of_sides _ _ (by simp [m₁, qg₁, SPath.sides_append, SPath.sides_two, SPath.sides]))
      pu₂ pg₂ qg₂ pv₂
      (SPath.eq_of_sides _ _ (by
        simp [m₁, qg₁, pu₂, pg₂, pv₂, SPath.sides_append, SPath.sides_two, SPath.sides]))
      (SPath.eq_of_sides _ _ (by
        simp [m₂, pu₂, qg₂, pv₂, SPath.sides_append, SPath.sides, SPath.sides_castTgt]))
      pu₃ pg₃ (SPath.nil s₀) (SPath.nil s₀)
      (SPath.eq_of_sides _ _ (by
        simp [m₂, pu₂, qg₂, pv₂, pu₃, pg₃, sd, SPath.sides_append, SPath.sides_two, SPath.sides,
          SPath.sides_castTgt]))
      (SPath.eq_of_sides _ _ (by simp [pu₃, sd, SPath.sides_append, SPath.sides_two, SPath.sides]))]
  simp only [upwardGens, Generators.image, sigL₁, sigL₂, sigL₃, SKM.lay, crossImage,
    dite_eq_right hij, cupImage, capImage]
  have hcross : ∀ W, P.twoTwo _ _ _ _ (P.crossNeEntry i j _ _ _ _) pg₂ qg₂ rfl W =
      (P.mixedJ i j t' hv₁ W).hom := fun W => rfl
  erw [hcross]
  simp only [qg₁, pg₃]
  rw [zeroTwo_two (Z' := (nextSector_up_dn hw₁).symm ▸ _) (hZ := eqRec_heq _ _)]
  rw [twoZero_two (Z' := (nextSector_dn_up s₀).symm ▸ _) (hZ := eqRec_heq _ _)]
  simp only [cupEntry, capEntry, preCup, preCap]
  simp only [pu₂, pu₃, pathFunctor_cons, pathFunctor_nil, Functor.comp_map, Functor.id_map]
  simp only [Category.assoc]
  apply isIso_probeMixedMateNe i j hw₁ hv₁ hw₂
  · refine (eqRec_heq _ _).trans ?_
    refine (eqRec_heq _ _).trans ?_
    exact pathFunctor_two_obj_heq (nextSector_up_dn hw₁).symm false true hv₁ hv₂ ep hv₁ pv₂
      (congrArg (List.cons true) (SPath.sides_castTgt _ _)) Z
  · exact pathFunctor_one_obj_heq (nextSector_resUp_probeUp t') true pv₂
      (congrArg (List.cons true) (SPath.sides_castTgt _ _))
      hd Z ((eqRec_heq _ _).trans (pathFunctor_obj_heq_of_nil _ Z))

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
