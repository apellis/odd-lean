/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Action
import OddMath.QuiverHecke.SwappedVacuumAdjunctionBubbles
import OddMath.QuiverHecke.SwappedVacuumCornerEvaluation
import OddMath.QuiverHecke.FiniteColourNondegeneracy

/-!
# The Nondegeneracy Conjecture from swapped vacuum observations (conditional)

Research issue #345, toward the Nondegeneracy Conjecture of Brundan–Ellis,
*Super Kac–Moody 2-categories* (arXiv:1701.04133v2), §8. This file composes the
conditional pieces of the written proof `docs/Nondegeneracy/SwappedNondegeneracy.md`
(§§3–5) into one statement whose hypotheses are exactly the interfaces that are not yet
constructed in Lean.

A `SwappedVacuumObservation` at external weight `μ`, upward words `t, t'` and degree bound
`d` consists of

* a probe/reservoir pair `P : ProbeReservoir k B D Sc` in a fixed target 2-supercategory `B`
  (the factor actions F1–F2 of `SwappedActionAssembly.md` §1: Rouquier families with their
  multicolour relations and the probe's shifted left adjunctions);
* a crossing coefficient `c`, leftward data `L` and the entrywise relation identities
  `SwappedRelationData c L` for the swapped generators (`SwappedActionAssembly.md` §§3–5);
  together with objects `Gs`, `Ys` these give the swapped upward module action `A` at `μ`
  (`SwappedRelationData.upwardModuleAction`);
* a vacuum vector and the raw reservoir coefficient action on the source sector `A.V t`;
* the left-bubble series of the `homContent` adjunctions at the schedule of
  `SwappedNondegeneracy.md` §2 (`AdjunctionBubbleSeries`, probe exponents `probeExponent`,
  reservoir levels `reservoirLevel`);
* a corner evaluation of `A` at the source word (`VacuumCornerEvaluation`: the generator
  square and the vacuum value of `SwappedVacuumCoordinates.md` §§2–5);
* the weight bound of `SwappedVacuumCoordinates.md` §6 on the transformed ideal at `t'`.

Everything between these inputs and the conjecture is proved:

* `SwappedVacuumObservation.toSwappedVacuumBlock`: the moments (A16) come from the bubble
  series by the infinite Grassmannian relations (`AdjunctionBubbleSeries.vacuumMoments`), and
  (A18) from the corner evaluation (`SwappedVacuumBlock.ofCornerEvaluation`);
* `nondegeneracy_of_swapped_vacuum_observations`: observations at every equal-weight upward
  word pair, external weight and degree bound give the conjecture over a field
  (`nondegeneracy_of_vacuum_blocks`, hence `upward_independence_of_coefficientMap` and
  `SKM.nondegeneracy_of_upward_independence`);
* `nondegeneracy_of_restrictColours_swapped_vacuum_observations`: the same with observations
  only for the restrictions of `D` to finite sets of colours (`SwappedNondegeneracy.md` §5,
  finite witnesses), for an arbitrary colour set.

These theorems are **conditional**: the observations are hypotheses. In particular the factor
interface `CyclotomicAction.GlobalLocalInversion` (KKO local inversion for the cyclotomic
weight-space factors) does not appear: the cyclotomic action target lives in a higher universe
than the one `ProbeReservoir` requires, so `CyclotomicAction.globalRouquierFamily` cannot yet
be used as the probe or reservoir of a `ProbeReservoir`. The probe and reservoir families are
therefore part of the observation.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SwappedAssembly
universe u

section Observation
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (B : Type u) [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

/-- **A swapped vacuum observation** at external weight `μ`, upward words `t, t'` and degree
bound `d`, in the target 2-supercategory `B`: the swapped action built from a probe/reservoir
pair and the entrywise relation identities of its generators, with a vacuum, a raw reservoir
coefficient action, the left-bubble series at the schedule of `SwappedNondegeneracy.md` §2, a
corner evaluation at the source word and the weight bound on its ideal at the target word.
Each field other than the bookkeeping is an open obligation of the written proof. -/
structure SwappedVacuumObservation (μ : X) (t t' : List I) (d : ℕ) where
  /-- The probe and reservoir factors. -/
  P : ProbeReservoir k B D Sc
  /-- The same-colour mixed crossing coefficient. -/
  c : P.CrossCoeff
  /-- The leftward generator images (A7). -/
  L : P.LeftwardData
  /-- The entrywise identities of the swapped generators. -/
  relations : P.SwappedRelationData c L
  /-- The left objects of the Hom sectors. -/
  Gs : ∀ s, P.H s
  /-- The right objects of the Hom sectors. -/
  Ys : ∀ s, P.H s
  /-- The vacuum vector of the source sector. -/
  vacuum : (relations.upwardModuleAction Gs Ys μ).V t
  /-- The raw action of the reservoir coefficients on the source sector. -/
  raw : SKM.SYM D k →ₐ[k] Module.End k ((relations.upwardModuleAction Gs Ys μ).V t)
  /-- The left-bubble series of the adjunctions at the schedule. -/
  bubbles : AdjunctionBubbleSeries cs (relations.upwardModuleAction Gs Ys μ) t raw
    (probeExponent D μ t d) (reservoirLevel D μ t d)
  /-- The corner evaluation at the source word. -/
  corner : VacuumCornerEvaluation D Sc (relations.upwardModuleAction Gs Ys μ) t raw vacuum
  /-- The weight bound `N₀ - 2·C(|t|, 2)` on the transformed ideal at the target word. -/
  ideal_le : corner.K t' ≤ ExtendedAtLeast D Sc t t'
    ((vacuumCutoff t d : ℤ) - 2 * t.length.choose 2)

variable {B D Sc cs}

/-- The swapped upward module action of an observation. -/
abbrev SwappedVacuumObservation.action {μ : X} {t t' : List I} {d : ℕ}
    (O : SwappedVacuumObservation B D Sc cs μ t t' d) : UpwardModuleAction D Sc μ :=
  O.relations.upwardModuleAction O.Gs O.Ys μ

/-- **A swapped vacuum observation is a vacuum block**: (A16) from the bubble series and
(A18) from the corner evaluation. -/
def SwappedVacuumObservation.toSwappedVacuumBlock {μ : X} {t t' : List I} {d : ℕ}
    (O : SwappedVacuumObservation B D Sc cs μ t t' d) : SwappedVacuumBlock D Sc cs μ t t' d :=
  SwappedVacuumBlock.ofCornerEvaluation cs O.action O.vacuum O.raw O.bubbles.vacuumMoments
    O.corner O.ideal_le

/-- The vacuum block of an observation acts through the swapped action. -/
theorem SwappedVacuumObservation.toSwappedVacuumBlock_A {μ : X} {t t' : List I} {d : ℕ}
    (O : SwappedVacuumObservation B D Sc cs μ t t' d) : O.toSwappedVacuumBlock.A = O.action :=
  rfl

end Observation

section Field
variable {I X k : Type u} [AddCommGroup X] [Field k]
  (B : Type u) [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

/-- **Conditional field theorem from swapped vacuum observations.** If at every
equal-weight pair of upward words, every external weight `μ` and every degree bound `d` there
is a swapped vacuum observation in `B`, then the Nondegeneracy Conjecture holds for `cs`.
The observations are hypotheses; see the module docstring for the list of open inputs. -/
theorem nondegeneracy_of_swapped_vacuum_observations
    (h : ∀ (t t' : List I), SKM.wt D 0 (SKM.ups t) = SKM.wt D 0 (SKM.ups t') →
      ∀ (μ : X) (d : ℕ), Nonempty (SwappedVacuumObservation B D Sc cs μ t t' d)) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_vacuum_blocks D Sc cs fun t t' hw μ d =>
    (h t t' hw μ d).map SwappedVacuumObservation.toSwappedVacuumBlock

/-- **Conditional field theorem, finite-colour form.** For an arbitrary colour set, swapped
vacuum observations in `B` for every restriction of `D` to a finite set of colours, at every
equal-weight upward word pair, external weight and degree bound, give the Nondegeneracy
Conjecture for `D` (`SwappedNondegeneracy.md` §5). The observations are hypotheses. -/
theorem nondegeneracy_of_restrictColours_swapped_vacuum_observations
    (h : ∀ (J : Finset I) (tJ t'J : List J),
      SKM.wt (D.restrictColours J) 0 (SKM.ups tJ) =
        SKM.wt (D.restrictColours J) 0 (SKM.ups t'J) →
      ∀ (μ : X) (d : ℕ), Nonempty (SwappedVacuumObservation B (D.restrictColours J)
        (Sc.restrictColours D J) (cs.restrictColours D J Sc) μ tJ t'J d)) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_restrictColours_vacuum_evaluations D Sc cs fun J tJ t'J hw μ d =>
    (h J tJ t'J hw μ d).map fun O => O.toSwappedVacuumBlock.toSwappedVacuumEvaluation

end Field

end OddMath.QuiverHecke
