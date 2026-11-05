/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.FiniteColourUpward
import OddMath.QuiverHecke.SwappedVacuumRecovery

/-!
# The Nondegeneracy Conjecture from its finite-colour case

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5 and the
Nondegeneracy Conjecture (§10). The conjecture for an arbitrary colour set follows from the
upward coefficient injectivity of the finite-colour restrictions `D.restrictColours J`,
`J` a finite set of colours.

## Main results

* `wt_ups_restrictColours`: the weight of an upward word is unchanged by colour inclusion.
* `nondegeneracy_of_restrictColours_upward`: if `upwardCoefficientMap` is injective for every
  finite-colour restriction, at every equal-weight pair of upward words and every external
  weight, the Nondegeneracy Conjecture holds for `D`. Over a commutative ring; no field,
  grading or independence premise.
* `nondegeneracy_of_finiteColour_upward`: the same, with the hypothesis quantified over all
  data with a finite colour set.
* `nondegeneracy_of_restrictColours_vacuum_evaluations`: over a field, vacuum evaluations of
  the swapped action at every finite-colour restriction imply the conjecture for `D`.

The proof composes `upwardCoefficientMap_injective_of_restrictColours` (finite-colour
detection of upward injectivity) with `upward_independence_of_coefficientMap` and
`SKM.nondegeneracy_of_upward_independence`.
-/

namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct

universe u

/-- The weight of an upward word over `D.restrictColours J` is that of its image over `D`. -/
theorem wt_ups_restrictColours {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X)
    (J : Finset I) (μ : X) (t : List J) :
    SKM.wt (D.restrictColours J) μ (SKM.ups t) = SKM.wt D μ (SKM.ups (t.map Subtype.val)) := by
  induction t with
  | nil => rfl
  | cons i t ih =>
    simp only [SKM.ups, List.map_cons, SKM.wt_cons] at ih ⊢
    rw [ih]
    rfl

section CommRing
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

/-- **The Nondegeneracy Conjecture from its finite-colour restrictions.** If the upward
evaluation is injective for every restriction of `D` to a finite set of colours, at every
equal-weight pair of upward words and every external weight, the conjecture holds for `D`. -/
theorem nondegeneracy_of_restrictColours_upward
    (h : ∀ (J : Finset I) (tJ t'J : List J),
      SKM.wt (D.restrictColours J) 0 (SKM.ups tJ) =
        SKM.wt (D.restrictColours J) 0 (SKM.ups t'J) →
      ∀ μ : X, Function.Injective (upwardCoefficientMap (D.restrictColours J)
        (Sc.restrictColours D J) (cs.restrictColours D J Sc) μ tJ t'J)) :
    SKM.NondegeneracyConjecture cs := by
  apply SKM.nondegeneracy_of_upward_independence cs
  apply upward_independence_of_coefficientMap D Sc cs
  intro t t' hw μ
  apply upwardCoefficientMap_injective_of_restrictColours D Sc cs μ t t'
  rintro J tJ t'J rfl rfl
  refine h J tJ t'J ?_ μ
  rw [wt_ups_restrictColours, wt_ups_restrictColours]
  exact hw

/-- **Finite-colour reduction.** Upward coefficient injectivity for every datum with a
finite colour set (on the same weight lattice and ground ring) implies the Nondegeneracy
Conjecture for every datum. -/
theorem nondegeneracy_of_finiteColour_upward
    (h : ∀ (J : Type u) [Finite J] (D' : SKM.Datum J X) (Sc' : SKM.Scalars D' k)
      (cs' : SKM.CScalars Sc') (t t' : List J),
      SKM.wt D' 0 (SKM.ups t) = SKM.wt D' 0 (SKM.ups t') →
      ∀ μ : X, Function.Injective (upwardCoefficientMap D' Sc' cs' μ t t')) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_restrictColours_upward D Sc cs fun J tJ t'J hw μ =>
    h J (D.restrictColours J) (Sc.restrictColours D J) (cs.restrictColours D J Sc) tJ t'J hw μ

end CommRing

section Field
variable {I X k : Type u} [AddCommGroup X] [Field k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

/-- **Conditional field theorem, finite-colour form.** Over a field, vacuum evaluations of the
swapped action at every finite-colour restriction of `D`, every equal-weight pair of upward
words, every external weight and every degree bound imply the Nondegeneracy Conjecture for
`D`. -/
theorem nondegeneracy_of_restrictColours_vacuum_evaluations
    (h : ∀ (J : Finset I) (tJ t'J : List J),
      SKM.wt (D.restrictColours J) 0 (SKM.ups tJ) =
        SKM.wt (D.restrictColours J) 0 (SKM.ups t'J) →
      ∀ (μ : X) (d : ℕ), Nonempty (SwappedVacuumEvaluation (D.restrictColours J)
        (Sc.restrictColours D J) (cs.restrictColours D J Sc) μ tJ t'J d)) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_restrictColours_upward D Sc cs fun J tJ t'J hw μ =>
    upwardCoefficientMap_injective_of_vacuum_evaluations μ tJ t'J (h J tJ t'J hw μ)

end Field

end OddMath.QuiverHecke
