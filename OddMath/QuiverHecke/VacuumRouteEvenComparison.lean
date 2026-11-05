/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteNondegeneracy
import OddMath.SKM.EvenBridge.EvenNondegeneracy

/-!
# The vacuum route on purely even data

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture after Theorem 8.1. This file records the all-even comparison of the
research completion criterion (`docs/Nondegeneracy/FieldScopeBoundary.md`): on purely even data
the conclusion of the vacuum route end theorem `nondegeneracy_of_vacuum_route` is the ordinary
even nondegeneracy theorem.

## The comparison, stated exactly

Let `D` be a purely even datum (`IsEven D`) with finitely many colours, compatible with a
symmetric Cartan datum `C`, and let `Sc` be Khovanov–Lauda scalars (`IsKLScalars`) over a
commutative ring `k`.

* **Scope.** These data lie in the scope of `nondegeneracy_of_vacuum_route`: `D` carries the
  symmetrizer `EvenBridge.symmetrizer D C hc` (`dᵢ = (i·i)/2`), and Khovanov–Lauda scalars are
  homogeneous (`isKLScalars_homogeneous`, since all `sᵢⱼ^{pq}` vanish). When `2` is a unit of
  `k`, every premise of the end theorem except the route hypotheses is therefore met
  (`vacuumRouteScope_of_isEven`).
* **Conclusion.** The end theorem and the even theorem
  `EvenBridge.nondegeneracyConjecture_of_isEven` have literally the same conclusion,
  `SKM.NondegeneracyConjecture cs`: the decorated reduced matchings of Theorem 8.1 form a basis
  of `HOM(E_a 1_μ, E_b 1_μ)` over the bubble algebra. On these data that conclusion holds with no
  route hypothesis and over every commutative ring, without invertibility of `2`
  (`vacuumRoute_conclusion_of_isEven`), via Khovanov–Lauda's nondegeneracy (KL III Theorem 1.2).
  So the odd route, once its hypotheses are discharged, specializes on even data to exactly the
  even basis theorem (same presentation, normalizations, decorated matchings and bubble algebra),
  except that the end theorem additionally assumes `2` is a unit.
* **What is not claimed.** The even theorem does not discharge `VacuumRouteHypotheses D sy` on
  even data. Those hypotheses concern the swapped vacuum action on the pairing extension of each
  finite-colour restriction (route sectors, bubble identities, coordinates and chart
  coherence), which the even nondegeneracy statement does not mention; deriving them from it
  would be a separate argument. The comparison is at the level of the conclusion, as the
  completion criterion requires.
-/

noncomputable section

namespace OddMath.QuiverHecke

open OddMath.SKM OddMath.SKM.EvenBridge

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : SKM.Datum I X}
  {k : Type w} [CommRing k] {Sc : SKM.Scalars D k}

/-- Khovanov–Lauda scalars are homogeneous: every `sᵢⱼ^{pq}` vanishes, so the homogeneity
condition (`SKM.ScalarData.Homogeneous`, Brundan–Ellis (1.31)) holds vacuously. -/
theorem isKLScalars_homogeneous (hS : IsKLScalars D k Sc) : Sc.Homogeneous :=
  fun i j p q _ _ _ _ hs => (hs (hS.2 i j p q)).elim

/-- **Even data lie in the vacuum route's scope.** A purely even datum compatible with a
symmetric Cartan datum is symmetrizable (by `EvenBridge.symmetrizer`), and Khovanov–Lauda
scalars are homogeneous: these are the premises of `nondegeneracy_of_vacuum_route` other than
the route hypotheses and the unit `2`. -/
theorem vacuumRouteScope_of_isEven (C : Categorification.QuantumGroup.CartanDatum I)
    (hc : Compatible D C) (hS : IsKLScalars D k Sc) :
    Nonempty (SKM.Symmetrizer D) ∧ Sc.Homogeneous :=
  ⟨⟨symmetrizer D C hc⟩, isKLScalars_homogeneous hS⟩

/-- **The all-even comparison for the vacuum route.** On purely even data with Khovanov–Lauda
scalars, a compatible Cartan datum and finitely many colours, the conclusion of
`nondegeneracy_of_vacuum_route` holds over every commutative ring, with no route hypothesis and
no unit `2`: it is the even nondegeneracy theorem `EvenBridge.nondegeneracyConjecture_of_isEven`
(Brundan–Ellis, arXiv:1701.04133v2, §8, via Khovanov–Lauda, arXiv:0807.3250v1, Theorem 1.2).
This compares conclusions only; it does not discharge `VacuumRouteHypotheses`. -/
theorem vacuumRoute_conclusion_of_isEven [Finite I]
    (C : Categorification.QuantumGroup.CartanDatum I) (hc : Compatible D C) (hD : IsEven D)
    (hS : IsKLScalars D k Sc) (cs : SKM.CScalars Sc) : SKM.NondegeneracyConjecture cs :=
  nondegeneracyConjecture_of_isEven C hc hD hS cs

/-- On even Khovanov–Lauda data with `2` a unit, the vacuum route end theorem and the even
theorem prove the same proposition: the end theorem applies (its non-route premises hold by
`vacuumRouteScope_of_isEven`), and its conclusion is the even theorem's. -/
theorem nondegeneracy_of_vacuum_route_of_isEven {X : Type u} [AddCommGroup X]
    {D : SKM.Datum I X} {Sc : SKM.Scalars D k} (C : Categorification.QuantumGroup.CartanDatum I)
    (hc : Compatible D C) (hS : IsKLScalars D k Sc)
    (H : VacuumRouteHypotheses D (symmetrizer D C hc)) (h₂ : IsUnit (2 : k))
    (cs : SKM.CScalars Sc) : SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_vacuum_route H h₂ (isKLScalars_homogeneous hS) cs

end OddMath.QuiverHecke
