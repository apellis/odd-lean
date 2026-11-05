/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.GroundRingNondegeneracy
import OddMath.SKM.IntegralParameters
import OddMath.SKM.ScalarChangeIntegral

/-!
# Nondegeneracy of the integral form

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, the Nondegeneracy Conjecture
of §8, for the integral form of the presentation (the relations of Definition 1.5 together with
the integral relations `zInt`, which are imposed exactly when `2` is not a unit), over every
commutative ring, without any condition on `2`.

The deduction is from the conjecture over the universal parameter ring with `2` inverted:

1. `integralUniversal`: the coefficient map `toHalf` from the integral universal parameter ring
   (over `ℤ`) to the universal parameter ring over `ℤ[1/2]` is injective, and the decorated
   matching expansions commute with it (`ScalarChange.homMap_expansion`, using that the integral
   relations are transported, `ScalarChange.ZTransport.of_cScalars`). So injectivity of the
   expansion over `ℤ[1/2]` gives injectivity over `ℤ`.
2. `of_integralUniversal`: every homogeneous scalar system over a commutative ring `k` is a
   specialization of the integral universal one (`IntegralParameters.specialize`), and the
   conjecture is stable under coefficient change (`nondegeneracyConjecture_scalarChange`).

## Main results

* `nondegeneracyConjecture_of_universal`: the conjecture over the universal parameter ring with
  `2` inverted implies the conjecture for every commutative ring `k`, every homogeneous scalar
  system `Sc` without a condition on `2` and every `cs : CScalars Sc`.
-/

noncomputable section

namespace OddMath.SKM.IntegralNondegeneracy

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}

/-- The conjecture over the universal parameter ring with `2` inverted implies the conjecture over
the integral universal parameter ring. -/
theorem integralUniversal
    (h : NondegeneracyConjecture (UniversalPolynomialParameters.normalizations D)) :
    NondegeneracyConjecture (IntegralParameters.normalizations D) := by
  have := ScalarChange.ZTransport.of_cScalars (IntegralParameters.toHalf D)
    (IntegralParameters.normalizations D)
  have h' : NondegeneracyConjecture
      (ScalarChange.cScalars D (IntegralParameters.toHalf D)
        (IntegralParameters.normalizations D)) := by
    refine nondegeneracyConjecture_congr (eq_true (UniversalPolynomialParameters.two_isUnit D))
      ?_ ?_ _ _ ?_ h
    · funext i j
      exact (IntegralParameters.toHalf_t D i j).symm
    · funext i j p q
      exact (IntegralParameters.toHalf_coefficient D ⟨i, j, p, q⟩).symm
    · intro μ i
      exact (IntegralParameters.toHalf_c D μ i).symm
  rw [nondegeneracyConjecture_iff_injective]
  intro a b hab μ F
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hinj := (nondegeneracyConjecture_iff_injective _).1 h' a b hab μ F
  have hz' : Finsupp.mapRange.addMonoidHom
      (ScalarChange.symMap (D := D) (IntegralParameters.toHalf D)).toAddMonoidHom z = 0 := by
    apply hinj
    rw [← ScalarChange.homMap_expansion, hz, map_zero, map_zero]
  ext t
  apply ScalarChange.eq_zero_of_symMap_eq_zero (fun _ : Unit => IntegralParameters.toHalf D)
    (fun r hr => IntegralParameters.toHalf_injective D (by simpa using hr ())) (z t)
  intro _
  simpa using congrArg (fun y => y t) hz'

/-- The conjecture over the integral universal parameter ring implies the conjecture for every
homogeneous scalar system over every commutative ring. -/
theorem of_integralUniversal (h : NondegeneracyConjecture (IntegralParameters.normalizations D))
    {k : Type w} [CommRing k] {Sc : IntegralScalars D k} (hh : Sc.Homogeneous)
    (cs : CScalars Sc) : NondegeneracyConjecture cs := by
  have := ScalarChange.ZTransport.of_cScalars (IntegralParameters.specialize cs)
    (IntegralParameters.normalizations D)
  have hU := nondegeneracyConjecture_scalarChange (IntegralParameters.specialize cs) h
  refine nondegeneracyConjecture_congr rfl ?_ ?_ _ cs ?_ hU
  · funext i j
    exact IntegralParameters.specialize_t cs i j
  · funext i j p q
    exact IntegralParameters.specialize_coefficient cs hh ⟨i, j, p, q⟩
  · intro μ i
    exact IntegralParameters.specialize_c cs μ i

/-- **Nondegeneracy of the integral form.** The conjecture over the universal parameter ring with
`2` inverted implies the conjecture for every commutative ring `k`, every homogeneous scalar
system over `k` and every normalization; `2` need not be invertible in `k`. -/
theorem nondegeneracyConjecture_of_universal
    (h : NondegeneracyConjecture (UniversalPolynomialParameters.normalizations D))
    {k : Type w} [CommRing k] {Sc : IntegralScalars D k} (hh : Sc.Homogeneous)
    (cs : CScalars Sc) : NondegeneracyConjecture cs :=
  of_integralUniversal (integralUniversal h) hh cs

end OddMath.SKM.IntegralNondegeneracy
