/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ParameterTransport
import OddMath.SKM.BWWPureNilpotent

/-!
# The parity transport of parameters keeps the pure coefficients nilpotent

`parameterTwist` multiplies each coefficient `sᵢⱼ(p, q)` by a sign, so pure coefficients lying
in a nilpotent ideal stay in it. The instance lets `ScalarData.PureNilpotent`, a hypothesis of
the probe unit arguments for parameters with pure terms, pass to the transported parameters.
-/

namespace OddMath.QuiverHecke

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

theorem parameterTwist_pureNilpotent (hP : Sc.PureNilpotent) :
    (parameterTwist D Sc).PureNilpotent := by
  obtain ⟨J, N, hJ, hpure⟩ := hP
  refine ⟨J, N, hJ, ?_⟩
  intro i j p hij hp
  have hji : D.dn j i ≠ 0 := fun h =>
    absurd ((SKM.ScalarData.dn_eq_zero_iff (D := D) i j).mpr h) (by omega)
  have h := hpure i j p hij hp
  rw [SKM.ScalarData.toBWW_c_of_lt _ hij hp (Nat.pos_of_ne_zero hji)] at h ⊢
  exact J.mul_mem_left _ h

instance parameterTwist_pureNilpotent_fact [hP : Fact Sc.PureNilpotent] :
    Fact (parameterTwist D Sc).PureNilpotent :=
  ⟨parameterTwist_pureNilpotent D Sc hP.out⟩

end OddMath.QuiverHecke
