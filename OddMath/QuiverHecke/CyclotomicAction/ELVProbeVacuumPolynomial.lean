import OddMath.QuiverHecke.CyclotomicAction.ELVProbeInductionDotUnit
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionPolynomialSigns
import OddMath.QuiverHecke.SwappedVacuum.InverseCapMoments
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # The signed probe polynomial at vacuum content

The probe numerator used in `SwappedVacuumBubbles.md`, (5), and
`SwappedVacuumNonpositiveBubbles.md`, (8)--(9), comes from the literal
first-dot relation on the one-letter probe block. The source content here
is empty; no same-exponent last-dot assertion at arbitrary content is used.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)

/-- At vacuum append the literal ordinary dot is the first dot, so its
original cyclotomic probe polynomial vanishes. -/
theorem probeOrdinaryVacuumDot_polynomial (i : I)
    (v : OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) []) :
    ((End.of (probeOrdinaryAppendDot D Sc m [] i v)) ^ probeDotExponent D i - 1) ^ m i = 0 := by
  obtain ⟨word, hw⟩ := v
  have hh : word = [] := List.perm_nil.mp hw
  subst word
  let s : Word I (0 + 1) := ⟨[i], rfl⟩
  let a := probePolynomial (k := k) (probeDotExponent D) m
  change (((End.of ((cycHom D Sc a [i] [i]).mkQ (dotE D Sc [i] 0)) :
    End (⟨[i], List.Perm.refl _⟩ : OrdinaryContentCategory D Sc a [i])) ^
      probeDotExponent D i - 1) ^ m i) = 0
  apply ordinaryWordEndCornerMap_injective D Sc a [i] s (List.Perm.refl _)
  rw [map_pow, map_sub, map_pow, map_one, map_zero, ordinaryWordEndCornerMap_mk]
  have h := cyclotomicWordEnd_generator D Sc a s
  simp only [a, s, probePolynomial, map_pow, map_sub, Polynomial.aeval_X, map_one] at h
  change ((cyclotomicWordEnd D Sc a s (dotE D Sc [i] 0) ^ probeDotExponent D i - 1) ^ m i) = 0 at h
  exact h

/-- The signed dot on the actual vacuum-source ordinary probe coend
satisfies the plus-one polynomial at every target and every input module. -/
theorem probeOrdinaryVacuumInductionDot_odd (i : I) (hi : D.parity i = 1)
    (M : Superfunctor k
      (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) []) (SVec k))
    (w : OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) [i]) :
    (ELVOld.BalancedInduction.transformLinear
      (probeOrdinaryAppendDot_supernatural D Sc m [] i) M w ^ 2 + 1) ^ m i = 0 := by
  let J := probeOrdinaryAppend D Sc m [] i
  let a : ∀ v, End (J.obj v) := fun v => probeOrdinaryAppendDot D Sc m [] i v
  have ha : IsSupernatural k (D.parity i) a := probeOrdinaryAppendDot_supernatural D Sc m [] i
  have hn : ∀ v, (a v ^ 2 - 1) ^ m i = 0 := by
    intro v
    have h := probeOrdinaryVacuumDot_polynomial D Sc m i v
    have he : probeDotExponent D i = 2 := by rw [probeDotExponent, ite_eq_left hi]
    rw [he] at h
    exact h
  exact ELVOld.BalancedInduction.transformLinear_odd_probe_polynomial
    (J := J) (a := a) ha hi (m i) hn M w

end OddMath.QuiverHecke
