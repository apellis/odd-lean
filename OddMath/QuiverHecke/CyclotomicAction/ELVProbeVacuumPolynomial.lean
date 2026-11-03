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

/-- The same relation holds as an endomorphism of the entire induced
supermodule, before choosing a target word or Hom coordinate. -/
theorem probeOrdinaryVacuumModuleDot_odd (i : I) (hi : D.parity i = 1)
    (M : Superfunctor k
      (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) []) (SVec k)) :
    let x : End (ELVOld.BalancedInduction.induced (probeOrdinaryAppend D Sc m [] i) M) :=
      ELVOld.BalancedInduction.transformComponent
        (probeOrdinaryAppendDot_supernatural D Sc m [] i) M
    (x ^ 2 + 1) ^ m i = 0 := by
  dsimp only
  apply ELVOld.BalancedInduction.end_eq_zero_of_total
  intro w
  let P := ELVOld.BalancedInduction.induced (probeOrdinaryAppend D Sc m [] i) M
  let x : End P := ELVOld.BalancedInduction.transformComponent
    (probeOrdinaryAppendDot_supernatural D Sc m [] i) M
  have hx : x.total w = ELVOld.BalancedInduction.transformLinear
      (probeOrdinaryAppendDot_supernatural D Sc m [] i) M w := by
    simp only [x, SuperNatTrans.total, ELVOld.BalancedInduction.transformComponent_app,
      hi, zero_ne_one, ↓reduceIte, zero_add]
  change ((x ^ 2 + 1) ^ m i).total w = 0
  rw [ELVOld.BalancedInduction.end_total_pow]
  have hs : (x ^ 2 + 1).total w = (x ^ 2).total w + (1 : End P).total w := by
    change ((x ^ 2).app 0 w + (1 : End P).app 0 w) +
      ((x ^ 2).app 1 w + (1 : End P).app 1 w) =
      ((x ^ 2).app 0 w + (x ^ 2).app 1 w) +
        ((1 : End P).app 0 w + (1 : End P).app 1 w)
    abel
  have h1 : (1 : End P).total w = (1 : End (P.obj w)) := SuperNatTrans.id_total _ _
  rw [hs, ELVOld.BalancedInduction.end_total_pow, h1, hx]
  exact probeOrdinaryVacuumInductionDot_odd D Sc m i hi M w

private theorem oddProbeDegree (n : ℕ) :
    ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ n).natDegree ≤ 2 * n := by
  have hb : (Polynomial.X ^ 2 + 1 : Polynomial k).natDegree ≤ 2 := by
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (Polynomial.natDegree_X_pow_le 2) (by simp))
  calc
    _ ≤ n * (Polynomial.X ^ 2 + 1 : Polynomial k).natDegree := Polynomial.natDegree_pow_le
    _ ≤ n * 2 := Nat.mul_le_mul_left n hb
    _ = 2 * n := Nat.mul_comm _ _

private theorem capPolynomial_eq_aeval {C : Type v} [Category.{u} C] [Preadditive C] [Linear k C]
    {V : C} (x : End V) (g : Polynomial k) (P : ℕ) (hP : g.natDegree ≤ P) :
    SwappedVacuum.capPolynomial g.coeff P x = Polynomial.aeval x g := by
  exact (Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hP) x).symm

/-- The concrete annihilator in precisely the finite coefficient format consumed
by the principal and negative inverse-cap theorems. -/
theorem probeOrdinaryVacuumInductionDot_capPolynomial (i : I) (hi : D.parity i = 1)
    (M : Superfunctor k
      (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) []) (SVec k))
    (w : OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) [i]) :
    SwappedVacuum.capPolynomial ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).coeff (2 * m i)
      (show End (ELVOld.BalancedInduction.superspace
        (probeOrdinaryAppend D Sc m [] i) M.toFunctor w) from
          ELVOld.BalancedInduction.transformLinear
            (probeOrdinaryAppendDot_supernatural D Sc m [] i) M w) = 0 := by
  rw [capPolynomial_eq_aeval _ _ _ (oddProbeDegree (k := k) (m i))]
  simp only [map_pow, map_add, Polynomial.aeval_X, map_one]
  exact probeOrdinaryVacuumInductionDot_odd D Sc m i hi M w

/-- On the literal Hom block out of the induced probe object, ordinary
precomposition retains the same plus-one annihilator. -/
theorem probeOrdinaryVacuumHomDot_odd (i : I) (hi : D.parity i = 1)
    (M : Superfunctor k
      (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) []) (SVec k))
    (w : OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) [i])
    (Y : SVec k) :
    ((Linear.leftComp k Y (show End (ELVOld.BalancedInduction.superspace
        (probeOrdinaryAppend D Sc m [] i) M.toFunctor w) from
          ELVOld.BalancedInduction.transformLinear
            (probeOrdinaryAppendDot_supernatural D Sc m [] i) M w)) ^ 2 + 1) ^ m i = 0 := by
  apply ELVOld.BalancedInduction.precompose_odd_probe_polynomial
  exact probeOrdinaryVacuumInductionDot_odd D Sc m i hi M w

/-- The literal vacuum-probe Hom operator satisfies the exact finite
coefficient annihilator required by the inverse-cap recovery library. -/
theorem probeOrdinaryVacuumHomDot_capPolynomial (i : I) (hi : D.parity i = 1)
    (M : Superfunctor k
      (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) []) (SVec k))
    (w : OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) [i])
    (Y : SVec k) :
    let V := ELVOld.BalancedInduction.superspace (probeOrdinaryAppend D Sc m [] i) M.toFunctor w
    let x : End V := ELVOld.BalancedInduction.transformLinear
      (probeOrdinaryAppendDot_supernatural D Sc m [] i) M w
    SwappedVacuum.capPolynomial ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).coeff (2 * m i)
      (show End (ModuleCat.of k (V ⟶ Y)) from ModuleCat.ofHom (Linear.leftComp k Y x)) = 0 := by
  dsimp only
  rw [capPolynomial_eq_aeval _ _ _ (oddProbeDegree (k := k) (m i))]
  simp only [map_pow, map_add, Polynomial.aeval_X, map_one]
  apply (ModuleCat.endRingEquiv _).injective
  simp only [map_pow, map_add, map_one, map_zero]
  exact probeOrdinaryVacuumHomDot_odd D Sc m i hi M w Y

/-- The chosen parity-shift functor preserves the polynomial on its prescribed
image of the probe dot. Its odd-map sign is retained by the functor itself. -/
theorem probeOrdinaryVacuumParityDot_odd (i : I) (hi : D.parity i = 1)
    (M : Superfunctor k
      (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) []) (SVec k))
    (w : OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) [i]) :
    let V := ELVOld.BalancedInduction.superspace (probeOrdinaryAppend D Sc m [] i) M.toFunctor w
    let x : End V := ELVOld.BalancedInduction.transformLinear
      (probeOrdinaryAppendDot_supernatural D Sc m [] i) M w
    (((PiSupercategory.pi (R := k)).mapEnd V x) ^ 2 + 1) ^ m i = 0 := by
  dsimp only
  apply ELVOld.BalancedInduction.additiveFunctor_odd_probe_polynomial
  exact probeOrdinaryVacuumInductionDot_odd D Sc m i hi M w

/-- The actual supernatural Hom block out of the induced vacuum probe,
not just the pointwise SVec Hom, supplies the finite hprobe input. -/
theorem probeOrdinaryVacuumModuleHom_capPolynomial (i : I) (hi : D.parity i = 1)
    (M : Superfunctor k
      (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) []) (SVec k))
    (N : Superfunctor k
      (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) [i]) (SVec k)) :
    let P := ELVOld.BalancedInduction.induced (probeOrdinaryAppend D Sc m [] i) M
    let x : End P := ELVOld.BalancedInduction.transformComponent
      (probeOrdinaryAppendDot_supernatural D Sc m [] i) M
    SwappedVacuum.capPolynomial ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).coeff (2 * m i)
      (show End (ModuleCat.of k (P ⟶ N)) from ModuleCat.ofHom (Linear.leftComp k N x)) = 0 := by
  dsimp only
  rw [capPolynomial_eq_aeval _ _ _ (oddProbeDegree (k := k) (m i))]
  simp only [map_pow, map_add, Polynomial.aeval_X, map_one]
  apply (ModuleCat.endRingEquiv _).injective
  simp only [map_pow, map_add, map_one, map_zero]
  apply ELVOld.BalancedInduction.precompose_odd_probe_polynomial
  exact probeOrdinaryVacuumModuleDot_odd D Sc m i hi M

end OddMath.QuiverHecke
