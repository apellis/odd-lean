/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.GradedParameters
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Universal lower-degree parameters

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §1, (1.5),
(1.6), and the Nondegeneracy Conjecture of §8, for inhomogeneous parameters; J. Brundan,
W. Wang, B. Webster, arXiv:2505.22929v2, Theorem 5.6, proof (reduction to a generic graded
parameter ring).

The universal ring of lower-degree parameters is the polynomial ring over the universal
normalization ring `UniversalCoefficientRing.UnitRing D` on one variable for each coefficient
position allowed by the parity conditions of `Scalars` and, inside the used rectangle
`0 < p < dᵢⱼ`, `0 < q < dⱼᵢ`, by nonnegativity of the coefficient degree (positions are taken
modulo `(i, j, p, q) ↦ (j, i, q, p)`). Giving each variable its coefficient degree makes it an
`ℕ`-graded ring on which the universal parameters are graded homogeneous.

## Main results

* `LowerDegreeParameters.nondegeneracyConjecture_of_universal`: the conjecture for the
  universal lower-degree parameters implies it for every lower-degree parameter system over
  every commutative ring in which `2` is invertible.
* `LowerDegreeParameters.gradedCoefficientNondegeneracy_iff`: the graded-coefficient
  statement `GradedCoefficientNondegeneracy D sy` is equivalent to the single universal
  instance.
* `LowerDegreeParameters.universal_nondegeneracy`: the universal instance follows from the
  case of characteristic-zero fields (`CharZeroFieldLowerDegreeNondegeneracy`), by joint
  detection through the prime fraction fields of the rationalized universal ring, as in the
  homogeneous ground-ring descent.
* `gradedCoefficientNondegeneracy_of_charZeroField`: hence the graded-coefficient statement
  follows from lower-degree nondegeneracy over characteristic-zero fields.
-/

noncomputable section

namespace OddMath.SKM

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}

/-- Graded-homogeneous parameters are lower-degree parameters. -/
theorem Scalars.GradedHomogeneous.lowerDegree {k : Type w} [CommRing k] {σ : Type*}
    [SetLike σ k] {sy : Symmetrizer D} {𝒜 : ℕ → σ} {Sc : Scalars D k}
    (h : Sc.GradedHomogeneous sy 𝒜) : Sc.LowerDegree sy := by
  intro i j p q hp hp' hq hq' hs
  obtain ⟨n, hn, -⟩ := h.2 i j p q hp hp' hq hq' hs
  rw [← hn]
  exact Int.natCast_nonneg n

/-- Lower-degree parameters stay lower-degree under every ring map. -/
theorem ScalarData.LowerDegree.scalarChange {R : Type w} {S : Type*} [CommRing R]
    [CommRing S] (f : R →+* S) {sy : Symmetrizer D} {Ptwo : Prop} {Sc : ScalarData D R Ptwo}
    (h : Sc.LowerDegree sy) :
    (ScalarChange.scalars D f Sc).LowerDegree sy := by
  intro i j p q hp hp' hq hq' hs
  apply h i j p q hp hp' hq hq'
  intro h0
  apply hs
  simp [h0]

namespace LowerDegreeParameters

open UniversalPolynomialParameters (RawSlot RawSlot.swap)

variable (D) (sy : Symmetrizer D)

/-- Parity conditions everywhere, and a nonnegative coefficient degree in the used
rectangle. -/
def Allowed (a : RawSlot I) : Prop :=
  (a.p : ZMod 2) * D.parity a.i ≠ 1 ∧
  (a.q : ZMod 2) * D.parity a.j ≠ 1 ∧
  (0 < a.p → (a.p : ℤ) < D.d a.i a.j → 0 < a.q → (a.q : ℤ) < D.d a.j a.i →
    0 ≤ coefficientDegree sy a.i a.j a.p a.q)

theorem allowed_swap (a : RawSlot I) (h : Allowed D sy a) : Allowed D sy a.swap := by
  refine ⟨h.2.1, h.1, ?_⟩
  intro hq hq' hp hp'
  have h' := h.2.2 hp hp' hq hq'
  rw [coefficientDegree_symm] at h'
  exact h'

/-- Allowed positions modulo the swap involution. -/
def Slot := Quot (fun a b : {a : RawSlot I // Allowed D sy a} => b.val = a.val.swap)

/-- The class of an allowed position. -/
def slot (a : RawSlot I) (h : Allowed D sy a) : Slot D sy := Quot.mk _ ⟨a, h⟩

theorem slot_swap (a : RawSlot I) (h : Allowed D sy a) :
    slot D sy a h = slot D sy a.swap (allowed_swap D sy a h) := Quot.sound rfl

/-- Fix the canonical ring structure before forming the nested group algebras. -/
local instance halfIntegersCommRing : CommRing UniversalCoefficientRing.HalfIntegers :=
  inferInstance

local instance unitRingCommRing : CommRing (UniversalCoefficientRing.UnitRing D) :=
  inferInstance

/-- The universal lower-degree parameter ring. -/
abbrev ParameterRing := MvPolynomial (Slot D sy) (UniversalCoefficientRing.UnitRing D)

instance parameterRingCommRing : CommRing (ParameterRing D sy) := inferInstance

theorem two_isUnit : IsUnit (2 : ParameterRing D sy) := by
  simpa only [map_ofNat] using (UniversalCoefficientRing.two_isUnit D).map
    (MvPolynomial.C : UniversalCoefficientRing.UnitRing D →+* ParameterRing D sy)

/-- The universal coefficient, zero at the forbidden positions. -/
def coefficient (a : RawSlot I) : ParameterRing D sy := by
  classical
  exact if h : Allowed D sy a then MvPolynomial.X (slot D sy a h) else 0

theorem coefficient_of_allowed (a : RawSlot I) (h : Allowed D sy a) :
    coefficient D sy a = MvPolynomial.X (slot D sy a h) := by
  classical
  simp [coefficient, h]

theorem coefficient_of_not_allowed (a : RawSlot I) (h : ¬ Allowed D sy a) :
    coefficient D sy a = 0 := by
  classical
  simp [coefficient, h]

theorem coefficient_swap (a : RawSlot I) :
    coefficient D sy a = coefficient D sy a.swap := by
  classical
  by_cases h : Allowed D sy a
  · rw [coefficient_of_allowed D sy a h,
      coefficient_of_allowed D sy a.swap (allowed_swap D sy a h), slot_swap D sy a h]
  · have hs : ¬ Allowed D sy a.swap := fun hs => h (by simpa using allowed_swap D sy a.swap hs)
    rw [coefficient_of_not_allowed D sy a h, coefficient_of_not_allowed D sy a.swap hs]

/-- Universal endpoint units and lower-degree coefficients. -/
def scalars : Scalars D (ParameterRing D sy) where
  t i j := Units.map
    (MvPolynomial.C : UniversalCoefficientRing.UnitRing D →+* ParameterRing D sy).toMonoidHom
    (UniversalCoefficientRing.t D i j)
  t_self i := by simp
  t_symm_of_d_eq_zero i j h := by rw [UniversalCoefficientRing.t_symm D i j h]
  s i j p q := coefficient D sy ⟨i, j, p, q⟩
  s_symm i j p q := coefficient_swap D sy ⟨i, j, p, q⟩
  s_eq_zero i j p q h := coefficient_of_not_allowed D sy _ (fun ha => ha.1 h)
  two_isUnit _ := two_isUnit D sy

theorem lowerDegree : (scalars D sy).LowerDegree sy := by
  intro i j p q hp hp' hq hq' hn
  by_cases h : Allowed D sy ⟨i, j, p, q⟩
  · exact h.2.2 hp hp' hq hq'
  · exact (hn (coefficient_of_not_allowed D sy _ h)).elim

/-- All normalization units, with their shift laws. -/
def normalizations : CScalars (scalars D sy) where
  c μ i := Units.map
    (MvPolynomial.C : UniversalCoefficientRing.UnitRing D →+* ParameterRing D sy).toMonoidHom
    (UniversalCoefficientRing.c D μ i)
  shift μ i j := by simp [UniversalCoefficientRing.c_shift, scalars]

/-! ### The grading by coefficient degree -/

/-- The weight of a slot: its coefficient degree, truncated at zero. -/
def weight : Slot D sy → ℕ :=
  Quot.lift (fun a => (coefficientDegree sy a.val.i a.val.j a.val.p a.val.q).toNat) (by
    intro a b h
    rw [h]
    exact congrArg Int.toNat (coefficientDegree_symm sy _ _ _ _))

/-- The grading of the universal ring by coefficient degree. -/
abbrev grading : ℕ → Submodule (UniversalCoefficientRing.UnitRing D) (ParameterRing D sy) :=
  MvPolynomial.weightedHomogeneousSubmodule _ (weight D sy)

theorem gradedHomogeneous : (scalars D sy).GradedHomogeneous sy (grading D sy) := by
  refine ⟨fun i j => ?_, fun i j p q hp hp' hq hq' hs => ?_⟩
  · exact (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
      (MvPolynomial.isWeightedHomogeneous_C _ _)
  · have h : Allowed D sy ⟨i, j, p, q⟩ := by
      by_contra h
      exact hs (coefficient_of_not_allowed D sy _ h)
    refine ⟨(coefficientDegree sy i j p q).toNat, Int.toNat_of_nonneg (h.2.2 hp hp' hq hq'), ?_⟩
    change coefficient D sy ⟨i, j, p, q⟩ ∈ _
    rw [coefficient_of_allowed D sy _ h]
    exact (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
      (MvPolynomial.isWeightedHomogeneous_X _ (weight D sy) (slot D sy _ h))

/-! ### Specialization -/

variable {R : Type w} [CommRing R] {D}

/-- A nonzero lower-degree coefficient is an allowed position. -/
theorem allowed_of_ne_zero {Sc : Scalars D R} (hl : Sc.LowerDegree sy)
    (a : RawSlot I) (h : Sc.s a.i a.j a.p a.q ≠ 0) : Allowed D sy a := by
  refine ⟨fun hp => h (Sc.s_eq_zero _ _ _ _ hp), ?_, ?_⟩
  · intro hq
    apply h
    rw [Sc.s_symm]
    exact Sc.s_eq_zero _ _ _ _ hq
  · exact fun hp hp' hq hq' => hl _ _ _ _ hp hp' hq hq' h

/-- Evaluation on slots, well defined by the symmetry law. -/
def slotValue (Sc : Scalars D R) : Slot D sy → R :=
  Quot.lift (fun a => Sc.s a.val.i a.val.j a.val.p a.val.q) (by
    intro a b h
    rw [h]
    exact Sc.s_symm _ _ _ _)

/-- Specialize the units and every allowed coefficient. -/
def specialize (h₂ : IsUnit (2 : R)) {Sc : Scalars D R} (cs : CScalars Sc) :
    ParameterRing D sy →+* R :=
  MvPolynomial.eval₂Hom (UniversalCoefficientRing.specialize h₂ cs) (slotValue sy Sc)

@[simp] theorem specialize_C (h₂ : IsUnit (2 : R)) {Sc : Scalars D R}
    (cs : CScalars Sc) (a : UniversalCoefficientRing.UnitRing D) :
    specialize sy h₂ cs (MvPolynomial.C a) = UniversalCoefficientRing.specialize h₂ cs a := by
  simp [specialize]

theorem specialize_coefficient (h₂ : IsUnit (2 : R)) {Sc : Scalars D R}
    (cs : CScalars Sc) (hl : Sc.LowerDegree sy) (a : RawSlot I) :
    specialize sy h₂ cs (coefficient D sy a) = Sc.s a.i a.j a.p a.q := by
  classical
  by_cases h : Allowed D sy a
  · simp [coefficient, h, specialize, slotValue, slot]
  · have hz : Sc.s a.i a.j a.p a.q = 0 := by
      by_contra hn
      exact h (allowed_of_ne_zero sy hl a hn)
    simp [coefficient, h, hz]

theorem specialize_t (h₂ : IsUnit (2 : R)) {Sc : Scalars D R}
    (cs : CScalars Sc) (i j : I) :
    Units.map (specialize sy h₂ cs).toMonoidHom ((scalars D sy).t i j) = Sc.t i j := by
  apply Units.ext
  change specialize sy h₂ cs (MvPolynomial.C (UniversalCoefficientRing.t D i j :
    UniversalCoefficientRing.UnitRing D)) = (Sc.t i j : R)
  rw [specialize_C]
  exact congrArg (fun z : Rˣ => (z : R))
    (UniversalCoefficientRing.specialize_t h₂ cs i j)

theorem specialize_c (h₂ : IsUnit (2 : R)) {Sc : Scalars D R}
    (cs : CScalars Sc) (μ : X) (i : I) :
    Units.map (specialize sy h₂ cs).toMonoidHom ((normalizations D sy).c μ i) = cs.c μ i := by
  apply Units.ext
  change specialize sy h₂ cs (MvPolynomial.C (UniversalCoefficientRing.c D μ i :
    UniversalCoefficientRing.UnitRing D)) = (cs.c μ i : R)
  rw [specialize_C]
  exact congrArg (fun z : Rˣ => (z : R))
    (UniversalCoefficientRing.specialize_c h₂ cs μ i)

/-- **Universality.** The conjecture for the universal lower-degree parameters implies the
conjecture for every lower-degree parameter system over every commutative ring in which `2`
is invertible. -/
theorem nondegeneracyConjecture_of_universal
    (hU : NondegeneracyConjecture (normalizations D sy)) (h₂ : IsUnit (2 : R))
    {Sc : Scalars D R} (hl : Sc.LowerDegree sy) (cs : CScalars Sc) :
    NondegeneracyConjecture cs := by
  have hS := nondegeneracyConjecture_scalarChange (specialize sy h₂ cs) hU
  refine nondegeneracyConjecture_congr (eq_true h₂).symm ?_ ?_ _ cs ?_ hS
  · funext i j
    exact specialize_t sy h₂ cs i j
  · funext i j p q
    exact specialize_coefficient sy h₂ cs hl ⟨i, j, p, q⟩
  · intro μ i
    exact specialize_c sy h₂ cs μ i

variable (D)

/-- **The graded-coefficient statement is one universal instance**: it holds if and only if
the conjecture holds for the universal lower-degree parameters. -/
theorem gradedCoefficientNondegeneracy_iff :
    GradedCoefficientNondegeneracy.{u, v, max u v} D sy ↔
      NondegeneracyConjecture (normalizations D sy) := by
  constructor
  · intro hG
    let _ : GradedRing (grading D sy) := MvPolynomial.weightedGradedAlgebra _ (weight D sy)
    exact hG (ParameterRing D sy)
      (Submodule (UniversalCoefficientRing.UnitRing D) (ParameterRing D sy)) (grading D sy)
      (two_isUnit D sy) (scalars D sy) (gradedHomogeneous D sy) (normalizations D sy)
  · intro hU k _ σ _ _ 𝒜 _ h₂ Sc hSc cs
    exact nondegeneracyConjecture_of_universal sy hU h₂ hSc.lowerDegree cs

/-- The universal instance gives the graded-coefficient statement in every universe. -/
theorem gradedCoefficientNondegeneracy_of_universal
    (hU : NondegeneracyConjecture (normalizations D sy)) :
    GradedCoefficientNondegeneracy.{u, v, w} D sy := by
  intro k _ σ _ _ 𝒜 _ h₂ Sc hSc cs
  exact nondegeneracyConjecture_of_universal sy hU h₂ hSc.lowerDegree cs

/-! ### Reduction to characteristic-zero fields -/

open UniversalCoefficientRationalization in
/-- Rational universal lower-degree parameters. -/
abbrev RationalParameters := MvPolynomial (Slot D sy) (RationalUnitRing D)

/-- The point of a prime fraction field of the rational parameters. -/
def point (p : PrimeSpectrum (RationalParameters D sy)) :
    ParameterRing D sy →+* primeFractionField (RationalParameters D sy) p :=
  (primeFractionMap (RationalParameters D sy) p).comp
    (UniversalCoefficientRationalization.rationalizePolynomial D (Slot D sy))

/-- The prime fraction fields jointly detect zero in the universal ring. -/
theorem point_separate (a : ParameterRing D sy) (h : ∀ p, point D sy p a = 0) : a = 0 := by
  apply UniversalCoefficientRationalization.rationalizePolynomial_injective D (Slot D sy)
  have : IsReduced (RationalParameters D sy) := by
    let := UniversalCoefficientReduced.rationalGroupAlgebra_isReduced
      (NormalizationParameterGroup.Group D)
    infer_instance
  have hq : UniversalCoefficientRationalization.rationalizePolynomial D (Slot D sy) a = 0 :=
    primeFractionMaps_separate _ _ h
  simpa using hq

/-- **The field case for lower-degree parameters**: over every field of characteristic zero,
for every lower-degree parameter system and every normalization. -/
def CharZeroFieldLowerDegreeNondegeneracy : Prop :=
  ∀ (K : Type (max u v)) [Field K] [CharZero K] (Sc : Scalars D K),
    Sc.LowerDegree sy → ∀ cs : CScalars Sc, NondegeneracyConjecture cs

/-- The field case implies the conjecture for the universal lower-degree parameters. -/
theorem universal_nondegeneracy (hK : CharZeroFieldLowerDegreeNondegeneracy D sy) :
    NondegeneracyConjecture (normalizations D sy) := by
  rw [nondegeneracyConjecture_iff_injective]
  intro a b hab μ F
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hpt (p : PrimeSpectrum (RationalParameters D sy)) :
      Finsupp.mapRange.addMonoidHom
        (ScalarChange.symMap (D := D) (point D sy p)).toAddMonoidHom z = 0 := by
    have h2 : IsUnit (2 : primeFractionField (RationalParameters D sy) p) :=
      isUnit_iff_ne_zero.2 two_ne_zero
    have hinj := (nondegeneracyConjecture_iff_injective _).1
      (nondegeneracyConjecture_congr (eq_true h2) rfl rfl _
        (ScalarChange.cScalars D (point D sy p) (normalizations D sy)) (fun _ _ => rfl)
        (hK (primeFractionField (RationalParameters D sy) p)
          ((ScalarChange.scalars D (point D sy p) (scalars D sy)).withProp fun _ => h2)
          ((lowerDegree D sy).scalarChange (point D sy p))
          ((ScalarChange.cScalars D (point D sy p) (normalizations D sy)).withProp
            fun _ => h2)))
      a b hab μ F
    apply hinj
    rw [← ScalarChange.homMap_expansion, hz, map_zero, map_zero]
  ext t
  apply ScalarChange.eq_zero_of_symMap_eq_zero (fun p => point D sy p) (point_separate D sy)
    (z t)
  intro p
  simpa using congrArg (fun y => y t) (hpt p)

end LowerDegreeParameters

/-- **Reduction to fields.** Lower-degree nondegeneracy over characteristic-zero fields implies
the graded-coefficient statement, and with it the conjecture for every lower-degree parameter
system over every commutative ring in which `2` is invertible. -/
theorem gradedCoefficientNondegeneracy_of_charZeroField {sy : Symmetrizer D}
    (hK : LowerDegreeParameters.CharZeroFieldLowerDegreeNondegeneracy D sy) :
    GradedCoefficientNondegeneracy.{u, v, w} D sy :=
  LowerDegreeParameters.gradedCoefficientNondegeneracy_of_universal D sy
    (LowerDegreeParameters.universal_nondegeneracy D sy hK)

end OddMath.SKM
