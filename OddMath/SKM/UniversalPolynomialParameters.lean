/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.UniversalCoefficientRing
import OddMath.SKM.Grading
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Universal homogeneous scalar parameters

The coefficient-slot polynomial extension in `GroundRingDescent.md` §3,
for the proposed deduction supporting Brundan–Ellis, arXiv:1701.04133v2,
Theorem 8.1 and the §8 conjecture. The slot restrictions are precisely
`Scalars.s_eq_zero`, its symmetric counterpart, and `Scalars.Homogeneous`.
All allowed unused slots remain, including diagonal slots. No symmetrizer
is needed for this construction: the homogeneity predicate uses `D.d`.
The original colours, weights and unsaturated normalization group are retained.
Exterior bubble generators, rationalization and reducedness are not part
of this construction.
-/

noncomputable section

namespace OddMath.SKM.UniversalPolynomialParameters

universe u v w

/-- A coefficient position, whether or not it occurs in the presentation. -/
structure RawSlot (I : Type u) where
  i : I
  j : I
  p : ℕ
  q : ℕ

/-- Exchange the two colours and their exponents. -/
def RawSlot.swap {I : Type u} (a : RawSlot I) : RawSlot I := ⟨a.j, a.i, a.q, a.p⟩

@[simp] theorem RawSlot.swap_swap {I : Type u} (a : RawSlot I) : a.swap.swap = a := rfl

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)

/-- Separate odd support everywhere, and homogeneity only in the used rectangle. -/
def Allowed (a : RawSlot I) : Prop :=
  (a.p : ZMod 2) * D.parity a.i ≠ 1 ∧
  (a.q : ZMod 2) * D.parity a.j ≠ 1 ∧
  (0 < a.p → (a.p : ℤ) < D.d a.i a.j →
    0 < a.q → (a.q : ℤ) < D.d a.j a.i →
    a.p * D.d a.j a.i + a.q * D.d a.i a.j = D.d a.i a.j * D.d a.j a.i)

theorem allowed_swap (a : RawSlot I) (h : Allowed D a) : Allowed D a.swap := by
  refine ⟨h.2.1, h.1, ?_⟩
  intro hq hq' hp hp'
  simpa only [RawSlot.swap, add_comm, mul_comm] using h.2.2 hp hp' hq hq'

/-- Allowed positions modulo the swap involution, with no extra identifications. -/
def Slot := Quot (fun a b : {a : RawSlot I // Allowed D a} => b.val = a.val.swap)

/-- The class of an allowed position. -/
def slot (a : RawSlot I) (h : Allowed D a) : Slot D := Quot.mk _ ⟨a, h⟩

theorem slot_swap (a : RawSlot I) (h : Allowed D a) :
    slot D a h = slot D a.swap (allowed_swap D a h) := Quot.sound rfl

/-- Fix the canonical ring structure before forming the nested group algebras. -/
local instance halfIntegersCommRing : CommRing UniversalCoefficientRing.HalfIntegers :=
  inferInstance

local instance unitRingCommRing : CommRing (UniversalCoefficientRing.UnitRing D) :=
  inferInstance

/-- The ordinary polynomial ring over the normalization group algebra. -/
abbrev ParameterRing := MvPolynomial (Slot D) (UniversalCoefficientRing.UnitRing D)

instance parameterRingCommRing : CommRing (ParameterRing D) := inferInstance

/-- The base localization makes 2 a unit, independently of the parity of the datum. -/
theorem two_isUnit : IsUnit (2 : ParameterRing D) := by
  simpa only [map_ofNat] using (UniversalCoefficientRing.two_isUnit D).map
    (MvPolynomial.C : UniversalCoefficientRing.UnitRing D →+* ParameterRing D)

/-- The universal coefficient, set to zero at the forbidden positions. -/
def coefficient (a : RawSlot I) : ParameterRing D := by
  classical
  exact if h : Allowed D a then MvPolynomial.X (slot D a h) else 0

theorem coefficient_of_allowed (a : RawSlot I) (h : Allowed D a) :
    coefficient D a = MvPolynomial.X (slot D a h) := by
  classical
  simp [coefficient, h]

theorem coefficient_of_not_allowed (a : RawSlot I) (h : ¬ Allowed D a) :
    coefficient D a = 0 := by
  classical
  simp [coefficient, h]

theorem coefficient_swap (a : RawSlot I) : coefficient D a = coefficient D a.swap := by
  classical
  by_cases h : Allowed D a
  · rw [coefficient_of_allowed D a h,
      coefficient_of_allowed D a.swap (allowed_swap D a h), slot_swap D a h]
  · have hs : ¬ Allowed D a.swap := fun hs => h (by simpa using allowed_swap D a.swap hs)
    rw [coefficient_of_not_allowed D a h, coefficient_of_not_allowed D a.swap hs]

/-- Universal endpoint units and coefficient slots. -/
def scalars : Scalars D (ParameterRing D) where
  t i j := Units.map
    (MvPolynomial.C : UniversalCoefficientRing.UnitRing D →+* ParameterRing D).toMonoidHom
    (UniversalCoefficientRing.t D i j)
  t_self i := by simp
  t_symm_of_d_eq_zero i j h := by rw [UniversalCoefficientRing.t_symm D i j h]
  s i j p q := coefficient D ⟨i, j, p, q⟩
  s_symm i j p q := coefficient_swap D ⟨i, j, p, q⟩
  s_eq_zero i j p q h := coefficient_of_not_allowed D _ (fun ha => ha.1 h)
  two_isUnit _ := two_isUnit D

/-- The exact existing homogeneity predicate, not a stronger global support bound. -/
theorem homogeneous : (scalars D).Homogeneous := by
  intro i j p q hp hp' hq hq' hn
  by_cases h : Allowed D ⟨i, j, p, q⟩
  · exact h.2.2 hp hp' hq hq'
  · exact (hn (coefficient_of_not_allowed D _ h)).elim

/-- All normalization units at the original weights, with their shift laws. -/
def normalizations : CScalars (scalars D) where
  c μ i := Units.map
    (MvPolynomial.C : UniversalCoefficientRing.UnitRing D →+* ParameterRing D).toMonoidHom
    (UniversalCoefficientRing.c D μ i)
  shift μ i j := by simp [UniversalCoefficientRing.c_shift, scalars]

variable {R : Type w} [CommRing R] {D}

/-- A nonzero supplied coefficient is an allowed position, including unused ones. -/
theorem allowed_of_ne_zero (Sc : Scalars D R) (hh : Sc.Homogeneous)
    (a : RawSlot I) (h : Sc.s a.i a.j a.p a.q ≠ 0) : Allowed D a := by
  refine ⟨fun hp => h (Sc.s_eq_zero _ _ _ _ hp), ?_, ?_⟩
  · intro hq
    apply h
    rw [Sc.s_symm]
    exact Sc.s_eq_zero _ _ _ _ hq
  · exact fun hp hp' hq hq' => hh _ _ _ _ hp hp' hq hq' h

/-- Evaluation on quotient slots is well defined by the supplied symmetry law. -/
def slotValue (Sc : Scalars D R) : Slot D → R :=
  Quot.lift (fun a => Sc.s a.val.i a.val.j a.val.p a.val.q) (by
    intro a b h
    rw [h]
    exact Sc.s_symm _ _ _ _)

/-- Specialize every unit and every allowed coefficient, without restrictions on
colours, roots, the target's zero divisors or its characteristic beyond 2 being a unit. -/
def specialize (h₂ : IsUnit (2 : R)) {Sc : Scalars D R} (cs : CScalars Sc) :
    ParameterRing D →+* R :=
  MvPolynomial.eval₂Hom (UniversalCoefficientRing.specialize h₂ cs) (slotValue Sc)

@[simp] theorem specialize_C (h₂ : IsUnit (2 : R)) {Sc : Scalars D R}
    (cs : CScalars Sc) (a : UniversalCoefficientRing.UnitRing D) :
    specialize h₂ cs (MvPolynomial.C a) = UniversalCoefficientRing.specialize h₂ cs a := by
  simp [specialize]

@[simp] theorem specialize_coefficient (h₂ : IsUnit (2 : R)) {Sc : Scalars D R}
    (cs : CScalars Sc) (hh : Sc.Homogeneous) (a : RawSlot I) :
    specialize h₂ cs (coefficient D a) = Sc.s a.i a.j a.p a.q := by
  classical
  by_cases h : Allowed D a
  · simp [coefficient, h, specialize, slotValue, slot]
  · have hz : Sc.s a.i a.j a.p a.q = 0 := by
      by_contra hn
      exact h (allowed_of_ne_zero Sc hh a hn)
    simp [coefficient, h, hz]

@[simp] theorem specialize_t (h₂ : IsUnit (2 : R)) {Sc : Scalars D R}
    (cs : CScalars Sc) (i j : I) :
    Units.map (specialize h₂ cs).toMonoidHom ((scalars D).t i j) = Sc.t i j := by
  apply Units.ext
  change specialize h₂ cs (MvPolynomial.C (UniversalCoefficientRing.t D i j :
    UniversalCoefficientRing.UnitRing D)) = (Sc.t i j : R)
  rw [specialize_C]
  exact congrArg (fun z : Rˣ => (z : R))
    (UniversalCoefficientRing.specialize_t h₂ cs i j)

@[simp] theorem specialize_c (h₂ : IsUnit (2 : R)) {Sc : Scalars D R}
    (cs : CScalars Sc) (μ : X) (i : I) :
    Units.map (specialize h₂ cs).toMonoidHom ((normalizations D).c μ i) = cs.c μ i := by
  apply Units.ext
  change specialize h₂ cs (MvPolynomial.C (UniversalCoefficientRing.c D μ i :
    UniversalCoefficientRing.UnitRing D)) = (cs.c μ i : R)
  rw [specialize_C]
  exact congrArg (fun z : Rˣ => (z : R))
    (UniversalCoefficientRing.specialize_c h₂ cs μ i)

/-- Endpoint, normalization and coefficient images determine a ring map uniquely. -/
theorem hom_ext {f g : ParameterRing D →+* R}
    (ht : ∀ i j, Units.map f.toMonoidHom ((scalars D).t i j) = Units.map g.toMonoidHom ((scalars D).t i j))
    (hc : ∀ μ i, Units.map f.toMonoidHom ((normalizations D).c μ i) =
      Units.map g.toMonoidHom ((normalizations D).c μ i))
    (hs : ∀ i j p q, f ((scalars D).s i j p q) = g ((scalars D).s i j p q)) : f = g := by
  apply MvPolynomial.ringHom_ext'
  · apply UniversalCoefficientRing.hom_ext
    · intro i j
      exact ht i j
    · intro μ i
      exact hc μ i
  · intro a
    induction a using Quot.inductionOn with
    | h a =>
      rcases a with ⟨⟨i, j, p, q⟩, ha⟩
      have h := hs i j p q
      change f (coefficient D ⟨i, j, p, q⟩) = g (coefficient D ⟨i, j, p, q⟩) at h
      simpa only [coefficient_of_allowed D _ ha, slot] using h

/-- Unique simultaneous specialization of the supplied Scalars and CScalars,
including coefficients outside all used rectangles. -/
theorem specialize_unique (h₂ : IsUnit (2 : R)) {Sc : Scalars D R}
    (cs : CScalars Sc) (hh : Sc.Homogeneous) (f : ParameterRing D →+* R)
    (ht : ∀ i j, Units.map f.toMonoidHom ((scalars D).t i j) = Sc.t i j)
    (hc : ∀ μ i, Units.map f.toMonoidHom ((normalizations D).c μ i) = cs.c μ i)
    (hs : ∀ i j p q, f ((scalars D).s i j p q) = Sc.s i j p q) : f = specialize h₂ cs := by
  apply hom_ext
  · intro i j
    exact (ht i j).trans (specialize_t h₂ cs i j).symm
  · intro μ i
    exact (hc μ i).trans (specialize_c h₂ cs μ i).symm
  · intro i j p q
    exact (hs i j p q).trans (specialize_coefficient h₂ cs hh ⟨i, j, p, q⟩).symm

end OddMath.SKM.UniversalPolynomialParameters
