/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.UniversalPolynomialParameters

/-!
# The universal parameters over the integers

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5 and the
Nondegeneracy Conjecture of §8, for the integral form of the presentation, in which `2` need not
be invertible. This is the integral counterpart of `UniversalPolynomialParameters`: the
normalization group algebra over `ℤ` (instead of `ℤ[1/2]`), with one polynomial variable for every
allowed coefficient slot.

## Main results

* `ParameterRing`, `scalars`, `normalizations`: the universal integral parameters, homogeneous
  (`homogeneous`).
* `specialize`: the unique ring map to any commutative ring `R` sending the universal parameters
  to given homogeneous `Sc : IntegralScalars D R` and `cs : CScalars Sc`
  (`specialize_t`, `specialize_c`, `specialize_coefficient`). No condition on `2` is needed.
* `toHalf`: the coefficient map to `UniversalPolynomialParameters.ParameterRing D` induced by
  `ℤ → ℤ[1/2]`. It is injective (`toHalf_injective`) and sends the integral universal parameters to
  the universal parameters with `2` inverted (`toHalf_t`, `toHalf_c`, `toHalf_coefficient`).
-/

noncomputable section

namespace OddMath.SKM.IntegralParameters

open UniversalPolynomialParameters

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)

/-- The group algebra over `ℤ` of the normalization group. -/
abbrev UnitRing := AddMonoidAlgebra ℤ (NormalizationParameterGroup.Group D)

/-- Every group element gives a unit, with inverse indexed by its negative. -/
def groupUnit : NormalizationParameterGroup.Group D →+ Additive (UnitRing D)ˣ where
  toFun g := Additive.ofMul {
    val := AddMonoidAlgebra.single g 1
    inv := AddMonoidAlgebra.single (-g) 1
    val_inv := by simp [← AddMonoidAlgebra.one_def]
    inv_val := by simp [← AddMonoidAlgebra.one_def] }
  map_zero' := by apply congrArg Additive.ofMul; apply Units.ext; rfl
  map_add' g h := by
    apply congrArg Additive.ofMul
    apply Units.ext
    simp

@[simp] theorem groupUnit_val (g : NormalizationParameterGroup.Group D) :
    ((groupUnit D g).toMul : UnitRing D) = AddMonoidAlgebra.single g 1 := rfl

/-- The ordinary polynomial ring over the integral normalization group algebra. -/
abbrev ParameterRing := MvPolynomial (Slot D) (UnitRing D)

/-- Universal endpoint units. -/
def tU (i j : I) : (ParameterRing D)ˣ :=
  Units.map (MvPolynomial.C : UnitRing D →+* ParameterRing D).toMonoidHom
    (groupUnit D (NormalizationParameterGroup.t D i j)).toMul

/-- Universal normalization units. -/
def cU (μ : X) (i : I) : (ParameterRing D)ˣ :=
  Units.map (MvPolynomial.C : UnitRing D →+* ParameterRing D).toMonoidHom
    (groupUnit D (NormalizationParameterGroup.c D μ i)).toMul

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

/-- The universal integral parameters. -/
def scalars : IntegralScalars D (ParameterRing D) where
  t := tU D
  t_self i := by simp [tU]
  t_symm_of_d_eq_zero i j h := by rw [tU, tU, NormalizationParameterGroup.t_symm D i j h]
  s i j p q := coefficient D ⟨i, j, p, q⟩
  s_symm i j p q := coefficient_swap D ⟨i, j, p, q⟩
  s_eq_zero i j p q h := coefficient_of_not_allowed D _ (fun ha => ha.1 h)
  two_isUnit _ := trivial

theorem homogeneous : (scalars D).Homogeneous := by
  intro i j p q hp hp' hq hq' hn
  by_cases h : Allowed D ⟨i, j, p, q⟩
  · exact h.2.2 hp hp' hq hq'
  · exact (hn (coefficient_of_not_allowed D _ h)).elim

/-- The universal integral normalization units. -/
def normalizations : CScalars (scalars D) where
  c := cU D
  shift μ i j := by
    apply Units.ext
    simp [cU, tU, scalars, NormalizationParameterGroup.c_shift]

variable {R : Type w} [CommRing R] {D}

/-- The unit part of the specialization. -/
def unitSpecialize {Ptwo : Prop} {Sc : ScalarData D R Ptwo} (cs : CScalars Sc) : UnitRing D →+* R :=
  AddMonoidAlgebra.liftNCRingHom (Int.castRingHom R)
    { toFun := fun g => ((NormalizationParameterGroup.specialize cs g.toAdd).toMul : R)
      map_one' := by simp
      map_mul' := by intro g h; simp }
    (fun _ _ => Commute.all _ _)

theorem unitSpecialize_groupUnit {Ptwo : Prop} {Sc : ScalarData D R Ptwo} (cs : CScalars Sc)
    (g : NormalizationParameterGroup.Group D) :
    Units.map (unitSpecialize cs) (groupUnit D g).toMul =
      (NormalizationParameterGroup.specialize cs g).toMul := by
  apply Units.ext
  simp [unitSpecialize]

/-- Specialization of the universal integral parameters to homogeneous parameters over any
commutative ring. -/
def specialize {Ptwo : Prop} {Sc : ScalarData D R Ptwo} (cs : CScalars Sc) : ParameterRing D →+* R :=
  MvPolynomial.eval₂Hom (unitSpecialize cs) (slotValue Sc)

@[simp] theorem specialize_t {Ptwo : Prop} {Sc : ScalarData D R Ptwo} (cs : CScalars Sc) (i j : I) :
    Units.map (specialize cs).toMonoidHom ((scalars D).t i j) = Sc.t i j := by
  apply Units.ext
  change specialize cs (MvPolynomial.C _) = _
  simp only [specialize, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
  exact congrArg (fun z : Rˣ => (z : R)) ((unitSpecialize_groupUnit cs _).trans (by simp))

@[simp] theorem specialize_c {Ptwo : Prop} {Sc : ScalarData D R Ptwo} (cs : CScalars Sc) (μ : X) (i : I) :
    Units.map (specialize cs).toMonoidHom ((normalizations D).c μ i) = cs.c μ i := by
  apply Units.ext
  change specialize cs (MvPolynomial.C _) = _
  simp only [specialize, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
  exact congrArg (fun z : Rˣ => (z : R)) ((unitSpecialize_groupUnit cs _).trans (by simp))

@[simp] theorem specialize_coefficient {Ptwo : Prop} {Sc : ScalarData D R Ptwo} (cs : CScalars Sc)
    (hh : Sc.Homogeneous) (a : RawSlot I) :
    specialize cs (coefficient D a) = Sc.s a.i a.j a.p a.q := by
  classical
  by_cases h : Allowed D a
  · simp [coefficient, h, specialize, slotValue, slot]
  · have hz : Sc.s a.i a.j a.p a.q = 0 := by
      by_contra hn
      exact h (allowed_of_ne_zero Sc hh a hn)
    simp [coefficient, h, hz]

variable (D)

/-- The coefficient map `ℤ → ℤ[1/2]` on the universal parameter rings. -/
def toHalf : ParameterRing D →+* UniversalPolynomialParameters.ParameterRing D :=
  MvPolynomial.map (AddMonoidAlgebra.mapRingHom _
    (Int.castRingHom UniversalCoefficientRing.HalfIntegers))

theorem toHalf_injective : Function.Injective (toHalf D) := by
  apply MvPolynomial.map_injective
  apply AddMonoidAlgebra.map_injective
  have h := IsLocalization.injective (S := UniversalCoefficientRing.HalfIntegers)
    (M := Submonoid.powers (2 : ℤ)) (powers_le_nonZeroDivisors_of_noZeroDivisors two_ne_zero)
  rwa [show algebraMap ℤ UniversalCoefficientRing.HalfIntegers = Int.castRingHom _ from
    RingHom.ext_int _ _] at h

@[simp] theorem toHalf_t (i j : I) :
    Units.map (toHalf D).toMonoidHom ((scalars D).t i j) =
      (UniversalPolynomialParameters.scalars D).t i j := by
  apply Units.ext
  simp [toHalf, scalars, tU, UniversalPolynomialParameters.scalars, UniversalCoefficientRing.t]

@[simp] theorem toHalf_c (μ : X) (i : I) :
    Units.map (toHalf D).toMonoidHom ((normalizations D).c μ i) =
      (UniversalPolynomialParameters.normalizations D).c μ i := by
  apply Units.ext
  simp [toHalf, normalizations, cU, UniversalPolynomialParameters.normalizations,
    UniversalCoefficientRing.c]

@[simp] theorem toHalf_coefficient (a : RawSlot I) :
    toHalf D (coefficient D a) = UniversalPolynomialParameters.coefficient D a := by
  classical
  by_cases h : Allowed D a
  · simp [coefficient, UniversalPolynomialParameters.coefficient, h, toHalf]
  · simp [coefficient, UniversalPolynomialParameters.coefficient, h]

end OddMath.SKM.IntegralParameters
