/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.UniversalCoefficientRing
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Rationalization of the normalization group algebra

The coefficientwise injection in `GroundRingDescent.md` §4, supporting
Brundan–Ellis, arXiv:1701.04133v2, Theorem 8.1 and the §8 conjecture.
The original unsaturated normalization group is unchanged. This establishes
neither reducedness of its rational group algebra nor nondegeneracy.
-/

noncomputable section

namespace OddMath.SKM.UniversalCoefficientRationalization

open UniversalCoefficientRing

universe u v w

/-- The canonical coefficient inclusion from ℤ[1/2] into ℚ. -/
def coefficientMap : HalfIntegers →+* ℚ :=
  baseSpecialize (show IsUnit (2 : ℚ) by norm_num)

theorem coefficientMap_injective : Function.Injective coefficientMap := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (2 : ℤ)) coefficientMap).2
  intro a b
  constructor
  · intro h
    simpa only [coefficientMap, baseSpecialize, IsLocalization.Away.lift_eq] using
      (congrArg coefficientMap h)
  · intro h
    exact congrArg (algebraMap ℤ HalfIntegers) ((Int.castRingHom ℚ).injective_int
      (by simpa only [coefficientMap, baseSpecialize, IsLocalization.Away.lift_eq] using h))

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)

/-- Rational group algebra on the same, potentially torsion-bearing group. -/
abbrev RationalUnitRing := AddMonoidAlgebra ℚ (NormalizationParameterGroup.Group D)

/-- Coefficientwise rationalization without changing the group index. -/
def rationalize : UnitRing D →+* RationalUnitRing D :=
  AddMonoidAlgebra.mapRingHom _ coefficientMap

@[simp] theorem rationalize_single (g : NormalizationParameterGroup.Group D)
    (a : HalfIntegers) :
    rationalize D (AddMonoidAlgebra.single g a) =
      AddMonoidAlgebra.single g (coefficientMap a) :=
  AddMonoidAlgebra.mapRingHom_single _ _ _

@[simp] theorem rationalize_groupUnit (g : NormalizationParameterGroup.Group D) :
    rationalize D ((groupUnit D g).toMul : UnitRing D) =
      AddMonoidAlgebra.single g 1 := by
  simp

@[simp] theorem rationalize_t (i j : I) :
    rationalize D ((t D i j : (UnitRing D)ˣ) : UnitRing D) =
      AddMonoidAlgebra.single (NormalizationParameterGroup.t D i j) 1 := by
  exact rationalize_groupUnit D _

@[simp] theorem rationalize_c (μ : X) (i : I) :
    rationalize D ((c D μ i : (UnitRing D)ˣ) : UnitRing D) =
      AddMonoidAlgebra.single (NormalizationParameterGroup.c D μ i) 1 := by
  exact rationalize_groupUnit D _

/-- Injectivity is coefficientwise; no torsion-freeness or domain hypothesis on `G`. -/
theorem rationalize_injective : Function.Injective (rationalize D) :=
  AddMonoidAlgebra.map_injective _ coefficientMap_injective

/-- The same injection for polynomials over any variable type, including empty ones. -/
def rationalizePolynomial (σ : Type w) :
    MvPolynomial σ (UnitRing D) →+* MvPolynomial σ (RationalUnitRing D) :=
  MvPolynomial.map (rationalize D)

theorem rationalizePolynomial_injective (σ : Type w) :
    Function.Injective (rationalizePolynomial D σ) :=
  MvPolynomial.map_injective _ (rationalize_injective D)

@[simp] theorem rationalizePolynomial_C (σ : Type w) (a : UnitRing D) :
    rationalizePolynomial D σ (MvPolynomial.C a) = MvPolynomial.C (rationalize D a) :=
  MvPolynomial.map_C _ _

@[simp] theorem rationalizePolynomial_X (σ : Type w) (s : σ) :
    rationalizePolynomial D σ (MvPolynomial.X s) = MvPolynomial.X s :=
  MvPolynomial.map_X _ _

end OddMath.SKM.UniversalCoefficientRationalization
