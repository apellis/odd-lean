/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.NormalizationParameterGroup
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The normalization group algebra over the integers with 2 inverted

This constructs the unit-ring part of `GroundRingDescent.md` §3, supporting
Brundan–Ellis, arXiv:1701.04133v2, Theorem 8.1 and the §8 conjecture.
The group is the unsaturated `NormalizationParameterGroup.Group D`, with
all original weights and root dependencies. The base is the localization
of ℤ at the powers of 2. Specialization requires only a commutative target
ring with 2 invertible and the supplied endpoint and normalization units.

The allowed coefficient-slot polynomial extension, universal `Scalars`,
rationalization injection and reducedness are separate obligations.
Exterior bubble generators do not belong to this purely even ring.
-/

noncomputable section

namespace OddMath.SKM.UniversalCoefficientRing

universe u v w

/-- The genuine localization ℤ[1/2], not the field of rational numbers. -/
abbrev HalfIntegers := Localization.Away (2 : ℤ)

theorem two_isUnit_base : IsUnit (2 : HalfIntegers) := by
  simpa using (IsLocalization.Away.algebraMap_isUnit (S := HalfIntegers) (2 : ℤ))

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)

/-- The group-algebra part of the universal coefficient ring. -/
abbrev UnitRing := AddMonoidAlgebra HalfIntegers (NormalizationParameterGroup.Group D)

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

/-- Universal endpoint units. -/
def t (i j : I) : (UnitRing D)ˣ :=
  (groupUnit D (NormalizationParameterGroup.t D i j)).toMul

/-- Universal normalization units at every original weight. -/
def c (μ : X) (i : I) : (UnitRing D)ˣ :=
  (groupUnit D (NormalizationParameterGroup.c D μ i)).toMul

@[simp] theorem t_self (i : I) : t D i i = 1 := by
  simp [t]

theorem t_symm (i j : I) (h : D.d i j = 0) : t D i j = t D j i := by
  rw [t, t, NormalizationParameterGroup.t_symm D i j h]

theorem c_shift (μ : X) (i j : I) : c D (μ + D.α j) i = t D i j * c D μ i := by
  simp [c, t, NormalizationParameterGroup.c_shift]

theorem two_isUnit : IsUnit (2 : UnitRing D) := by
  simpa only [map_ofNat] using two_isUnit_base.map
    (AddMonoidAlgebra.singleZeroRingHom : HalfIntegers →+* UnitRing D)

variable {R : Type w} [CommRing R]

/-- The canonical map from ℤ[1/2] to any ring in which 2 is a unit. -/
def baseSpecialize (h₂ : IsUnit (2 : R)) : HalfIntegers →+* R :=
  IsLocalization.Away.lift (2 : ℤ) (g := Int.castRingHom R) (by simpa using h₂)

/-- A ring map out of ℤ[1/2] is unique; no chosen inverse of 2 is additional data. -/
theorem base_hom_ext (f g : HalfIntegers →+* R) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (2 : ℤ))
  ext n
  simp

/-- Extend a unit-valued additive homomorphism by the group-algebra universal property. -/
def lift (h₂ : IsUnit (2 : R))
    (f : NormalizationParameterGroup.Group D →+ Additive Rˣ) : UnitRing D →+* R :=
  AddMonoidAlgebra.liftNCRingHom (baseSpecialize h₂)
    { toFun := fun g => ((f g.toAdd).toMul : R)
      map_one' := by simp
      map_mul' := by intro g h; simp }
    (fun _ _ => Commute.all _ _)

@[simp] theorem lift_single (h₂ : IsUnit (2 : R))
    (f : NormalizationParameterGroup.Group D →+ Additive Rˣ)
    (g : NormalizationParameterGroup.Group D) (a : HalfIntegers) :
    lift D h₂ f (AddMonoidAlgebra.single g a) =
      baseSpecialize h₂ a * ((f g).toMul : R) := by
  simp [lift]

@[simp] theorem lift_groupUnit (h₂ : IsUnit (2 : R))
    (f : NormalizationParameterGroup.Group D →+ Additive Rˣ)
    (g : NormalizationParameterGroup.Group D) :
    Units.map (lift D h₂ f) (groupUnit D g).toMul = (f g).toMul := by
  apply Units.ext
  simp

/-- A ring homomorphism evaluated on the canonical group units. -/
def onGroup (f : UnitRing D →+* R) :
    NormalizationParameterGroup.Group D →+ Additive Rˣ where
  toFun g := Additive.ofMul (Units.map f (groupUnit D g).toMul)
  map_zero' := by simp
  map_add' g h := by simp

/-- Endpoint and normalization images determine the entire ring homomorphism. -/
theorem hom_ext {f g : UnitRing D →+* R}
    (ht : ∀ i j, Units.map f.toMonoidHom (t D i j) = Units.map g.toMonoidHom (t D i j))
    (hc : ∀ μ i, Units.map f.toMonoidHom (c D μ i) = Units.map g.toMonoidHom (c D μ i)) : f = g := by
  have hu : onGroup D f = onGroup D g := by
    apply NormalizationParameterGroup.hom_ext
    · intro i j
      exact congrArg Additive.ofMul (ht i j)
    · intro μ i
      exact congrArg Additive.ofMul (hc μ i)
  apply AddMonoidAlgebra.ringHom_ext
  · intro a
    exact RingHom.congr_fun
      (base_hom_ext (f.comp AddMonoidAlgebra.singleZeroRingHom)
        (g.comp AddMonoidAlgebra.singleZeroRingHom)) a
  · intro x
    exact congrArg (fun z : Additive Rˣ => (z.toMul : R)) (DFunLike.congr_fun hu x)

variable {D}

/-- Specialization to every supplied endpoint/normalization system, without
homogeneity, finiteness, flatness, field or independent-root assumptions. -/
def specialize (h₂ : IsUnit (2 : R)) {Sc : Scalars D R} (cs : CScalars Sc) :
    UnitRing D →+* R :=
  lift D h₂ (NormalizationParameterGroup.specialize cs)

@[simp] theorem specialize_t (h₂ : IsUnit (2 : R)) {Sc : Scalars D R}
    (cs : CScalars Sc) (i j : I) :
    Units.map (specialize h₂ cs) (t D i j) = Sc.t i j := by
  simp [specialize, t]

@[simp] theorem specialize_c (h₂ : IsUnit (2 : R)) {Sc : Scalars D R}
    (cs : CScalars Sc) (μ : X) (i : I) :
    Units.map (specialize h₂ cs) (c D μ i) = cs.c μ i := by
  simp [specialize, c]

/-- Uniqueness of specialization, including all disconnected endpoints and
all weights simultaneously. -/
theorem specialize_unique (h₂ : IsUnit (2 : R)) {Sc : Scalars D R}
    (cs : CScalars Sc) (f : UnitRing D →+* R)
    (ht : ∀ i j, Units.map f (t D i j) = Sc.t i j)
    (hc : ∀ μ i, Units.map f (c D μ i) = cs.c μ i) : f = specialize h₂ cs := by
  apply hom_ext
  · intro i j
    exact (ht i j).trans (specialize_t h₂ cs i j).symm
  · intro μ i
    exact (hc μ i).trans (specialize_c h₂ cs μ i).symm

end OddMath.SKM.UniversalCoefficientRing
