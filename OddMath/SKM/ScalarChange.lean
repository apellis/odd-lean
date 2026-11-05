/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.MoreGenerators

/-!
# Transport of Brundan–Ellis scalar parameters

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
(1.3), (1.4), (1.17). A commutative ring homomorphism carries the prescribed
unit and homogeneous parameters, and the shifted bubble units, to a new
admissible choice over the target ring. The induced map on presented
Hom spaces is constructed in `ScalarChangePresentation.lean`.
-/

namespace OddMath.SKM.ScalarChange

universe u v w w'
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
  {R : Type w} {S : Type w'} [CommRing R] [CommRing S] (f : R →+* S)

/-- Transport the homogeneous parameters, including their specified units. -/
def scalars {Ptwo : Prop} (Sc : ScalarData D R Ptwo) : IntegralScalars D S where
  t i j := Units.map f.toMonoidHom (Sc.t i j)
  t_self i := by rw [Sc.t_self]; simp
  t_symm_of_d_eq_zero i j h := by rw [Sc.t_symm_of_d_eq_zero i j h]
  s i j p q := f (Sc.s i j p q)
  s_symm i j p q := by rw [Sc.s_symm]
  s_eq_zero i j p q h := by rw [Sc.s_eq_zero i j p q h, map_zero]
  two_isUnit _ := trivial

/-- The transported parameters when `2` is invertible in the source whenever some colour is
odd: `2` stays invertible in the target. -/
def unitScalars (Sc : Scalars D R) : Scalars D S :=
  { scalars D f Sc with
    two_isUnit := fun h => by
      convert (Sc.two_isUnit h).map f using 1
      exact (map_ofNat f 2).symm }

@[simp] theorem unitScalars_toIntegralScalars (Sc : Scalars D R) :
    (unitScalars D f Sc).toIntegralScalars = scalars D f Sc := rfl

/-- The shifted bubble normalization is transported with the units. -/
def cScalars {Ptwo : Prop} {Sc : ScalarData D R Ptwo} (cs : CScalars Sc) : CScalars (scalars D f Sc) where
  c μ i := Units.map f.toMonoidHom (cs.c μ i)
  shift μ i j := by
    rw [cs.shift, map_mul]
    rfl

@[simp] theorem scalars_t {Ptwo : Prop} (Sc : ScalarData D R Ptwo) (i j : I) :
    (scalars D f Sc).t i j = Units.map f.toMonoidHom (Sc.t i j) := rfl

@[simp] theorem scalars_s {Ptwo : Prop} (Sc : ScalarData D R Ptwo) (i j : I) (p q : ℕ) :
    (scalars D f Sc).s i j p q = f (Sc.s i j p q) := rfl

@[simp] theorem cScalars_c {Ptwo : Prop} {Sc : ScalarData D R Ptwo} (cs : CScalars Sc) (μ : X) (i : I) :
    (cScalars D f cs).c μ i = Units.map f.toMonoidHom (cs.c μ i) := rfl

end OddMath.SKM.ScalarChange
