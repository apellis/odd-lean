/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CliffordLocalization

/-!
# Colour projections on localized polynomial–Clifford coefficients

Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2, Definition 3.5(i)–(iii).
The colour involution acts together with the Clifford operator, rather than
leaving the colour summand fixed. For finite colours the projections sum to
one. The construction works over arbitrary commutative rings; it does not
supply the crossing operators or an action of `Hn`.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.QuiverHecke.CliffordColours

variable {R J : Type*} [CommRing R] {n : ℕ}

/-- Colour words of length `n`. -/
abbrev Word (J : Type*) (n : ℕ) := Fin n → J

/-- The colour-indexed localized coefficient module. -/
abbrev Space (R J : Type*) [CommRing R] (n : ℕ) :=
  Word J n → CliffordLocalization.Coeff (R := R) (n := n)

/-- Apply the colour involution at one position. -/
def flip (c : J → J) (i : Fin n) (ν : Word J n) : Word J n :=
  fun j => if j = i then c (ν j) else ν j

@[simp] theorem flip_flip (c : J → J) (hc : Function.Involutive c)
    (i : Fin n) (ν : Word J n) : flip c i (flip c i ν) = ν := by
  funext j
  by_cases h : j = i <;> simp [flip, h, hc]

theorem flip_commute (c : J → J) (i j : Fin n) (ν : Word J n) :
    flip c i (flip c j ν) = flip c j (flip c i ν) := by
  funext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp [flip, hi, hj]

/-- Projection onto a single colour word. -/
def e (ν : Word J n) : Module.End R (Space R J n) where
  toFun f μ := if μ = ν then f μ else 0
  map_add' f g := by classical funext μ; by_cases h : μ = ν <;> simp [h]
  map_smul' a f := by classical funext μ; by_cases h : μ = ν <;> simp [h]

@[simp] theorem e_apply (ν μ : Word J n) (f : Space R J n) :
    e ν f μ = if μ = ν then f μ else 0 := rfl

/-- Colour projections are pairwise orthogonal idempotents. -/
theorem e_mul (ν μ : Word J n) :
    e (R := R) ν * e μ = if ν = μ then e ν else 0 := by
  classical
  ext f κ
  by_cases h : ν = μ <;> by_cases hκ : κ = ν <;>
    simp_all [Module.End.mul_apply]

/-- For a finite colour set the colour projections resolve the identity. -/
theorem sum_e [Fintype J] : (∑ ν : Word J n, e (R := R) ν) = 1 := by
  classical
  ext f μ
  simp [e_apply]

/-- Scalar multiplication on every colour summand. -/
def scalar (a : CliffordLocalization.K R n) : Module.End R (Space R J n) where
  toFun f ν := CliffordLocalization.scalar a (f ν)
  map_add' f g := by ext ν; simp
  map_smul' a f := by ext ν; simp

/-- Clifford multiplication with the required colour change. -/
def C (c : J → J) (i : Fin n) : Module.End R (Space R J n) where
  toFun f ν := CliffordLocalization.C i (f (flip c i ν))
  map_add' f g := by ext ν; simp
  map_smul' a f := by ext ν; simp

@[simp] theorem C_apply (c : J → J) (i : Fin n) (f : Space R J n) (ν : Word J n) :
    C c i f ν = CliffordLocalization.C i (f (flip c i ν)) := rfl

/-- KKT's colour transport relation for the Clifford generator. -/
theorem C_e (c : J → J) (hc : Function.Involutive c) (i : Fin n) (ν : Word J n) :
    C (R := R) c i * e ν = e (flip c i ν) * C c i := by
  classical
  have hiff (μ : Word J n) : flip c i μ = ν ↔ μ = flip c i ν :=
    ⟨fun h => by rw [← h, flip_flip c hc], fun h => by rw [h, flip_flip c hc]⟩
  ext f μ
  simp only [Module.End.mul_apply, C_apply, e_apply]
  by_cases h : μ = flip c i ν <;> simp [hiff, h]

/-- Colour-coupled Clifford generators square to the identity. -/
theorem C_sq (c : J → J) (hc : Function.Involutive c) (i : Fin n) :
    C (R := R) c i * C c i = 1 := by
  ext f ν
  simp only [Module.End.mul_apply, C_apply, flip_flip c hc]
  exact DFunLike.congr_fun (CliffordLocalization.C_sq (R := R) i) (f ν)

/-- Colour changes preserve anticommutation of distinct Clifford generators. -/
theorem C_anticommute (c : J → J) (i j : Fin n) (hij : i ≠ j) :
    C (R := R) c i * C c j = -(C c j * C c i) := by
  ext f ν
  simp only [Module.End.mul_apply, C_apply, LinearMap.neg_apply, Pi.neg_apply]
  rw [flip_commute c i j]
  exact DFunLike.congr_fun (CliffordLocalization.C_anticommute (R := R) i j hij)
    (f (flip c j (flip c i ν)))

/-- The colour projections commute with all localized scalar operators. -/
theorem scalar_e (a : CliffordLocalization.K R n) (ν : Word J n) :
    scalar (J := J) a * e ν = e ν * scalar a := by
  classical
  ext f μ
  by_cases h : μ = ν <;> simp [Module.End.mul_apply, scalar, h]

/-- Clifford generators reflect scalar coefficients also on colour summands. -/
theorem C_scalar (c : J → J) (i : Fin n) (a : CliffordLocalization.K R n) :
    C c i * scalar a = scalar (CliffordLocalization.reflect i a) * C c i := by
  ext f ν
  exact DFunLike.congr_fun (CliffordLocalization.C_scalar i a) (f (flip c i ν))

end OddMath.QuiverHecke.CliffordColours
