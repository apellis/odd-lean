/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.Diagrams.OddNilHecke.Relations
import OddMath.Frontier.NilHeckeAction

/-!
# Integral odd nilHecke generators over a coefficient ring

The presented integral ring maps to the diagrammatic odd nilHecke category
over any commutative ring. This is the coefficient extension needed for
BE2 §11's same-colour map when the coefficient ring has two invertible.
-/
noncomputable section
namespace OddMath.Diagrams.OddNilHecke
open CategoryTheory StringDiagrams
open OddMath.Frontier NilHeckeAction
variable (k : Type*) [CommRing k]

/-- Dots and crossings of the free algebra go to the corresponding diagrams on `n + 2`
strands. -/
def toDiagramsOverFree (n : ℕ) : NilHeckeAction.Free n →ₐ[ℤ] End ((pres k).obj (strands (n + 2))) :=
  FreeAlgebra.lift ℤ (Sum.elim (fun j => x k (n + 2) j) (fun i => ψ k (n + 2) i))

@[simp] theorem toDiagramsOverFree_dot (n : ℕ) (j : Fin (n + 2)) :
    toDiagramsOverFree k n (dotFree n j) = x k (n + 2) j := by
  simp [toDiagramsOverFree, dotFree]

@[simp] theorem toDiagramsOverFree_crossing (n : ℕ) (i : Fin (n + 1)) :
    toDiagramsOverFree k n (crossingFree n i) = ψ k (n + 2) i := by
  simp [toDiagramsOverFree, crossingFree]

/-- Every relator of EKL Prop. 2.1 holds between the diagrams. -/
theorem toDiagramsOverFree_relator (n : ℕ) (w : NilHeckeAction.Free n) (hw : Relator n w) :
    toDiagramsOverFree k n w = 0 := by
  cases hw with
  | square i =>
    simp only [map_mul, toDiagramsOverFree_crossing]
    exact ψ_mul_ψ k _ _
  | braid i j h =>
    simp only [map_sub, map_mul, toDiagramsOverFree_crossing, sub_eq_zero, h]
    exact ψ_braid k _ _
  | dots i j h =>
    simp only [map_add, map_mul, toDiagramsOverFree_dot]
    exact x_mul_x_add_x_mul_x k (Fin.val_ne_of_ne h)
  | distant i j h =>
    simp only [map_add, map_mul, toDiagramsOverFree_crossing]
    exact ψ_mul_ψ_add_ψ_mul_ψ k h
  | mixedRight i =>
    simp only [map_sub, map_add, map_mul, map_one, toDiagramsOverFree_dot, toDiagramsOverFree_crossing,
      Fin.val_castSucc, Fin.val_succ, sub_eq_zero]
    exact x_mul_ψ_add_ψ_mul_x k (by omega)
  | mixedLeft i =>
    simp only [map_sub, map_add, map_mul, map_one, toDiagramsOverFree_dot, toDiagramsOverFree_crossing,
      Fin.val_castSucc, Fin.val_succ, sub_eq_zero]
    exact ψ_mul_x_add_x_mul_ψ k (by omega)
  | spectator i j hl hr =>
    simp only [map_add, map_mul, toDiagramsOverFree_dot, toDiagramsOverFree_crossing]
    exact x_mul_ψ_add_ψ_mul_x_of_ne k (fun h => hl (Fin.ext h)) (fun h => hr (Fin.ext h))

theorem toDiagramsOverFree_ideal (n : ℕ) (w : NilHeckeAction.Free n) (hw : w ∈ relIdeal n) :
    toDiagramsOverFree k n w = 0 := by
  rw [relIdeal, relTwoSided, TwoSidedIdeal.mem_asIdeal] at hw
  induction hw using TwoSidedIdeal.span_induction with
  | mem x h => exact toDiagramsOverFree_relator k n x h
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | neg x hx ih => rw [map_neg, ih, neg_zero]
  | left_absorb a x hx ih => rw [map_mul, ih, mul_zero]
  | right_absorb b x hx ih => rw [map_mul, ih, zero_mul]

/-- The comparison homomorphism from odd-lean's presented odd nilHecke ring to endomorphisms
of `n + 2` strands in the diagrammatic category. -/
def toDiagramsOver (n : ℕ) : Presented n →+* End ((pres k).obj (strands (n + 2))) :=
  Ideal.Quotient.lift (relIdeal n) (toDiagramsOverFree k n).toRingHom (toDiagramsOverFree_ideal k n)

@[simp] theorem toDiagramsOver_mk (n : ℕ) (w : NilHeckeAction.Free n) :
    toDiagramsOver k n (Ideal.Quotient.mk (relIdeal n) w) = toDiagramsOverFree k n w := rfl

@[simp] theorem toDiagramsOver_dot (n : ℕ) (j : Fin (n + 2)) :
    toDiagramsOver k n (dot n j) = x k (n + 2) j := toDiagramsOverFree_dot k n j

@[simp] theorem toDiagramsOver_crossing (n : ℕ) (i : Fin (n + 1)) :
    toDiagramsOver k n (crossing n i) = ψ k (n + 2) i := toDiagramsOverFree_crossing k n i


end OddMath.Diagrams.OddNilHecke
