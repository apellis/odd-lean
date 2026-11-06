/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BWWScalars

/-!
# The root cover of a super Kac–Moody datum

The units `c_{λ;i}` of Brundan–Ellis, arXiv:1701.04133v2, (1.17), satisfy
`c_{λ+αⱼ;i} = tᵢⱼ c_{λ;i}`; when the simple roots are linearly dependent this constrains the
`tᵢⱼ` (`OddMath.SKM.RootCoverUnits`). Brundan–Wang–Webster, arXiv:2505.22929v2, Remark 2.4,
use arbitrary normalizations instead. This file sets up the integer relations among the simple
roots and a cover of the weight lattice with independent simple roots.

* `rootSum D : (I →₀ ℤ) →+ X`, `n ↦ Σ nⱼ αⱼ`, and `rootChar t i : (I →₀ ℤ) →+ Additive kˣ`,
  `n ↦ Π tᵢⱼ^{nⱼ}`.
* `rootCover D`: the datum on `X × (I →₀ ℤ)` with roots `(αᵢ, eᵢ)` and coroots `hᵢ ∘ fst`.
  It has the same Cartan matrix, `dᵢⱼ` and parity, and independent simple roots
  (`rootSum_rootCover`). Parameters transport unchanged (`coverScalars`, `coverBWWScalars`),
  and the first projection is compatible with roots and coroots (`fst_root`, `h_rootCover`).

Comparing the 2-categories of `D` and `rootCover D` is not done here.
-/

noncomputable section

namespace OddMath.SKM.RootCover

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X) {k : Type w} [CommRing k]

/-- `n ↦ Σ nⱼ αⱼ`. -/
def rootSum : (I →₀ ℤ) →+ X :=
  Finsupp.liftAddHom fun j => zmultiplesHom X (D.α j)

@[simp] theorem rootSum_single (j : I) (m : ℤ) :
    rootSum D (Finsupp.single j m) = m • D.α j := by
  simp [rootSum]

/-- `n ↦ Π tᵢⱼ^{nⱼ}`, written additively. -/
def rootChar (t : I → I → kˣ) (i : I) : (I →₀ ℤ) →+ Additive kˣ :=
  Finsupp.liftAddHom fun j => zmultiplesHom (Additive kˣ) (Additive.ofMul (t i j))

@[simp] theorem rootChar_single (t : I → I → kˣ) (i j : I) (m : ℤ) :
    Additive.toMul (rootChar t i (Finsupp.single j m)) = t i j ^ m := by
  simp [rootChar]

theorem rootChar_add (t : I → I → kˣ) (i : I) (n n' : I →₀ ℤ) :
    Additive.toMul (rootChar t i (n + n')) =
      Additive.toMul (rootChar t i n) * Additive.toMul (rootChar t i n') := by
  rw [map_add, toMul_add]

/-! ## The root cover -/

variable {Ptwo : Prop}

/-- The datum on `X × (I →₀ ℤ)` with roots `(αᵢ, eᵢ)` and coroots `μ ↦ ⟨hᵢ, μ.1⟩`. -/
def rootCover : Datum I (X × (I →₀ ℤ)) where
  cd :=
    { root := fun i => (D.α i, Finsupp.single i 1)
      coroot := fun i => (D.cd.coroot i).comp (LinearMap.fst ℤ X (I →₀ ℤ))
      coroot_root_self := fun i => by simpa using D.cd.coroot_root_self i }
  isGCM := by
    convert D.isGCM using 1
    ext i j
    rfl
  parity := D.parity
  even_of_odd := fun i j h => D.even_of_odd i j h

@[simp] theorem fst_root (i : I) : ((rootCover D).α i).1 = D.α i := rfl

@[simp] theorem h_rootCover (i : I) (μ : X × (I →₀ ℤ)) : (rootCover D).h i μ = D.h i μ.1 := rfl

@[simp] theorem rootCover_parity (i : I) : (rootCover D).parity i = D.parity i := rfl

@[simp] theorem rootCover_d (i j : I) : (rootCover D).d i j = D.d i j := rfl

@[simp] theorem rootCover_dn (i j : I) : (rootCover D).dn i j = D.dn i j := rfl

theorem rootCover_cartanMatrix : (rootCover D).cd.cartanMatrix = D.cd.cartanMatrix := rfl

/-- The roots of the cover are independent: `Σ nⱼ (αⱼ, eⱼ) = (Σ nⱼ αⱼ, n)`. -/
theorem rootSum_rootCover (n : I →₀ ℤ) : rootSum (rootCover D) n = (rootSum D n, n) := by
  induction n using Finsupp.induction_linear with
  | zero => simp only [map_zero]; rfl
  | add n n' hn hn' => rw [map_add, hn, hn', map_add, Prod.mk_add_mk]
  | single j m =>
    rw [rootSum_single, rootSum_single]
    change (m • D.α j, m • Finsupp.single j (1 : ℤ)) = _
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem rootSum_rootCover_injective : Function.Injective (rootSum (rootCover D)) := by
  intro n n' h
  rw [rootSum_rootCover, rootSum_rootCover] at h
  exact (Prod.mk.inj h).2

/-- The same parameters on the root cover. -/
def coverScalars (Sc : ScalarData D k Ptwo) : ScalarData (rootCover D) k Ptwo where
  t := Sc.t
  t_self := Sc.t_self
  t_symm_of_d_eq_zero := Sc.t_symm_of_d_eq_zero
  s := Sc.s
  s_symm := Sc.s_symm
  s_eq_zero := Sc.s_eq_zero
  two_isUnit := Sc.two_isUnit

@[simp] theorem coverScalars_t (Sc : ScalarData D k Ptwo) : (coverScalars D Sc).t = Sc.t := rfl

@[simp] theorem coverScalars_s (Sc : ScalarData D k Ptwo) : (coverScalars D Sc).s = Sc.s := rfl

/-- The same Brundan–Wang–Webster parameters on the root cover. -/
def coverBWWScalars (Sc : BWWScalars D k) : BWWScalars (rootCover D) k where
  t := Sc.t
  t_self := Sc.t_self
  t_symm_of_d_eq_zero := Sc.t_symm_of_d_eq_zero
  c := Sc.c
  c_symm := Sc.c_symm
  c_parity := Sc.c_parity
  c_self := Sc.c_self
  c_corner := Sc.c_corner
  c_outside := Sc.c_outside
  c_top := Sc.c_top
  two_isUnit := Sc.two_isUnit

@[simp] theorem coverBWWScalars_t (Sc : BWWScalars D k) : (coverBWWScalars D Sc).t = Sc.t := rfl

@[simp] theorem coverBWWScalars_c (Sc : BWWScalars D k) : (coverBWWScalars D Sc).c = Sc.c := rfl

end OddMath.SKM.RootCover
