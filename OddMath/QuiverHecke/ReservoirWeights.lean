/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Basic

/-! # Cofinal reservoir and probe levels

Ports the balancing arithmetic of
`Categorification/KLR/Unfurling/GenericWeights.lean` (`sum_level_difference`).
The probe levels are even, whereas reservoir levels have the parity of the
prescribed coroot pairing. These are levels on the cover, not assertions that
an arbitrary weight lattice contains all dominant pairing vectors.
-/

namespace OddMath.QuiverHecke.ReservoirWeights

variable {I : Type*}

/-- An even probe cutoff, including the negative part of the prescribed pairing. -/
def probeLevel (h : I → ℤ) (m : ℕ) (i : I) : ℕ :=
  2 * m + 2 * (-h i).toNat

/-- The connected reservoir cutoff; its parity need not be even. -/
def reservoirLevel (h : I → ℤ) (m : ℕ) (i : I) : ℕ :=
  2 * m + (h i).toNat + (-h i).toNat

/-- Balancing changes neither the external pairing nor the cofinal parameter. -/
theorem level_difference (h : I → ℤ) (m : ℕ) (i : I) :
    (reservoirLevel h m i : ℤ) - probeLevel h m i = h i := by
  simp only [reservoirLevel, probeLevel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

/-- In particular this applies to every odd colour, without restricting its pairing. -/
theorem reservoir_parity (h : I → ℤ) (m : ℕ) (i : I) :
    (reservoirLevel h m i : ℤ) % 2 = h i % 2 := by
  have hd := level_difference h m i
  simp only [probeLevel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hd
  omega

variable {X : Type*} [AddCommGroup X] (D : SKM.Datum I X)

/-- Add independent coroot coordinates while preserving the roots, Cartan
matrix, and parity. The original weights embed by `μ ↦ (μ, 0)`. -/
def pairingExtension : SKM.Datum I (X × (I → ℤ)) where
  cd :=
    { root := fun i => (D.α i, 0)
      coroot := fun i =>
        { toFun := fun ν => D.h i ν.1 + ν.2 i
          map_add' := by intros; simp [SKM.Datum.h]; abel
          map_smul' := by intros; simp [SKM.Datum.h, mul_add] }
      coroot_root_self := by intro i; simpa using D.cd.coroot_root_self i }
  isGCM := by
    simpa [CartanDatum.cartanMatrix] using D.isGCM
  parity := D.parity
  even_of_odd := by
    intro i j hij
    simpa using D.even_of_odd i j hij

@[simp] theorem pairingExtension_h (i : I) (ν : X × (I → ℤ)) :
    (pairingExtension D).h i ν = D.h i ν.1 + ν.2 i := rfl

@[simp] theorem pairingExtension_cartanMatrix :
    (pairingExtension D).cd.cartanMatrix = D.cd.cartanMatrix := by
  ext i j
  simp [CartanDatum.cartanMatrix_apply, pairingExtension, SKM.Datum.h, SKM.Datum.α]

end OddMath.QuiverHecke.ReservoirWeights
