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

theorem probe_even (h : I → ℤ) (m : ℕ) (i : I) : Even (probeLevel h m i) := by
  exact ⟨m + (-h i).toNat, by simp [probeLevel]; omega⟩

/-- In particular this applies to every odd colour, without restricting its pairing. -/
theorem reservoir_parity (h : I → ℤ) (m : ℕ) (i : I) :
    (reservoirLevel h m i : ℤ) % 2 = h i % 2 := by
  have hd := level_difference h m i
  simp only [probeLevel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hd
  omega

/-- Both sectors grow, with the reservoir retaining the required parity. -/
theorem levels_cofinal (h : I → ℤ) (N : ℕ) :
    ∃ m, ∀ i, N ≤ probeLevel h m i ∧ N ≤ reservoirLevel h m i := by
  exact ⟨N, fun i => by simp only [probeLevel, reservoirLevel]; omega⟩

/-- The same family contains every bounded active-strand observation window. -/
theorem observation_bound (h : I → ℤ) (d n : ℕ) :
    ∃ m N, (∀ i, N ≤ reservoirLevel h m i ∧ N ≤ probeLevel h m i) ∧
      d + 2 * n.choose 2 < N := by
  let N := d + 2 * n.choose 2 + 1
  obtain ⟨m, hm⟩ := levels_cofinal h N
  exact ⟨m, N, fun i => ⟨(hm i).2, (hm i).1⟩, by omega⟩

variable {X : Type*} [AddCommGroup X] (D : SKM.Datum I X)

/-- A pairing-complete weight lattice realizes the explicit levels by weights
whose difference is literally the prescribed weight. Pairing completeness is
an additional hypothesis, not a consequence of symmetrizability. -/
theorem exists_weights_of_pairing_surjective
    (hs : Function.Surjective (fun ν : X => fun i => D.h i ν)) (μ : X) (m : ℕ) :
    ∃ μp μm : X, μm - μp = μ ∧
      (∀ i, D.h i μp = probeLevel (fun j => D.h j μ) m i) ∧
      (∀ i, D.h i μm = reservoirLevel (fun j => D.h j μ) m i) := by
  obtain ⟨ν, hν⟩ := hs (fun i => (probeLevel (fun j => D.h j μ) m i : ℤ))
  refine ⟨ν, μ + ν, by abel, ?_, ?_⟩
  · exact fun i => congrFun hν i
  · intro i
    change D.cd.coroot i (μ + ν) = _
    have hv : D.cd.coroot i ν = (probeLevel (fun j => D.h j μ) m i : ℤ) := congrFun hν i
    rw [map_add, hv]
    change D.h i μ + (probeLevel (fun j => D.h j μ) m i : ℤ) = _
    have hd := level_difference (fun j => D.h j μ) m i
    omega

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

/-- No richness assumption on the original weight lattice is needed after
adjoining independent pairing coordinates. -/
theorem pairingExtension_surjective :
    Function.Surjective (fun ν : X × (I → ℤ) => fun i => (pairingExtension D).h i ν) := by
  intro h
  refine ⟨(0, h), ?_⟩
  funext i
  simp [SKM.Datum.h, pairingExtension]

/-- Exact fixed external weight in the extended lattice, with cofinal levels
of the required parities. Restricting a categorical action along the original
weight embedding remains separate from this arithmetic assertion. -/
theorem exists_extended_weights (μ : X) (m : ℕ) :
    ∃ μp μm : X × (I → ℤ), μm - μp = (μ, 0) ∧
      (∀ i, (pairingExtension D).h i μp = probeLevel (fun j => D.h j μ) m i) ∧
      (∀ i, (pairingExtension D).h i μm = reservoirLevel (fun j => D.h j μ) m i) := by
  simpa using exists_weights_of_pairing_surjective (pairingExtension D)
    (pairingExtension_surjective D) (μ, 0) m

/-- Adding any signed root word preserves the coroot parity at an odd colour. -/
theorem odd_pairing_invariant (μ : X) (w : List (SKM.Letter I)) (i : I)
    (hi : D.parity i = 1) : D.h i (SKM.wt D μ w) % 2 = D.h i μ % 2 := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨a, ha⟩ := D.even_of_odd i l.2 hi
    simp only [SKM.wt, SKM.Datum.h, map_add, SKM.sh]
    split
    · change (D.h i (D.α l.2) + D.h i (SKM.wt D μ w)) % 2 = D.h i μ % 2
      change D.h i (D.α l.2) = a + a at ha
      omega
    · rw [map_neg]
      change (-D.h i (D.α l.2) + D.h i (SKM.wt D μ w)) % 2 = D.h i μ % 2
      change D.h i (D.α l.2) = a + a at ha
      omega

end OddMath.QuiverHecke.ReservoirWeights
