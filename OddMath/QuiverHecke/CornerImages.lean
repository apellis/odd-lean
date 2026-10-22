/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.TensorCorner

/-!
# Images of local corners

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, top step of the width
induction. The local corners of `End(E_𝐢 F_𝐢′ 1_λ)` are images of local corners of quiver Hecke
superalgebras: under the upward map `α` of (11.7), which is multiplicative, and under the
downward map `α′` of (11.8), which is defined on the super-opposite and so reverses products
up to the Koszul sign.

* `LocalCorner.map`: the image of a local corner under a linear map that is multiplicative on
  the family.
* `LocalCorner.mapAnti`: the same for a map with `Φ x * Φ y = ± Φ (y * x)`, the Koszul sign of
  the parities of `x` and `y`.
* `SuperComm.map`: supercommutation of images.
-/

namespace OddMath.SKM.GradedWalk

open scoped Pointwise

variable {k R S : Type*} [CommRing k] [Ring R] [Algebra k R] [Ring S] [Algebra k S]
  {E : Deg → Submodule k R} {ε : R} {NE : Submodule k R} {a lo : ℕ}

/-- The image family `γ ↦ Φ (E γ)`. -/
def mapFam {R : Type*} [Ring R] [Algebra k R] (Φ : R →ₗ[k] S) (E : Deg → Submodule k R)
    (γ : Deg) : Submodule k S :=
  (E γ).map Φ

theorem LocalCorner.rad_mul_rad (hE : LocalCorner E ε NE a lo) : NE * NE ≤ NE :=
  (mul_le_mul' le_rfl hE.rad_le).trans hE.rad_mul

theorem LocalCorner.pow_succ_le (hE : LocalCorner E ε NE a lo) (i : ℕ) : NE ^ (i + 1) ≤ NE := by
  induction i with
  | zero => rw [pow_one]
  | succ i ih =>
    rw [pow_succ]
    exact (mul_le_mul' ih le_rfl).trans hE.rad_mul_rad

/-- **The image of a local corner under a map that is multiplicative on it.** -/
theorem LocalCorner.map (hE : LocalCorner E ε NE a lo) (Φ : R →ₗ[k] S)
    (hΦ : ∀ {γ δ : Deg} {x y : R}, x ∈ E γ → y ∈ E δ → Φ x * Φ y = Φ (x * y)) :
    LocalCorner (mapFam Φ E) (Φ ε) (NE.map Φ) (a + 1) lo where
  mul_le γ δ := by
    refine Submodule.mul_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hΦ hx hy]
    exact Submodule.mem_map_of_mem (hE.mul_mem hx hy)
  unit_mem := Submodule.mem_map_of_mem hE.unit_mem
  unit_mul γ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hΦ hE.unit_mem hx, hE.unit_mul γ x hx]
  mul_unit γ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hΦ hx hE.unit_mem, hE.mul_unit γ x hx]
  rad_le := Submodule.map_mono hE.rad_le
  mul_rad := by
    refine Submodule.mul_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hΦ hx (hE.rad_le hy)]
    exact Submodule.mem_map_of_mem (hE.mul_rad (Submodule.mul_mem_mul hx hy))
  rad_mul := by
    refine Submodule.mul_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hΦ (hE.rad_le hx) hy]
    exact Submodule.mem_map_of_mem (hE.rad_mul (Submodule.mul_mem_mul hx hy))
  rad_pow := by
    have key : ∀ i : ℕ, NE.map Φ ^ (i + 1) ≤ (NE ^ (i + 1)).map Φ := by
      intro i
      induction i with
      | zero => rw [pow_one, pow_one]
      | succ i ih =>
        rw [pow_succ, pow_succ (NE) (i + 1)]
        refine (mul_le_mul' ih le_rfl).trans (Submodule.mul_le.2 ?_)
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [hΦ (hE.rad_le (hE.pow_succ_le i hx)) (hE.rad_le hy)]
        exact Submodule.mem_map_of_mem (Submodule.mul_mem_mul hx hy)
    refine eq_bot_iff.2 ((key a).trans ?_)
    rw [pow_succ, hE.rad_pow, Submodule.bot_mul, Submodule.map_bot]
  residue := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := hE.residue x hx
    exact ⟨c, by rw [← map_smul, ← map_sub]; exact Submodule.mem_map_of_mem hc⟩
  pair_le γ hγ := by
    refine Submodule.mul_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hΦ hx hy]
    exact Submodule.mem_map_of_mem (hE.pair_le γ hγ (Submodule.mul_mem_mul hx hy))
  eq_bot γ hγ := by rw [mapFam, hE.eq_bot γ hγ, Submodule.map_bot]

/-- **The image of a local corner under a map that reverses products up to the Koszul sign.** -/
theorem LocalCorner.mapAnti (hE : LocalCorner E ε NE a lo) (Φ : R →ₗ[k] S)
    (hΦ : ∀ {γ δ : Deg} {x y : R}, x ∈ E γ → y ∈ E δ →
      Φ x * Φ y = ksign γ.2 δ.2 • Φ (y * x)) :
    LocalCorner (mapFam Φ E) (Φ ε) (NE.map Φ) (a + 1) lo where
  mul_le γ δ := by
    refine Submodule.mul_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hΦ hx hy, ← map_zsmul]
    exact Submodule.mem_map_of_mem
      (Submodule.smul_of_tower_mem _ _ (add_comm δ γ ▸ hE.mul_mem hy hx))
  unit_mem := Submodule.mem_map_of_mem hE.unit_mem
  unit_mul γ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hΦ hE.unit_mem hx, Prod.snd_zero, ksign_zero_left, one_smul, hE.mul_unit γ x hx]
  mul_unit γ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hΦ hx hE.unit_mem, Prod.snd_zero, ksign_zero_right, one_smul, hE.unit_mul γ x hx]
  rad_le := Submodule.map_mono hE.rad_le
  mul_rad := by
    refine Submodule.mul_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hΦ hx (hE.rad_le hy), Prod.snd_zero, ksign_zero_left, one_smul]
    exact Submodule.mem_map_of_mem (hE.rad_mul (Submodule.mul_mem_mul hy hx))
  rad_mul := by
    refine Submodule.mul_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hΦ (hE.rad_le hx) hy, Prod.snd_zero, ksign_zero_left, one_smul]
    exact Submodule.mem_map_of_mem (hE.mul_rad (Submodule.mul_mem_mul hy hx))
  rad_pow := by
    have key : ∀ i : ℕ, NE.map Φ ^ (i + 1) ≤ (NE ^ (i + 1)).map Φ := by
      intro i
      induction i with
      | zero => rw [pow_one, pow_one]
      | succ i ih =>
        rw [pow_succ, pow_succ' (NE) (i + 1)]
        refine (mul_le_mul' ih le_rfl).trans (Submodule.mul_le.2 ?_)
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [hΦ (hE.rad_le (hE.pow_succ_le i hx)) (hE.rad_le hy), Prod.snd_zero,
          ksign_zero_left, one_smul]
        exact Submodule.mem_map_of_mem (Submodule.mul_mem_mul hy hx)
    refine eq_bot_iff.2 ((key a).trans ?_)
    rw [pow_succ, hE.rad_pow, Submodule.bot_mul, Submodule.map_bot]
  residue := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := hE.residue x hx
    exact ⟨c, by rw [← map_smul, ← map_sub]; exact Submodule.mem_map_of_mem hc⟩
  pair_le γ hγ := by
    refine Submodule.mul_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hΦ hx hy, ← map_zsmul]
    refine Submodule.mem_map_of_mem (Submodule.smul_of_tower_mem _ _ ?_)
    refine hE.pair_le (-γ) (neg_ne_zero.2 hγ) (Submodule.mul_mem_mul hy ?_)
    rwa [neg_neg]
  eq_bot γ hγ := by rw [mapFam, hE.eq_bot γ hγ, Submodule.map_bot]

/-- Supercommutation of images. -/
theorem SuperComm.map {R' : Type*} [Ring R'] [Algebra k R'] {F : Deg → Submodule k R'}
    (Φ : R →ₗ[k] S) (Ψ : R' →ₗ[k] S)
    (h : ∀ {γ δ : Deg} {x : R} {y : R'}, x ∈ E γ → y ∈ F δ →
      Ψ y * Φ x = ksign γ.2 δ.2 • (Φ x * Ψ y)) :
    SuperComm (mapFam Φ E) (mapFam Ψ F) := by
  rintro γ δ _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  exact h hx hy

end OddMath.SKM.GradedWalk
