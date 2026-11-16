/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing

/-! # The rational part of the same-colour braid on a mixed sector block

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5, relation
(1.9) for `Eᵢ Eᵢ Eᵢ`, in the swapped Hom construction of
`docs/Nondegeneracy/SwappedActionAssembly.md`. On a block of three paths of `Eᵢ Eᵢ Eᵢ` with
the same number of probe summands, after transporting every entry to the first path by the
mixed interchanges (`docs/Nondegeneracy/ThreeStrandSectorBraid.md`, (1)), the two crossings are
the matrices

```
U = [ D   0    0 ]       V = [ -δ   1   0 ]
    [ 0  -γ    1 ]           [ -δ²  δ   0 ]
    [ 0  -γ²   γ ]           [  0   0   D ],
```

with `D` the factor crossing and `γ`, `δ` the transported mixed coefficients. Products in a
ring `R` are read in diagrammatic order (`a * b` is `a` followed by `b`); in particular matrix
products are the composites of the crossing matrices.

* `sectorBraid`: `U V U = V U V` as soon as `D² = 0`, `D γ = δ D + γ δ`,
  `D δ = γ D - δ γ`, `γ δ² = δ² γ` and `γ² δ = δ γ²`.
* `sectorRelations_even`, `sectorRelations_odd`: these relations follow from the slides of `D`
  past the two probe dots `x₁`, `x₂`, its (super)commutation with the reservoir dot `z`, and the
  characterizing identities of `γ = a(x₁, z)` and `δ = a(q x₂, q z)`
  (`CrossCoeff.IsInverse`), at even and odd colours.

The reduction is the one of `docs/Nondegeneracy/ThreeStrandSectorBraid.md` §2, written for
the transported coefficients in this order of composition.
-/

namespace OddMath.QuiverHecke.SwappedAssembly

open Matrix

variable {R : Type*} [Ring R]

/-- The left crossing on a mixed block, transported to the first path. -/
def sectorU (D γ : R) : Matrix (Fin 3) (Fin 3) R :=
  !![D, 0, 0; 0, -γ, 1; 0, -(γ * γ), γ]

/-- The right crossing on a mixed block, transported to the first path. -/
def sectorV (D δ : R) : Matrix (Fin 3) (Fin 3) R :=
  !![-δ, 1, 0; -(δ * δ), δ, 0; 0, 0, D]

/-- **The braid relation on a mixed block**, from the five relations between the factor
crossing and the transported mixed coefficients. -/
theorem sectorBraid {D γ δ : R} (hD : D * D = 0) (hB : D * γ = δ * D + γ * δ)
    (hC : D * δ = γ * D - δ * γ) (h₁ : γ * (δ * δ) = δ * δ * γ)
    (h₂ : γ * γ * δ = δ * (γ * γ)) :
    sectorU D γ * sectorV D δ * sectorU D γ = sectorV D δ * sectorU D γ * sectorV D δ := by
  have hb : (D * γ - (δ * D + γ * δ)) = 0 := sub_eq_zero.mpr hB
  have hc : (D * δ - (γ * D - δ * γ)) = 0 := sub_eq_zero.mpr hC
  have he₁ : (γ * (δ * δ) - δ * δ * γ) = 0 := sub_eq_zero.mpr h₁
  have he₂ : (γ * γ * δ - δ * (γ * γ)) = 0 := sub_eq_zero.mpr h₂
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [sectorU, sectorV, Matrix.mul_apply, Fin.sum_univ_three] <;> simp <;>
    rw [← sub_eq_zero]
  · refine Eq.trans (b :=
      -((D * δ - (γ * D - δ * γ)) * D) - γ * (D * D) - δ * (D * δ - (γ * D - δ * γ))
       - (γ * (δ * δ) - δ * δ * γ))
      (by noncomm_ring) ?_
    simp [hc, he₁, hD]
  · refine Eq.trans (b := -(D * γ - (δ * D + γ * δ))) (by noncomm_ring) ?_
    simp [hb]
  · refine Eq.trans (b :=
      (γ * (δ * δ) - δ * δ * γ) * D - δ * δ * (D * δ - (γ * D - δ * γ))
        - δ * (γ * (δ * δ) - δ * δ * γ))
      (by noncomm_ring) ?_
    simp [hc, he₁]
  · refine Eq.trans (b :=
      -((D * γ - (δ * D + γ * δ)) * γ) - δ * (D * γ - (δ * D + γ * δ)))
      (by noncomm_ring) ?_
    simp [hb]
  · refine Eq.trans (b := (D * γ - (δ * D + γ * δ))) (by noncomm_ring) ?_
    simp [hb]
  · refine Eq.trans (b :=
      ((γ * γ * δ - δ * (γ * γ)) * δ + δ * (γ * γ * δ - δ * (γ * γ))) * D
        - ((D * γ - (δ * D + γ * δ)) * γ + δ * (D * γ - (δ * D + γ * δ))) * (δ * δ)
        - δ * δ * ((D * δ - (γ * D - δ * γ)) * δ + γ * (D * δ - (γ * D - δ * γ)))
        - γ * δ * (γ * (δ * δ) - δ * δ * γ)
        - (γ * (δ * δ) - δ * δ * γ) * δ * γ - δ * (γ * (δ * δ) - δ * δ * γ) * δ)
      (by noncomm_ring) ?_
    simp [hb, hc, he₁, he₂]
  · refine Eq.trans (b :=
      -(γ * ((D * γ - (δ * D + γ * δ)) * γ + δ * (D * γ - (δ * D + γ * δ))))
        + ((D * γ - (δ * D + γ * δ)) * γ + δ * (D * γ - (δ * D + γ * δ))) * δ
        + δ * δ * (D * δ - (γ * D - δ * γ))
        - (γ * (δ * δ) - δ * δ * γ) * D + δ * (γ * (δ * δ) - δ * δ * γ))
      (by noncomm_ring) ?_
    simp [hb, hc, he₁]
  · refine Eq.trans (b :=
      γ * (D * γ - (δ * D + γ * δ)) - (D * γ - (δ * D + γ * δ)) * D - δ * (D * D))
      (by noncomm_ring) ?_
    simp [hb, hD]

/-! ## The relations from the dot algebra -/

/-- **The relations at an even colour.** `x₁`, `x₂` are the probe dots of the repeated
factor, `z` the reservoir dot, `γ = (z - x₁)⁻¹` and `δ = (z - x₂)⁻¹`. -/
theorem sectorRelations_even {D x₁ x₂ z γ δ : R} (h12 : x₁ * x₂ = x₂ * x₁)
    (h1z : x₁ * z = z * x₁) (h2z : x₂ * z = z * x₂) (hDz : D * z = z * D)
    (hs₁ : x₁ * D - D * x₂ = 1) (hs₂ : D * x₁ - x₂ * D = 1)
    (hγ₁ : γ * (z - x₁) = 1) (hγ₂ : (z - x₁) * γ = 1)
    (hδ₁ : δ * (z - x₂) = 1) (hδ₂ : (z - x₂) * δ = 1) :
    D * γ = δ * D + γ * δ ∧ D * δ = γ * D - δ * γ ∧ γ * (δ * δ) = δ * δ * γ ∧
      γ * γ * δ = δ * (γ * γ) := by
  let u₁ : Rˣ := ⟨z - x₁, γ, hγ₂, hγ₁⟩
  let u₂ : Rˣ := ⟨z - x₂, δ, hδ₂, hδ₁⟩
  have hc : Commute (u₁ : R) u₂ := by
    show (z - x₁) * (z - x₂) = (z - x₂) * (z - x₁)
    simp only [mul_sub, sub_mul, h12, h1z, h2z]
    abel
  have hγδ : Commute γ δ := hc.units_inv_left.units_inv_right
  have hD₁ : D * (z - x₁) = (z - x₂) * D - 1 := by
    rw [mul_sub, hDz, ← hs₂]; noncomm_ring
  have hD₂ : D * (z - x₂) = (z - x₁) * D + 1 := by
    rw [mul_sub, hDz, ← hs₁]; noncomm_ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc D * γ = δ * ((z - x₂) * D - 1 + 1) * γ := by
          rw [sub_add_cancel, ← mul_assoc, hδ₁, one_mul]
      _ = δ * D * ((z - x₁) * γ) + δ * γ := by rw [← hD₁]; noncomm_ring
      _ = δ * D + γ * δ := by rw [hγ₂, mul_one, hγδ.eq]
  · calc D * δ = γ * ((z - x₁) * D + 1 - 1) * δ := by
          rw [add_sub_cancel_right, ← mul_assoc, hγ₁, one_mul]
      _ = γ * D * ((z - x₂) * δ) - γ * δ := by rw [← hD₂]; noncomm_ring
      _ = γ * D - δ * γ := by rw [hδ₂, mul_one, hγδ.eq]
  · exact (hγδ.mul_right hγδ)
  · exact hγδ.mul_left hγδ

private theorem commute_sq_of_anti {a b : R} (h : a * b = -(b * a)) : Commute (a * a) b := by
  show a * a * b = b * (a * a)
  rw [mul_assoc, h, mul_neg, ← mul_assoc, h, neg_mul, neg_neg, mul_assoc]

private theorem anti_symm {a b : R} (h : a * b = -(b * a)) : b * a = -(a * b) := by
  rw [h, neg_neg]

/-- **The relations at an odd colour.** `x₁`, `x₂` are the probe dots of the repeated factor
and `z` the reservoir dot, pairwise anticommuting; `γ = (x₁ - z)(x₁² - z²)⁻¹` and
`δ = (z - x₂)(x₂² - z²)⁻¹`, the coefficient at the dots `-x₂`, `-z`. -/
theorem sectorRelations_odd {D x₁ x₂ z γ δ : R} (h12 : x₁ * x₂ = -(x₂ * x₁))
    (h1z : x₁ * z = -(z * x₁)) (h2z : x₂ * z = -(z * x₂)) (hDz : D * z = -(z * D))
    (hs₁ : x₁ * D + D * x₂ = 1) (hs₂ : D * x₁ + x₂ * D = 1)
    (hN₁ : IsUnit (x₁ * x₁ - z * z)) (hN₂ : IsUnit (x₂ * x₂ - z * z))
    (hγ₁ : γ * (x₁ * x₁ - z * z) = x₁ - z)
    (hδ₁ : δ * (x₂ * x₂ - z * z) = z - x₂) :
    D * γ = δ * D + γ * δ ∧ D * δ = γ * D - δ * γ ∧ γ * (δ * δ) = δ * δ * γ ∧
      γ * γ * δ = δ * (γ * γ) := by
  obtain ⟨u₁, hu₁⟩ := hN₁
  obtain ⟨u₂, hu₂⟩ := hN₂
  have c11 : Commute (x₁ * x₁) x₁ := (Commute.refl x₁).mul_left (Commute.refl x₁)
  have c1z : Commute (x₁ * x₁) z := commute_sq_of_anti h1z
  have c12 : Commute (x₁ * x₁) x₂ := commute_sq_of_anti h12
  have cz1 : Commute (z * z) x₁ := commute_sq_of_anti (anti_symm h1z)
  have czz : Commute (z * z) z := (Commute.refl z).mul_left (Commute.refl z)
  have cz2 : Commute (z * z) x₂ := commute_sq_of_anti (anti_symm h2z)
  have c21 : Commute (x₂ * x₂) x₁ := commute_sq_of_anti (anti_symm h12)
  have c2z : Commute (x₂ * x₂) z := commute_sq_of_anti h2z
  have c22 : Commute (x₂ * x₂) x₂ := (Commute.refl x₂).mul_left (Commute.refl x₂)
  have n1x1 : Commute (u₁ : R) x₁ := hu₁ ▸ c11.sub_left cz1
  have n1z : Commute (u₁ : R) z := hu₁ ▸ c1z.sub_left czz
  have n1x2 : Commute (u₁ : R) x₂ := hu₁ ▸ c12.sub_left cz2
  have n2x1 : Commute (u₂ : R) x₁ := hu₂ ▸ c21.sub_left cz1
  have n2z : Commute (u₂ : R) z := hu₂ ▸ c2z.sub_left czz
  have n2x2 : Commute (u₂ : R) x₂ := hu₂ ▸ c22.sub_left cz2
  have n12 : Commute (u₁ : R) u₂ := by
    rw [hu₂]; exact (n1x2.mul_right n1x2).sub_right (n1z.mul_right n1z)
  have hγ : γ = (x₁ - z) * ↑u₁⁻¹ := by rw [← hγ₁, ← hu₁, Units.mul_inv_cancel_right]
  have hδ : δ = (z - x₂) * ↑u₂⁻¹ := by rw [← hδ₁, ← hu₂, Units.mul_inv_cancel_right]
  -- `γ` commutes with `x₂`-free data of the other factor and conversely
  have γu₂ : Commute γ u₂ := by
    rw [hγ]; exact (n2x1.sub_right n2z).symm.mul_left n12.units_inv_left
  have δu₁ : Commute δ u₁ := by
    rw [hδ]; exact (n1z.sub_right n1x2).symm.mul_left n12.symm.units_inv_left
  -- the slides past the squared dots
  have hDx₁ : D * x₁ = 1 - x₂ * D := eq_sub_of_add_eq hs₂
  have hDx₂ : D * x₂ = 1 - x₁ * D := eq_sub_of_add_eq' hs₁
  have hDN₁ : D * u₁ = u₂ * D + (x₁ - x₂) := by
    rw [hu₁, hu₂]
    calc D * (x₁ * x₁ - z * z) = D * x₁ * x₁ - D * z * z := by noncomm_ring
      _ = (1 - x₂ * D) * x₁ - -(z * D) * z := by rw [hDx₁, hDz]
      _ = x₁ - x₂ * (D * x₁) + z * (D * z) := by noncomm_ring
      _ = (x₂ * x₂ - z * z) * D + (x₁ - x₂) := by rw [hDx₁, hDz]; noncomm_ring
  have hDN₂ : D * u₂ = u₁ * D + (x₂ - x₁) := by
    rw [hu₁, hu₂]
    calc D * (x₂ * x₂ - z * z) = D * x₂ * x₂ - D * z * z := by noncomm_ring
      _ = (1 - x₁ * D) * x₂ - -(z * D) * z := by rw [hDx₂, hDz]
      _ = x₂ - x₁ * (D * x₂) + z * (D * z) := by noncomm_ring
      _ = (x₁ * x₁ - z * z) * D + (x₂ - x₁) := by rw [hDx₂, hDz]; noncomm_ring
  have hδu₂ : δ * u₂ = z - x₂ := hu₂ ▸ hδ₁
  have hγu₁ : γ * u₁ = x₁ - z := hu₁ ▸ hγ₁
  have key₁ : δ * (x₁ - x₂) + (x₁ - z) * δ = 1 := by
    apply (Units.mul_left_inj u₂).mp
    have e : (x₁ - x₂) * u₂ = u₂ * (x₁ - x₂) := (n2x1.sub_right n2x2).eq.symm
    rw [add_mul, mul_assoc, e, ← mul_assoc, hδu₂, mul_assoc, hδu₂, one_mul, hu₂]
    simp only [mul_sub, sub_mul, h1z, h12]
    noncomm_ring
  have key₂ : γ * (x₁ - x₂) + (z - x₂) * γ = 1 := by
    apply (Units.mul_left_inj u₁).mp
    have e : (x₁ - x₂) * u₁ = u₁ * (x₁ - x₂) := (n1x1.sub_right n1x2).eq.symm
    rw [add_mul, mul_assoc, e, ← mul_assoc, hγu₁, mul_assoc, hγu₁, one_mul, hu₁]
    simp only [mul_sub, sub_mul, h12, h2z]
    noncomm_ring
  have hδδ : δ * δ = (z * z + x₂ * x₂) * ↑u₂⁻¹ * ↑u₂⁻¹ := by
    have e : Commute (z - x₂) (↑u₂⁻¹ : R) := (n2z.sub_right n2x2).symm.units_inv_right
    calc δ * δ = (z - x₂) * (↑u₂⁻¹ * (z - x₂)) * ↑u₂⁻¹ := by rw [hδ]; noncomm_ring
      _ = (z - x₂) * (z - x₂) * ↑u₂⁻¹ * ↑u₂⁻¹ := by rw [← e.eq]; noncomm_ring
      _ = (z * z + x₂ * x₂) * ↑u₂⁻¹ * ↑u₂⁻¹ := by
          congr 2; simp only [mul_sub, sub_mul, h2z]; noncomm_ring
  have hγγ : γ * γ = (x₁ * x₁ + z * z) * ↑u₁⁻¹ * ↑u₁⁻¹ := by
    have e : Commute (x₁ - z) (↑u₁⁻¹ : R) := (n1x1.sub_right n1z).symm.units_inv_right
    calc γ * γ = (x₁ - z) * (↑u₁⁻¹ * (x₁ - z)) * ↑u₁⁻¹ := by rw [hγ]; noncomm_ring
      _ = (x₁ - z) * (x₁ - z) * ↑u₁⁻¹ * ↑u₁⁻¹ := by rw [← e.eq]; noncomm_ring
      _ = (x₁ * x₁ + z * z) * ↑u₁⁻¹ * ↑u₁⁻¹ := by
          congr 2; simp only [mul_sub, sub_mul, h1z]; noncomm_ring
  have cW₂ : Commute γ (z * z + x₂ * x₂) := by
    have h1 : Commute (z * z + x₂ * x₂) (x₁ - z) :=
      (cz1.add_left c21).sub_right (czz.add_left c2z)
    have h2 : Commute (z * z + x₂ * x₂) (u₁ : R) := by
      rw [hu₁]
      exact ((cz1.mul_right cz1).add_left (c21.mul_right c21)).sub_right
        ((Commute.refl _).add_left (c2z.mul_right c2z))
    rw [hγ]; exact (h1.mul_right h2.units_inv_right).symm
  have cW₁ : Commute δ (x₁ * x₁ + z * z) := by
    have h1 : Commute (x₁ * x₁ + z * z) (z - x₂) :=
      (c1z.add_left czz).sub_right (c12.add_left cz2)
    have h2 : Commute (x₁ * x₁ + z * z) (u₂ : R) := by
      rw [hu₂]
      exact ((c12.mul_right c12).add_left (cz2.mul_right cz2)).sub_right
        ((c1z.mul_right c1z).add_left (Commute.refl _))
    rw [hδ]; exact (h1.mul_right h2.units_inv_right).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (Units.mul_left_inj u₁).mp
    calc D * γ * u₁ = D * x₁ - D * z := by rw [mul_assoc, hγu₁, mul_sub]
      _ = δ * u₂ * D + (δ * (x₁ - x₂) + (x₁ - z) * δ) := by
          rw [hDx₁, hDz, hδu₂, key₁]; noncomm_ring
      _ = (δ * D + γ * δ) * u₁ := by
          rw [add_mul, mul_assoc δ D, hDN₁, mul_assoc γ δ, δu₁.eq, ← mul_assoc γ,
            hγu₁]
          noncomm_ring
  · apply (Units.mul_left_inj u₂).mp
    calc D * δ * u₂ = D * z - D * x₂ := by rw [mul_assoc, hδu₂, mul_sub]
      _ = γ * u₁ * D - (γ * (x₁ - x₂) + (z - x₂) * γ) := by
          rw [hDx₂, hDz, hγu₁, key₂]; noncomm_ring
      _ = (γ * D - δ * γ) * u₂ := by
          rw [sub_mul (γ * D), mul_assoc γ D, hDN₂, mul_assoc δ γ, γu₂.eq, ← mul_assoc δ,
            hδu₂]
          noncomm_ring
  · have cu : Commute γ (↑u₂⁻¹ : R) := γu₂.units_inv_right
    rw [hδδ]; exact ((cW₂.mul_right cu).mul_right cu).eq
  · have cu : Commute δ (↑u₁⁻¹ : R) := δu₁.units_inv_right
    rw [hγγ]; exact (((cW₁.mul_right cu).mul_right cu).eq).symm

end OddMath.QuiverHecke.SwappedAssembly
