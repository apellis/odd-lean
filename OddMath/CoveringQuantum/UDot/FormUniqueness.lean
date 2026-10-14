/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.UDot.RhoHalfWords
import OddMath.CoveringQuantum.UDot.Triangular

/-!
# Uniqueness of rho-adjoint forms on the modified algebra over any coefficient ring

Supporting material for the nondegeneracy theorem of Brundan–Ellis, arXiv:1701.04133v2,
Theorem 10.1, which concerns the bilinear form on `U̇` that is adjoint for `ρ`.

Over any commutative ring `k`, with `q : kˣ` and `π² = 1`, two bilinear maps
`modified D q π × modified D q π → M` into an arbitrary `k`-module that are both left
`ρ`-adjoint (`B (u x) y = B x (ρ(u) y)`) and agree on all pairs of positive words
`E_a 1_μ, E_b 1_ν` agree everywhere (`forms_eq_of_positiveWord`). The proof uses
FE triangular spanning of the modified algebra (`triangularSpan_eq_modified`), the
reversal of half words by `ρ` up to a unit (`rho_halfWord_unit`), and finite local units
(`exists_localUnit`). No independence of the simple roots is assumed.

This generalizes `GenericTensor.forms_eq_of_positive_words`, which is stated over the generic
covering ring only.

## Main definitions

* `UDot.positiveWord`, `UDot.negativeWord`: the half words `E_a 1_μ` and `F_a 1_μ` as elements
  of the modified algebra.

## Main results

* `UDot.forms_eq_of_positiveWord`.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot

open PreF

variable {k I X : Type*} [CommRing k] [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X) (q : kˣ) (π : k)

/-- The positive half word `E_a 1_μ` as an element of the modified algebra. -/
def positiveWord (a : List I) (μ : X) : modified D q π :=
  ⟨halfWord D q π true a μ, block_le_modified D q π _ _ (halfWord_mem_block D q π true a μ)⟩

/-- The negative half word `F_a 1_μ` as an element of the modified algebra. -/
def negativeWord (a : List I) (μ : X) : modified D q π :=
  ⟨halfWord D q π false a μ, block_le_modified D q π _ _ (halfWord_mem_block D q π false a μ)⟩

@[simp]
theorem coe_positiveWord (a : List I) (μ : X) :
    (positiveWord D q π a μ : CoveringUDot k D q π) = halfWord D q π true a μ := rfl

@[simp]
theorem coe_negativeWord (a : List I) (μ : X) :
    (negativeWord D q π a μ : CoveringUDot k D q π) = halfWord D q π false a μ := rfl

/-- The idempotent `1_μ` as an element of the modified algebra. -/
private def weightUnit (μ : X) : modified D q π :=
  ⟨one D q π μ, one_mem_modified D q π μ⟩

/-- Linear maps out of the modified algebra are determined by their values on the FE
triangular products `F_a 1_μ E_b 1_ν`. -/
private theorem linearMap_ext_negative_mul_positive {M : Type*} [AddCommGroup M] [Module k M]
    (f g : modified D q π →ₗ[k] M)
    (h : ∀ a b μ ν, f (negativeWord D q π a μ * positiveWord D q π b ν) =
      g (negativeWord D q π a μ * positiveWord D q π b ν)) : f = g := by
  ext x
  have mem : ∀ z ∈ triangularSpan D q π, z ∈ modified D q π := by
    intro z hz
    change z ∈ (modified D q π).toSubmodule
    rwa [← triangularSpan_eq_modified]
  have aux : ∀ z ∈ triangularSpan D q π, ∀ hz : z ∈ modified D q π,
      f ⟨z, hz⟩ = g ⟨z, hz⟩ := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, b, μ, ν, rfl⟩ := hz
      intro _
      exact h a b μ ν
    | zero => intro _; exact (map_zero f).trans (map_zero g).symm
    | add z w hz hw ihz ihw =>
      intro _
      change f (⟨z, mem z hz⟩ + ⟨w, mem w hw⟩) = g (⟨z, mem z hz⟩ + ⟨w, mem w hw⟩)
      simp only [map_add, ihz (mem z hz), ihw (mem w hw)]
    | smul c z hz ih =>
      intro _
      change f (c • ⟨z, mem z hz⟩) = g (c • ⟨z, mem z hz⟩)
      simp only [map_smul, ih (mem z hz)]
  have hx : (x : CoveringUDot k D q π) ∈ triangularSpan D q π := by
    rw [triangularSpan_eq_modified]
    exact x.property
  exact aux _ hx x.property

/-- Two left `ρ`-adjoint bilinear maps on the modified algebra, with values in any `k`-module,
that agree on all pairs of positive words `E_a 1_μ, E_b 1_ν` are equal. No independence of the
simple roots is assumed. -/
theorem forms_eq_of_positiveWord (hπ : π ^ 2 = 1) {M : Type*} [AddCommGroup M] [Module k M]
    (B C : modified D q π →ₗ[k] modified D q π →ₗ[k] M)
    (hB : ∀ u x y, B (u * x) y = B x (rhoModified D q π hπ u * y))
    (hC : ∀ u x y, C (u * x) y = C x (rhoModified D q π hπ u * y))
    (hpositive : ∀ a b μ ν,
      B (positiveWord D q π a μ) (positiveWord D q π b ν) =
        C (positiveWord D q π a μ) (positiveWord D q π b ν)) : B = C := by
  have hunit (η : X) : B (weightUnit D q π η) = C (weightUnit D q π η) := by
    apply linearMap_ext_negative_mul_positive D q π
    intro a b μ ν
    obtain ⟨c, hc⟩ := rho_halfWord_unit D q π hπ false a μ
    have hr : rhoModified D q π hπ (negativeWord D q π a μ) =
        (c : k) • positiveWord D q π a.reverse (μ + halfWeight D false (wordWeight a)) :=
      Subtype.ext hc
    have he (F : modified D q π →ₗ[k] modified D q π →ₗ[k] M)
        (hF : ∀ u x y, F (u * x) y = F x (rhoModified D q π hπ u * y)) :
        F (weightUnit D q π η) (negativeWord D q π a μ * positiveWord D q π b ν) =
          F (rhoModified D q π hπ (negativeWord D q π a μ) * weightUnit D q π η)
            (positiveWord D q π b ν) := by
      rw [hF, rhoModified_rhoModified]
    rw [he B hB, he C hC, hr, smul_mul_assoc]
    have hm : positiveWord D q π a.reverse (μ + halfWeight D false (wordWeight a)) *
          weightUnit D q π η =
        if μ + halfWeight D false (wordWeight a) = η then
          positiveWord D q π a.reverse (μ + halfWeight D false (wordWeight a)) else 0 := by
      apply Subtype.ext
      simpa only [positiveWord, weightUnit, NonUnitalSubalgebra.coe_mul, apply_ite,
        NonUnitalSubalgebra.coe_zero] using
        mul_one_of_mem_block D q π
          (halfWord_mem_block D q π true a.reverse (μ + halfWeight D false (wordWeight a))) η
    rw [hm]
    split_ifs <;> simp [hpositive]
  ext x y
  obtain ⟨s, _, hs⟩ := exists_localUnit D q π x.property
  have hx : x * ∑ η ∈ s, weightUnit D q π η = x := by
    apply Subtype.ext
    change (x : CoveringUDot k D q π) *
      (modified D q π).toSubmodule.subtype (∑ η ∈ s, weightUnit D q π η) = _
    simpa only [map_sum, Submodule.subtype_apply, weightUnit] using hs
  calc
    B x y = B (x * ∑ η ∈ s, weightUnit D q π η) y := by rw [hx]
    _ = B (∑ η ∈ s, weightUnit D q π η) (rhoModified D q π hπ x * y) := hB _ _ _
    _ = C (∑ η ∈ s, weightUnit D q π η) (rhoModified D q π hπ x * y) := by
      simp only [map_sum, LinearMap.sum_apply, hunit]
    _ = C (x * ∑ η ∈ s, weightUnit D q π η) y := (hC _ _ _).symm
    _ = C x y := by rw [hx]

end OddMath.CoveringQuantum.UDot
