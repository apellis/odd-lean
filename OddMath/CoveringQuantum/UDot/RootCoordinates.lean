/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.Datum

/-!
# Root coordinates on the weight lattice

Supporting material for the nondegeneracy theorem of Brundan–Ellis, arXiv:1701.04133v2,
Theorem 10.1, whose proof compares weights differing by sums of simple roots.

When the simple roots `αᵢ` of a root datum are linearly independent over `ℤ`, every weight `μ`
is uniquely of the form `rootCosetRep μ + Σⱼ nⱼ αⱼ`, where `rootCosetRep μ` is a fixed
representative of the coset `μ + ℤ[I]` of the root lattice. The coefficients `nⱼ` are the root
coordinates `rootCoord D hα μ : I →₀ ℤ`.

## Main definitions

* `RootDatum.rootLattice`: the `ℤ`-span of the simple roots.
* `RootDatum.rootCosetRep`: a chosen representative of the root-lattice coset of a weight.
* `RootDatum.rootCoord`: the coordinates of `μ - rootCosetRep μ` in the basis `(αᵢ)`.

## Main results

* `RootDatum.rootCoord_add_α`, `RootDatum.rootCoord_sub_α`,
  `RootDatum.rootCoord_add_linearCombination`: adding roots shifts the coordinates.
* `RootDatum.rootCosetRep_add_linearCombination_rootCoord`: `μ` is recovered from its
  representative and its coordinates.
* `RootDatum.h_eq_rootCosetRep_add_sum`: `⟨hᵢ, μ⟩ = ⟨hᵢ, rep μ⟩ + Σⱼ nⱼ aᵢⱼ`.
-/

noncomputable section

namespace OddMath.CoveringQuantum.RootDatum

variable {I X : Type*} [AddCommGroup X] (D : RootDatum I X)

/-- The root lattice `ℤ[I] ⊆ X`, the `ℤ`-span of the simple roots. -/
abbrev rootLattice : Submodule ℤ X := Submodule.span ℤ (Set.range D.α)

theorem α_mem_rootLattice (j : I) : D.α j ∈ D.rootLattice :=
  Submodule.subset_span ⟨j, rfl⟩

/-- A chosen representative of the coset `μ + ℤ[I]`. -/
def rootCosetRep (μ : X) : X :=
  Function.surjInv D.rootLattice.mkQ_surjective (D.rootLattice.mkQ μ)

theorem mkQ_rootCosetRep (μ : X) : D.rootLattice.mkQ (D.rootCosetRep μ) = D.rootLattice.mkQ μ :=
  Function.surjInv_eq _ _

theorem sub_rootCosetRep_mem (μ : X) : μ - D.rootCosetRep μ ∈ D.rootLattice := by
  rw [← Submodule.Quotient.eq]
  exact (D.mkQ_rootCosetRep μ).symm

theorem rootCosetRep_eq_of_sub_mem {μ ν : X} (h : μ - ν ∈ D.rootLattice) :
    D.rootCosetRep μ = D.rootCosetRep ν := by
  unfold rootCosetRep
  congr 1
  exact (Submodule.Quotient.eq _).2 h

theorem rootCosetRep_add_of_mem (μ : X) {x : X} (hx : x ∈ D.rootLattice) :
    D.rootCosetRep (μ + x) = D.rootCosetRep μ :=
  D.rootCosetRep_eq_of_sub_mem (by simpa using hx)

@[simp]
theorem rootCosetRep_rootCosetRep (μ : X) : D.rootCosetRep (D.rootCosetRep μ) = D.rootCosetRep μ :=
  D.rootCosetRep_eq_of_sub_mem (by
    rw [← neg_mem_iff, neg_sub]; exact D.sub_rootCosetRep_mem μ)

@[simp]
theorem rootCosetRep_add_α (μ : X) (j : I) : D.rootCosetRep (μ + D.α j) = D.rootCosetRep μ :=
  D.rootCosetRep_add_of_mem μ (D.α_mem_rootLattice j)

variable (hα : LinearIndependent ℤ D.α)

/-- The root coordinates of a weight: the coefficients of `μ - rootCosetRep μ` in the basis
`(αᵢ)` of the root lattice. -/
def rootCoord (μ : X) : I →₀ ℤ :=
  hα.repr ⟨μ - D.rootCosetRep μ, D.sub_rootCosetRep_mem μ⟩

theorem rootCoord_add_of_mem (μ : X) {x : X} (hx : x ∈ D.rootLattice) :
    D.rootCoord hα (μ + x) = D.rootCoord hα μ + hα.repr ⟨x, hx⟩ := by
  unfold rootCoord
  rw [← map_add]
  congr 1
  ext
  simp only [D.rootCosetRep_add_of_mem μ hx, Submodule.coe_add]
  abel

@[simp]
theorem rootCoord_add_α (μ : X) (j : I) :
    D.rootCoord hα (μ + D.α j) = D.rootCoord hα μ + Finsupp.single j 1 := by
  rw [D.rootCoord_add_of_mem hα μ (D.α_mem_rootLattice j)]
  congr 1
  exact hα.repr_eq_single j _ rfl

@[simp]
theorem rootCoord_sub_α (μ : X) (j : I) :
    D.rootCoord hα (μ - D.α j) = D.rootCoord hα μ - Finsupp.single j 1 := by
  have := D.rootCoord_add_α hα (μ - D.α j) j
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

theorem rootCoord_add_linearCombination (μ : X) (n : I →₀ ℤ) :
    D.rootCoord hα (μ + Finsupp.linearCombination ℤ D.α n) = D.rootCoord hα μ + n := by
  have hx : Finsupp.linearCombination ℤ D.α n ∈ D.rootLattice := by
    change _ ∈ Submodule.span ℤ (Set.range D.α)
    rw [← Finsupp.range_linearCombination]; exact LinearMap.mem_range_self _ n
  rw [D.rootCoord_add_of_mem hα μ hx]
  congr 1
  exact hα.repr_eq rfl

@[simp]
theorem rootCoord_rootCosetRep (μ : X) : D.rootCoord hα (D.rootCosetRep μ) = 0 := by
  unfold rootCoord
  rw [← map_zero hα.repr]
  congr 1
  ext
  simp

/-- A weight is its coset representative plus the combination of simple roots given by its root
coordinates. -/
theorem rootCosetRep_add_linearCombination_rootCoord (μ : X) :
    D.rootCosetRep μ + Finsupp.linearCombination ℤ D.α (D.rootCoord hα μ) = μ := by
  unfold rootCoord
  rw [hα.linearCombination_repr]
  exact add_sub_cancel _ _

/-- Two weights in the same root-lattice coset with the same root coordinates are equal. -/
theorem eq_of_rootCoord_eq {μ ν : X} (hc : D.rootCosetRep μ = D.rootCosetRep ν)
    (h : D.rootCoord hα μ = D.rootCoord hα ν) : μ = ν := by
  rw [← D.rootCosetRep_add_linearCombination_rootCoord hα μ,
    ← D.rootCosetRep_add_linearCombination_rootCoord hα ν, hc, h]

/-- On each root-lattice coset, `⟨hᵢ, -⟩` is affine in the root coordinates:
`⟨hᵢ, μ⟩ = ⟨hᵢ, rootCosetRep μ⟩ + Σⱼ nⱼ aᵢⱼ`. -/
theorem h_eq_rootCosetRep_add_sum (i : I) (μ : X) :
    D.h i μ = D.h i (D.rootCosetRep μ) + (D.rootCoord hα μ).sum fun j c => c * D.a i j := by
  conv_lhs => rw [← D.rootCosetRep_add_linearCombination_rootCoord hα μ]
  show D.cd.coroot i _ = D.cd.coroot i _ + _
  rw [map_add, Finsupp.linearCombination_apply, map_finsuppSum]
  congr 1
  refine Finsupp.sum_congr fun j _ => ?_
  rw [map_zsmul, smul_eq_mul]
  exact congrArg _ (D.h_α i j)

end OddMath.CoveringQuantum.RootDatum
