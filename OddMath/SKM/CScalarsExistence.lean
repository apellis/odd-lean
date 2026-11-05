/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.MoreGenerators

/-!
# Existence of the normalizations `c_{λ;i}` (Brundan–Ellis (1.17))

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, (1.17), choose units
`c_{λ;i}` with `c_{λ+αⱼ;i} = tᵢⱼ c_{λ;i}`. This file shows that such a choice exists whenever the
simple roots are linearly independent over `ℤ` in the weight group `X`, which is the case in the
paper's setting (the `αᵢ` are linearly independent in `𝔥*`). The construction picks a
representative of each coset of the root lattice and multiplies the `tᵢⱼ` along the root-lattice
coordinates of `λ` minus its representative.

Without linear independence such a choice need not exist: if `α₀ + α₁ = 0` in `X`, then the
shift law forces `tᵢ₀ tᵢ₁ = 1` for every `i`. Theorems quantified over `cs : CScalars Sc` are
therefore only meaningful for data where a choice exists, and the existence statement below
records that this includes every datum with linearly independent simple roots.

## Main results

* `SKM.exists_shift_family`: a family `c : X → I → G` with `c (μ + αⱼ) i = tᵢⱼ c μ i`, for any
  commutative group `G` and linearly independent `α`.
* `SKM.CScalars.nonempty_of_linearIndependent`: `CScalars Sc` is nonempty when the simple roots
  are linearly independent over `ℤ`.
-/

namespace OddMath.SKM

universe u v w

section Generic

variable {I : Type u} {X : Type v} {G : Type w} [AddCommGroup X] [CommGroup G]

/-- Given `ℤ`-linearly independent `αⱼ ∈ X` and elements `tᵢⱼ` of a commutative group, there is a
family `c : X → I → G` with `c (μ + αⱼ) i = tᵢⱼ c μ i` for all `μ`, `i`, `j`. -/
theorem exists_shift_family (α : I → X) (hα : LinearIndependent ℤ α) (t : I → I → G) :
    ∃ c : X → I → G, ∀ μ i j, c (μ + α j) i = t i j * c μ i := by
  classical
  let Φ : (I →₀ ℤ) →+ X := (Finsupp.linearCombination ℤ α).toAddMonoidHom
  have hΦ : Function.Injective Φ := hα
  have hΦs : ∀ j, Φ (Finsupp.single j 1) = α j := fun j => by
    simp [Φ, Finsupp.linearCombination_single]
  let Q : AddSubgroup X := Φ.range
  let r : X → X := fun μ => (QuotientAddGroup.mk (s := Q) μ).out
  have hr : ∀ μ, -r μ + μ ∈ Q := fun μ =>
    QuotientAddGroup.eq.mp (Quotient.out_eq (QuotientAddGroup.mk (s := Q) μ))
  let e := AddMonoidHom.ofInjective hΦ
  let f : X → I →₀ ℤ := fun μ => e.symm ⟨-r μ + μ, hr μ⟩
  have hf : ∀ μ, Φ (f μ) = -r μ + μ := fun μ =>
    congrArg Subtype.val (e.apply_symm_apply ⟨-r μ + μ, hr μ⟩)
  have hrs : ∀ μ j, r (μ + α j) = r μ := fun μ j => by
    have : (QuotientAddGroup.mk (s := Q) (μ + α j)) = QuotientAddGroup.mk μ := by
      rw [QuotientAddGroup.eq]
      exact ⟨-Finsupp.single j 1, by rw [map_neg, hΦs]; abel⟩
    simp only [r, this]
  have hfs : ∀ μ j, f (μ + α j) = f μ + Finsupp.single j 1 := fun μ j => by
    apply hΦ
    rw [map_add, hf, hf, hΦs, hrs]; abel
  refine ⟨fun μ i => (f μ).prod fun j n => t i j ^ n, fun μ i j => ?_⟩
  simp only
  rw [hfs, Finsupp.prod_add_index (fun _ _ => zpow_zero _) (fun _ _ _ _ => zpow_add _ _ _),
    Finsupp.prod_single_index (zpow_zero _), zpow_one, mul_comm]

end Generic

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]

/-- **Normalizations exist** (Brundan–Ellis (1.17)): if the simple roots are linearly
independent over `ℤ` in the weight group, then units `c_{λ;i}` with `c_{λ+αⱼ;i} = tᵢⱼ c_{λ;i}`
exist, for arbitrary scalars `tᵢⱼ`. -/
theorem CScalars.nonempty_of_linearIndependent (Sc : Scalars D k)
    (hα : LinearIndependent ℤ D.α) : Nonempty (CScalars Sc) := by
  obtain ⟨c, hc⟩ := exists_shift_family D.α hα Sc.t
  exact ⟨⟨c, hc⟩⟩

end OddMath.SKM
