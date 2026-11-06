/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.MoreGenerators
import OddMath.SKM.RootCover

/-!
# When the units `c_{λ;i}` exist

Brundan–Ellis, arXiv:1701.04133v2, (1.17): units `c_{λ;i}` with `c_{λ+αⱼ;i} = tᵢⱼ c_{λ;i}`
(`CScalars`). Brundan–Wang–Webster, arXiv:2505.22929v2, Remark 2.4, allow arbitrary
normalizations instead.

* `CScalars.c_add_rootSum`: `c_{λ + Σ nⱼαⱼ; i} = (Π tᵢⱼ^{nⱼ}) c_{λ;i}`.
* `nonempty_cScalars_iff`: `CScalars Sc` exists if and only if `Π tᵢⱼ^{nⱼ} = 1` for every `i`
  and every integer relation `Σ nⱼ αⱼ = 0` among the simple roots.
* `nonempty_cScalars_of_injective`: with independent simple roots they exist for every `t`;
  `CScalars.t_mul_t_eq_one`: `αⱼ + αₗ = 0` forces `tᵢⱼ tᵢₗ = 1` (affine `A₁`).
* `nonempty_cScalars_rootCover`: they always exist on `RootCover.rootCover D`.
-/

noncomputable section

namespace OddMath.SKM.RootCover

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {k : Type w} [CommRing k]

variable {D : Datum I X} {Ptwo : Prop} {Sc : ScalarData D k Ptwo}

theorem _root_.OddMath.SKM.CScalars.c_sub_root (cs : CScalars Sc) (μ : X) (i j : I) :
    cs.c (μ - D.α j) i = (Sc.t i j)⁻¹ * cs.c μ i := by
  have h := cs.shift (μ - D.α j) i j
  rw [sub_add_cancel] at h
  rw [h, inv_mul_cancel_left]

theorem _root_.OddMath.SKM.CScalars.c_add_zsmul (cs : CScalars Sc) (μ : X) (i j : I) (m : ℤ) :
    cs.c (μ + m • D.α j) i = Sc.t i j ^ m * cs.c μ i := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
    rw [add_smul, one_smul, ← add_assoc, cs.shift, ih, zpow_add_one, mul_comm _ (Sc.t i j),
      mul_assoc]
  | pred m ih =>
    rw [sub_smul, one_smul, ← add_sub_assoc, cs.c_sub_root, ih, zpow_sub_one,
      mul_comm _ (Sc.t i j)⁻¹, mul_assoc]

/-- `c_{λ + Σ nⱼαⱼ; i} = (Π tᵢⱼ^{nⱼ}) c_{λ;i}`. -/
theorem _root_.OddMath.SKM.CScalars.c_add_rootSum (cs : CScalars Sc) (n : I →₀ ℤ) (μ : X)
    (i : I) :
    cs.c (μ + rootSum D n) i = Additive.toMul (rootChar Sc.t i n) * cs.c μ i := by
  induction n using Finsupp.induction_linear generalizing μ with
  | zero => simp
  | add n n' hn hn' =>
    rw [map_add, ← add_assoc, hn', hn, rootChar_add]
    ac_rfl
  | single j m => rw [rootSum_single, cs.c_add_zsmul, rootChar_single]

/-- Every integer relation among the simple roots forces a relation among the `tᵢⱼ`. -/
theorem _root_.OddMath.SKM.CScalars.rootChar_eq_one (cs : CScalars Sc) {n : I →₀ ℤ}
    (hn : rootSum D n = 0) (i : I) :
    Additive.toMul (rootChar Sc.t i n) = 1 := by
  have h := cs.c_add_rootSum n 0 i
  rw [hn, add_zero] at h
  exact (mul_eq_right.mp h.symm)


/-- Units with the shift law, built from the coset representatives of the root lattice. -/
def ofRootRelations
    (H : ∀ i (n : I →₀ ℤ), rootSum D n = 0 → Additive.toMul (rootChar Sc.t i n) = 1) :
    CScalars Sc :=
  let Q : AddSubgroup X := (rootSum D).range
  let rep : X → X := fun μ => (QuotientAddGroup.mk (s := Q) μ).out
  have hrep : ∀ μ, -rep μ + μ ∈ Q := fun μ =>
    (QuotientAddGroup.eq).mp (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (s := Q) μ))
  let n : X → I →₀ ℤ := fun μ => Classical.choose (hrep μ)
  have hn : ∀ μ, rootSum D (n μ) = -rep μ + μ := fun μ => Classical.choose_spec (hrep μ)
  { c := fun μ i => Additive.toMul (rootChar Sc.t i (n μ))
    shift := by
      intro μ i j
      have hr : rep (μ + D.α j) = rep μ := by
        change (QuotientAddGroup.mk (s := Q) (μ + D.α j)).out = (QuotientAddGroup.mk μ).out
        congr 1
        refine QuotientAddGroup.eq.mpr ⟨-Finsupp.single j 1, ?_⟩
        simp only [map_neg, rootSum_single, one_smul]
        abel
      have hz : rootSum D (n (μ + D.α j) - n μ - Finsupp.single j 1) = 0 := by
        simp only [map_sub, hn, hr, rootSum_single, one_smul]
        abel
      have h1 := H i _ hz
      have he : n (μ + D.α j) = (n (μ + D.α j) - n μ - Finsupp.single j 1) +
          (Finsupp.single j 1 + n μ) := by abel
      change Additive.toMul (rootChar Sc.t i (n (μ + D.α j))) = _
      rw [he, rootChar_add, h1, one_mul, rootChar_add, rootChar_single, zpow_one] }

/-- **Existence of the units `c_{λ;i}`.** They exist exactly when `Π tᵢⱼ^{nⱼ} = 1` for every
`i` and every integer relation `Σ nⱼ αⱼ = 0` among the simple roots. -/
theorem nonempty_cScalars_iff :
    Nonempty (CScalars Sc) ↔
      ∀ i (n : I →₀ ℤ), rootSum D n = 0 → Additive.toMul (rootChar Sc.t i n) = 1 :=
  ⟨fun ⟨cs⟩ _ _ hn => cs.rootChar_eq_one hn _, fun H => ⟨ofRootRelations H⟩⟩

/-- With independent simple roots the units exist for every choice of `tᵢⱼ`. -/
theorem nonempty_cScalars_of_injective (hD : Function.Injective (rootSum D)) :
    Nonempty (CScalars Sc) := by
  refine nonempty_cScalars_iff.mpr fun i n hn => ?_
  rw [hD (hn.trans (map_zero _).symm), map_zero, toMul_zero]

/-- Two simple roots with `αⱼ + αₗ = 0` force `tᵢⱼ tᵢₗ = 1`. -/
theorem _root_.OddMath.SKM.CScalars.t_mul_t_eq_one (cs : CScalars Sc) {j l : I}
    (h : D.α j + D.α l = 0) (i : I) : Sc.t i j * Sc.t i l = 1 := by
  have := cs.shift (0 + D.α j) i l
  rw [add_assoc, h, add_zero, cs.shift, ← mul_assoc] at this
  rw [mul_comm]
  exact mul_eq_right.mp this.symm

variable (D) in
/-- **The units `c_{λ;i}` exist on the root cover for every choice of parameters.** -/
theorem nonempty_cScalars_rootCover (Sc : ScalarData D k Ptwo) :
    Nonempty (CScalars (coverScalars D Sc)) :=
  nonempty_cScalars_of_injective (rootSum_rootCover_injective D)

end OddMath.SKM.RootCover
