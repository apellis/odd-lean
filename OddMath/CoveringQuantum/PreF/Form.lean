/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import OddMath.CoveringQuantum.PreF.Comul

/-!
# The bilinear form on `'f` and the algebra `f = 'f / I`

Clark–Hill–Wang, arXiv:1301.1665v2 ([CHW1]), Prop. 1.4.1: there is a unique bilinear form
`(·, ·)` on `'f` with `(1, 1) = 1` and
* (a) `(θᵢ, θⱼ) = δᵢⱼ (1 - πᵢ qᵢ⁻²)⁻¹`;
* (b) `(x, y'y'') = (r(x), y' ⊗ y'')`;
* (c) `(xx', y'') = (x ⊗ x', r(y''))`,
where `(x₁ ⊗ x₂, x₁' ⊗ x₂') = (x₁, x₁')(x₂, x₂')`; it is symmetric. Brundan–Ellis,
arXiv:1701.04133v2 ([BE2]), §10, state the same with `q ↦ q⁻¹`, `(θᵢ, θⱼ) = δᵢⱼ / (1 - πᵢ qᵢ²)`.

We work with an arbitrary symmetric `χ` (see `OddMath.CoveringQuantum.PreF.Basic`) and an
arbitrary normalization `(θᵢ, θᵢ) = nmᵢ ∈ k`; properties (b), (c) and symmetry hold for every
choice. We construct the form directly as `(x, y) = ε(Ψ(x) y)`, where `ε` is the counit and
`Ψ : 'f → End('f)` is the algebra homomorphism `θᵢ ↦ nmᵢ rᵢ` (`formEnd`); thus
`(x θᵢ, y) = nmᵢ (x, rᵢ(y))` holds by construction ([CHW1] §1.5). We then prove
`(x, y θⱼ) = nmⱼ (rⱼ(x), y)` (`form_mul_θ_right`), symmetry (`form_comm`), (b)
(`form_mul_right`, using `(1 ⊗ rⱼ) ∘ r = r ∘ rⱼ`), (c) (`form_mul_left`), and
`(θᵢ x, y) = nmᵢ (x, ᵢr(y))` (`form_θ_mul`). [CHW1] instead transpose `r` to an algebra structure
on the graded dual of `'f`; the construction here follows lie-lean's `LusztigF.form`.

The radical `I = {x | ∀ y, (x, y) = 0}` of the form is a two-sided ideal (by (c)), and
`f = 'f / I` ([CHW1] §1.4).

## Main definitions

* `PreF.form χ nm`: the bilinear form on `'f`; `PreF.formTensor χ nm`: the form on `'f ⊗ 'f`.
* `PreF.radical χ nm`: the radical, as a two-sided ideal.
* `PreF.Quotient χ nm`: the algebra `f = 'f / radical`, with `PreF.toQuotient`.

## Main results

* `PreF.form_one_one`, `PreF.form_θ_θ`: normalization.
* `PreF.form_mul_right` (b), `PreF.form_mul_left` (c), `PreF.form_comm`.
* `PreF.form_mul_θ`, `PreF.form_θ_mul`: the adjunction with `rᵢ`, `ᵢr`.
* `PreF.form_eq_zero_of_ne`: distinct weight spaces are orthogonal.
* `PreF.mem_radical_iff`, `PreF.toQuotient_eq_zero_iff`, `PreF.mem_radical_of_rDeriv_mem`.
-/

noncomputable section

open TensorProduct

namespace OddMath.CoveringQuantum

namespace PreF

variable {k I : Type*} [CommRing k] [DecidableEq I] (χ : Bichar k I) (nm : I → k)

/-- The algebra homomorphism `Ψ : 'f → End('f)`, `θᵢ ↦ (θᵢ, θᵢ) rᵢ`. -/
def formEnd : PreF k I →ₐ[k] Module.End k (PreF k I) :=
  FreeAlgebra.lift k fun i ↦ nm i • rDeriv χ i

/-- The bilinear form `(·, ·)` on `'f` with `(θᵢ, θᵢ) = nmᵢ` ([CHW1] Prop. 1.4.1),
`(x, y) = ε(Ψ(x) y)`. -/
def form : LinearMap.BilinForm k (PreF k I) :=
  (formEnd χ nm).toLinearMap.compr₂ (counit (k := k) (I := I)).toLinearMap

lemma form_apply (x y : PreF k I) : form χ nm x y = counit (formEnd χ nm x y) := rfl

lemma formEnd_apply_one (x : PreF k I) :
    formEnd χ nm x 1 = algebraMap k _ (counit x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp [Algebra.algebraMap_eq_smul_one]
  | grade1 i => simp [formEnd]
  | mul a b ha hb =>
    rw [map_mul, Module.End.mul_apply, hb, Algebra.algebraMap_eq_smul_one, map_smul, ha,
      map_mul, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul,
      mul_comm]
  | add a b ha hb => simp [ha, hb]

@[simp] lemma form_algebraMap_left (c : k) (y : PreF k I) :
    form χ nm (algebraMap k _ c) y = c * counit y := by
  simp [form_apply, Module.algebraMap_end_apply]

@[simp] lemma form_algebraMap_right (x : PreF k I) (c : k) :
    form χ nm x (algebraMap k _ c) = c * counit x := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, form_apply, formEnd_apply_one]
  simp

@[simp] lemma form_one_left (y : PreF k I) : form χ nm 1 y = counit y := by
  simpa using form_algebraMap_left χ nm 1 y

@[simp] lemma form_one_right (x : PreF k I) : form χ nm x 1 = counit x := by
  simpa using form_algebraMap_right χ nm x 1

/-- `(1, 1) = 1`. -/
theorem form_one_one : form χ nm (1 : PreF k I) 1 = 1 := by simp

/-- `(x θᵢ, y) = (θᵢ, θᵢ)(x, rᵢ(y))` ([CHW1] §1.5). -/
theorem form_mul_θ (x : PreF k I) (i : I) (y : PreF k I) :
    form χ nm (x * θ k i) y = nm i * form χ nm x (rDeriv χ i y) := by
  simp [form_apply, formEnd]

/-- `(θᵢ, θⱼ) = δᵢⱼ nmᵢ` ([CHW1] Prop. 1.4.1 (a), with `nmᵢ = (1 - πᵢ qᵢ⁻²)⁻¹` there). -/
theorem form_θ_θ (i j : I) :
    form χ nm (θ k i) (θ k j) = if i = j then nm i else 0 := by
  have := form_mul_θ χ nm 1 i (θ k j)
  rw [one_mul] at this
  rw [this, rDeriv_θ]
  split_ifs <;> simp

/-- `(x, y θⱼ) = (θⱼ, θⱼ)(rⱼ(x), y)`. -/
theorem form_mul_θ_right (x y : PreF k I) (j : I) :
    form χ nm x (y * θ k j) = nm j * form χ nm (rDeriv χ j x) y := by
  induction x using induction_right generalizing y with
  | algebraMap c => simp
  | smul c x hx => simp [hx, mul_left_comm]
  | add x x' hx hx' => simp [hx, hx', mul_add]
  | mul_θ x i hx =>
    rw [form_mul_θ, rDeriv_mul_θ, map_add, map_smul, hx, rDeriv_mul_θ]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, form_mul_θ,
      smul_eq_mul]
    by_cases h : i = j
    · subst h; simp only [ite_true]
    · simp only [h, Ne.symm h, ite_false, map_zero, LinearMap.zero_apply, χ.comm]
      ring

/-- The form is symmetric ([CHW1] Prop. 1.4.1). -/
theorem form_comm (x y : PreF k I) : form χ nm x y = form χ nm y x := by
  induction y using induction_right generalizing x with
  | algebraMap c => simp
  | smul c y hy => simp [hy]
  | add y y' hy hy' => simp [hy, hy']
  | mul_θ y j hy => rw [form_mul_θ_right, hy, form_mul_θ]

/-- The form is symmetric, as a bilinear form ([CHW1] Prop. 1.4.1). -/
theorem isSymm_form : LinearMap.IsSymm (form χ nm) :=
  LinearMap.isSymm_def.2 fun x y ↦ by simpa using form_comm χ nm x y

/-- The bilinear form `(x₁ ⊗ x₂, y₁ ⊗ y₂) = (x₁, y₁)(x₂, y₂)` on `'f ⊗ 'f`. -/
def formTensor : LinearMap.BilinForm k (PreF k I ⊗[k] PreF k I) :=
  (form χ nm).tmul (form χ nm)

@[simp] lemma formTensor_tmul (x₁ x₂ y₁ y₂ : PreF k I) :
    formTensor χ nm (x₁ ⊗ₜ x₂) (y₁ ⊗ₜ y₂) = form χ nm x₁ y₁ * form χ nm x₂ y₂ := by
  simp [formTensor, mul_comm]

lemma formTensor_comm (X Y : PreF k I ⊗[k] PreF k I) :
    formTensor χ nm X Y = formTensor χ nm Y X := by
  induction X generalizing Y with
  | tmul a b =>
    induction Y with
    | tmul c d => simp [form_comm χ nm a, form_comm χ nm b]
    | add Y Z hY hZ => simp [hY, hZ]
  | add X X' hX hX' => simp [hX, hX']

lemma formTensor_tmul_one (W : PreF k I ⊗[k] PreF k I) (y : PreF k I) :
    formTensor χ nm W (y ⊗ₜ 1) =
      form χ nm (TensorProduct.rid k _ ((counit (k := k) (I := I)).toLinearMap.lTensor _ W)) y := by
  induction W with
  | tmul a b => simp [mul_comm]
  | add X Y hX hY => simp [hX, hY]

lemma formTensor_tmul_mul_θ (W : PreF k I ⊗[k] PreF k I) (y z : PreF k I) (j : I) :
    formTensor χ nm W (y ⊗ₜ (z * θ k j)) =
      nm j * formTensor χ nm ((rDeriv χ j).lTensor _ W) (y ⊗ₜ z) := by
  induction W with
  | tmul a b => simp [form_mul_θ_right, mul_left_comm]
  | add X Y hX hY => simp [hX, hY, mul_add]

/-- Property (b): `(x, y'y'') = (r(x), y' ⊗ y'')` ([CHW1] Prop. 1.4.1 (b); [BE2] §10). -/
theorem form_mul_right (x y' y'' : PreF k I) :
    form χ nm x (y' * y'') = formTensor χ nm (comul χ x) (y' ⊗ₜ y'') := by
  induction y'' using induction_right generalizing x with
  | algebraMap c =>
    rw [← Algebra.commutes, ← Algebra.smul_def, map_smul, Algebra.algebraMap_eq_smul_one,
      tmul_smul, map_smul, formTensor_tmul_one, rid_lTensor_counit_comul]
  | smul c y hy => rw [mul_smul_comm, map_smul, hy, tmul_smul, map_smul]
  | add y z hy hz => rw [mul_add, map_add, hy, hz, tmul_add, map_add]
  | mul_θ y j hy =>
    rw [← mul_assoc, form_mul_θ_right, hy, formTensor_tmul_mul_θ, lTensor_rDeriv_comul]

/-- Property (c): `(x'x'', y) = (x' ⊗ x'', r(y))` ([CHW1] Prop. 1.4.1 (c); [BE2] §10). -/
theorem form_mul_left (x' x'' y : PreF k I) :
    form χ nm (x' * x'') y = formTensor χ nm (x' ⊗ₜ x'') (comul χ y) := by
  rw [form_comm, form_mul_right, formTensor_comm]

lemma formTensor_θ_tmul (i : I) (x : PreF k I) (W : PreF k I ⊗[k] PreF k I) :
    formTensor χ nm (θ k i ⊗ₜ x) W = nm i * form χ nm x (TensorProduct.lid k _
      (((counit (k := k) (I := I)).toLinearMap ∘ₗ rDeriv χ i).rTensor _ W)) := by
  induction W with
  | tmul a b =>
    have := form_mul_θ χ nm 1 i a
    rw [one_mul] at this
    simp [this, mul_assoc]
  | add X Y hX hY => simp [hX, hY, mul_add]

/-- `(θᵢ x, y) = (θᵢ, θᵢ)(x, ᵢr(y))` ([CHW1] §1.5). -/
theorem form_θ_mul (i : I) (x y : PreF k I) :
    form χ nm (θ k i * x) y = nm i * form χ nm x (lDeriv χ i y) := by
  rw [form_mul_left, formTensor_θ_tmul, lid_rTensor_counit_rDeriv_comul]

/-! ### Orthogonality of weight spaces -/

omit [DecidableEq I] in
lemma counit_eq_zero_of_mem {ν : I →₀ ℕ} (hν : ν ≠ 0) {x : PreF k I}
    (hx : x ∈ weightSpace k ν) : counit x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    cases w with
    | nil => exact absurd hw.symm hν
    | cons l w => simp
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

lemma rDeriv_monomial_eq_zero (i : I) (w : List I) (hw : wordWeight w i = 0) :
    rDeriv χ i (monomial k w) = 0 := by
  induction w with
  | nil => simp
  | cons l w ih =>
    have hl : l ≠ i := by
      rintro rfl; simp at hw
    have hw' : wordWeight w i = 0 := by
      simp only [wordWeight_cons, Finsupp.add_apply] at hw; omega
    rw [monomial_cons, rDeriv_θ_mul, ih hw']
    simp [Ne.symm hl]

lemma rDeriv_monomial_mem (i : I) (w : List I) :
    ∀ μ, wordWeight w = μ + Finsupp.single i 1 →
      rDeriv χ i (monomial k w) ∈ weightSpace k μ := by
  induction w with
  | nil =>
    intro μ h
    have := congr($h i)
    simp at this
  | cons l w ih =>
    intro μ h
    rw [monomial_cons, rDeriv_θ_mul]
    rw [wordWeight_cons] at h
    -- the term `θₗ rᵢ(m)`
    have h1 : θ k l * rDeriv χ i (monomial k w) ∈ weightSpace k μ := by
      by_cases hwi : wordWeight w i = 0
      · rw [rDeriv_monomial_eq_zero χ i w hwi, mul_zero]; exact Submodule.zero_mem _
      · have hw : wordWeight w = (wordWeight w - Finsupp.single i 1) + Finsupp.single i 1 := by
          ext j
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          split_ifs with hij
          · subst hij; omega
          · omega
        have hμ : μ = Finsupp.single l 1 + (wordWeight w - Finsupp.single i 1) := by
          ext j
          have := congr($h j)
          simp only [Finsupp.add_apply, Finsupp.tsub_apply] at this ⊢
          by_cases hij : i = j
          · subst hij
            simp only [Finsupp.single_eq_same] at this ⊢
            omega
          · rw [Finsupp.single_eq_of_ne (Ne.symm hij)] at this ⊢
            omega
        rw [hμ]
        exact mul_mem_weightSpace (θ_mem_weightSpace l) (ih _ hw)
    split_ifs with hil
    · subst hil
      have : wordWeight w = μ := by
        rw [add_comm] at h; exact add_right_cancel h
      exact Submodule.add_mem _ h1
        (this ▸ twist_mem_weightSpace χ i (monomial_mem_weightSpace w))
    · rw [add_zero]; exact h1

lemma rDeriv_mem_weightSpace (i : I) {μ : I →₀ ℕ} {y : PreF k I}
    (hy : y ∈ weightSpace k (μ + Finsupp.single i 1)) : rDeriv χ i y ∈ weightSpace k μ := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    exact rDeriv_monomial_mem χ i w μ hw
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

lemma rDeriv_eq_zero_of_mem (i : I) {μ : I →₀ ℕ} (hμ : μ i = 0) {y : PreF k I}
    (hy : y ∈ weightSpace k μ) : rDeriv χ i y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl, rfl⟩ := hy
    exact rDeriv_monomial_eq_zero χ i w hμ
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, hy, smul_zero]

lemma form_monomial_eq_zero (w : List I) :
    ∀ μ y, y ∈ weightSpace k μ → wordWeight w ≠ μ → form χ nm (monomial k w) y = 0 := by
  induction w using List.reverseRecOn with
  | nil =>
    intro μ y hy hμ
    rw [monomial_nil, form_one_left, counit_eq_zero_of_mem (Ne.symm hμ) hy]
  | append_singleton w i ih =>
    intro μ y hy hμ
    rw [monomial_append, show monomial k [i] = θ k i by simp [monomial], form_mul_θ]
    by_cases hμi : μ i = 0
    · rw [rDeriv_eq_zero_of_mem χ i hμi hy, map_zero, mul_zero]
    · have hμ' : μ = (μ - Finsupp.single i 1) + Finsupp.single i 1 := by
        ext j
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with hij
        · subst hij; omega
        · omega
      rw [hμ'] at hy
      rw [ih _ _ (rDeriv_mem_weightSpace χ i hy), mul_zero]
      intro h
      apply hμ
      rw [wordWeight_append, h, hμ']
      simp

/-- Distinct weight spaces are orthogonal ([BE2] §10). -/
theorem form_eq_zero_of_ne {ν μ : I →₀ ℕ} (hνμ : ν ≠ μ) {x y : PreF k I}
    (hx : x ∈ weightSpace k ν) (hy : y ∈ weightSpace k μ) : form χ nm x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact form_monomial_eq_zero χ nm w μ y hy (hw ▸ hνμ)
  | zero => simp
  | add x z _ _ hx hz => simp [hx, hz]
  | smul c x _ hx => simp [hx]

/-! ### The radical and the algebra `f` -/

lemma formTensor_tmul_eq_zero_left {x : PreF k I} (hx : ∀ y, form χ nm x y = 0)
    (z : PreF k I) (W : PreF k I ⊗[k] PreF k I) : formTensor χ nm (x ⊗ₜ z) W = 0 := by
  induction W with
  | tmul a b => simp [hx]
  | add X Y hX hY => simp [hX, hY]

lemma formTensor_tmul_eq_zero_right {x : PreF k I} (hx : ∀ y, form χ nm x y = 0)
    (z : PreF k I) (W : PreF k I ⊗[k] PreF k I) : formTensor χ nm (z ⊗ₜ x) W = 0 := by
  induction W with
  | tmul a b => simp [hx]
  | add X Y hX hY => simp [hX, hY]

/-- The radical `{x | ∀ y, (x, y) = 0}` of the form, a two-sided ideal of `'f` ([CHW1] §1.4). -/
def radical : TwoSidedIdeal (PreF k I) :=
  TwoSidedIdeal.mk' {x | ∀ y, form χ nm x y = 0} (by simp) (fun hx hy z ↦ by simp [hx z, hy z])
    (fun hx z ↦ by simp [hx z])
    (fun hy z ↦ by rw [form_mul_left, formTensor_tmul_eq_zero_right χ nm hy])
    (fun hx z ↦ by rw [form_mul_left, formTensor_tmul_eq_zero_left χ nm hx])

theorem mem_radical_iff {x : PreF k I} : x ∈ radical χ nm ↔ ∀ y, form χ nm x y = 0 := by
  simp [radical, TwoSidedIdeal.mem_mk']

theorem mem_radical_iff' {x : PreF k I} : x ∈ radical χ nm ↔ ∀ y, form χ nm y x = 0 := by
  simp only [mem_radical_iff, form_comm χ nm x]

/-- If `x` has no constant term and `rᵢ(x)` lies in the radical for all `i`, then so does `x`
(cf. [CHW1] Lemma 1.5.2). -/
theorem mem_radical_of_rDeriv_mem {x : PreF k I} (hx0 : counit x = 0)
    (hx : ∀ i, rDeriv χ i x ∈ radical χ nm) : x ∈ radical χ nm := by
  rw [mem_radical_iff']
  intro y
  induction y using induction_right with
  | algebraMap c => rw [form_algebraMap_left, hx0, mul_zero]
  | smul c y hy => simp [hy]
  | add y z hy hz => simp [hy, hz]
  | mul_θ y i _ => rw [form_mul_θ, (mem_radical_iff' χ nm).1 (hx i), mul_zero]

/-- The radical is stable under `rᵢ` when `(θᵢ, θᵢ)` is a unit. -/
theorem rDeriv_mem_radical {i : I} (hi : IsUnit (nm i)) {x : PreF k I}
    (hx : x ∈ radical χ nm) : rDeriv χ i x ∈ radical χ nm := by
  rw [mem_radical_iff']
  intro y
  have := form_mul_θ χ nm y i x
  rw [(mem_radical_iff' χ nm).1 hx] at this
  exact hi.mul_right_eq_zero.1 this.symm

/-- The radical is stable under `ᵢr` when `(θᵢ, θᵢ)` is a unit. -/
theorem lDeriv_mem_radical {i : I} (hi : IsUnit (nm i)) {x : PreF k I}
    (hx : x ∈ radical χ nm) : lDeriv χ i x ∈ radical χ nm := by
  rw [mem_radical_iff']
  intro y
  have := form_θ_mul χ nm i y x
  rw [(mem_radical_iff' χ nm).1 hx] at this
  exact hi.mul_right_eq_zero.1 this.symm

/-- The algebra `f = 'f / I`, the quotient of `'f` by the radical of the bilinear form
([CHW1] §1.4). -/
abbrev Quotient := (radical χ nm).ringCon.Quotient

/-- The projection `'f → f`. -/
def toQuotient : PreF k I →ₐ[k] Quotient χ nm := RingCon.mkₐ k (radical χ nm).ringCon

theorem toQuotient_surjective : Function.Surjective (toQuotient χ nm) :=
  RingCon.mkₐ_surjective _

theorem toQuotient_eq_zero_iff {x : PreF k I} : toQuotient χ nm x = 0 ↔ x ∈ radical χ nm := by
  rw [TwoSidedIdeal.mem_iff, ← RingCon.eq]
  rfl

end PreF

end OddMath.CoveringQuantum
