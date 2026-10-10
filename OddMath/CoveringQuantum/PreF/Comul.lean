/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.TensorProduct.Associator
import OddMath.CoveringQuantum.PreF.Basic

/-!
# The twisted coproduct `r : 'f → 'f ⊗ 'f`

Clark–Hill–Wang, arXiv:1301.1665v2 ([CHW1]), §1.4, and Brundan–Ellis, arXiv:1701.04133v2
([BE2]), §10: `'f ⊗ 'f` carries the twisted multiplication
`(x₁ ⊗ x₂)(x₁' ⊗ x₂') = χ(|x₂|, |x₁'|) x₁x₁' ⊗ x₂x₂'` (`x₂, x₁'` homogeneous; see
`OddMath.CoveringQuantum.PreF.Basic` for the bicharacter `χ`), and `r : 'f → 'f ⊗ 'f` is the
algebra homomorphism for this multiplication with `r(θᵢ) = θᵢ ⊗ 1 + 1 ⊗ θᵢ`.

We avoid choosing homogeneous components: the twisted product is
`twistedMul (a ⊗ b) Z = (a · ⊗ id)(ρ(b) Z)`, where `ρ : 'f → End('f ⊗ 'f)` is the algebra
homomorphism `θᵢ ↦ σᵢ ⊗ (θᵢ ·)` (`twistAct`), so `ρ(b)(c ⊗ d) = σ_{|b|}(c) ⊗ bd` for homogeneous
`b`; associativity (`twistedMul_assoc`) is proved without the grading. Then `r` is obtained by
letting `'f` act on `'f ⊗ 'f` by `θᵢ ↦` twisted left multiplication by `θᵢ ⊗ 1 + 1 ⊗ θᵢ`
(`rEnd`), and `r(x) = rEnd x (1 ⊗ 1)` (`comul`); `comul_mul` shows that `r` is multiplicative for
the twisted product. The construction follows lie-lean's `LusztigF.comul` (the even case).

We also prove the compatibilities of `r` with the counit, the twists and the skew derivations that
are needed for the bilinear form.

## Main definitions

* `PreF.twistAct`: `ρ : 'f → End('f ⊗ 'f)`, `θᵢ ↦ σᵢ ⊗ (θᵢ ·)`.
* `PreF.twistedMul`: the twisted multiplication on `'f ⊗ 'f`.
* `PreF.comul`: `r : 'f → 'f ⊗ 'f`.

## Main results

* `PreF.twistedMul_assoc`, `PreF.twistedMul_one_left`, `PreF.twistedMul_one_right`,
  `PreF.twistedMul_tmul_tmul`.
* `PreF.comul_θ`, `PreF.comul_one`, `PreF.comul_mul`: `r` is the twisted algebra
  homomorphism with `r(θᵢ) = θᵢ ⊗ 1 + 1 ⊗ θᵢ`.
* `PreF.rid_lTensor_counit_comul`, `PreF.lid_rTensor_counit_comul`: counit laws.
* `PreF.comul_twist`: `r ∘ σⱼ = (σⱼ ⊗ σⱼ) ∘ r`.
* `PreF.lTensor_rDeriv_comul`: `(1 ⊗ rⱼ) ∘ r = r ∘ rⱼ`.
* `PreF.lid_rTensor_counit_rDeriv_comul`: `(ε ∘ rᵢ ⊗ 1) ∘ r = ᵢr`.
-/

noncomputable section

open TensorProduct

namespace OddMath.CoveringQuantum

namespace PreF

variable {k I : Type*} [CommRing k] (χ : Bichar k I)

/-- The algebra homomorphism `ρ : 'f → End('f ⊗ 'f)`, `θᵢ ↦ σᵢ ⊗ (θᵢ ·)`; for homogeneous `b`,
`ρ(b)(c ⊗ d) = χ(|b|, |c|) c ⊗ bd`. -/
def twistAct : PreF k I →ₐ[k] Module.End k (PreF k I ⊗[k] PreF k I) :=
  FreeAlgebra.lift k fun i ↦ TensorProduct.map (twist χ i).toLinearMap
    (LinearMap.mulLeft k (θ k i))

lemma twistAct_θ (i : I) : twistAct χ (θ k i) =
    TensorProduct.map (twist χ i).toLinearMap (LinearMap.mulLeft k (θ k i)) := by
  simp [twistAct]

lemma twistAct_one_tmul (b d : PreF k I) : twistAct χ b (1 ⊗ₜ d) = 1 ⊗ₜ (b * d) := by
  induction b using FreeAlgebra.induction generalizing d with
  | grade0 c =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    rw [← Algebra.smul_def, TensorProduct.tmul_smul]
  | grade1 i => simp [twistAct_θ]
  | mul a b ha hb => rw [map_mul, Module.End.mul_apply, hb, ha, mul_assoc]
  | add a b ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_mul, tmul_add]

variable {χ} in
/-- For homogeneous `b ∈ 'f_β` and `c ∈ 'f_γ`, `ρ(b)(c ⊗ d) = χ(β, γ) c ⊗ bd`. -/
theorem twistAct_tmul_of_mem {β γ : I →₀ ℕ} {b c : PreF k I}
    (hb : b ∈ weightSpace k β) (hc : c ∈ weightSpace k γ) (d : PreF k I) :
    twistAct χ b (c ⊗ₜ d) = χ.wt β γ • (c ⊗ₜ (b * d)) := by
  induction hb using Submodule.span_induction generalizing d with
  | mem y hy =>
    obtain ⟨w, rfl, rfl⟩ := hy
    induction w generalizing d with
    | nil => simp [Module.End.one_apply, χ.wt_zero_left]
    | cons l w ih =>
      rw [monomial_cons, map_mul, Module.End.mul_apply, ih, map_smul, twistAct_θ, map_tmul,
        AlgHom.toLinearMap_apply, twist_of_mem l hc, LinearMap.mulLeft_apply, smul_tmul',
        smul_smul, wordWeight_cons, χ.wt_add_left, mul_comm, mul_assoc, smul_tmul']
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, LinearMap.add_apply, hy, hz, add_mul, tmul_add, smul_add]
  | smul a y _ hy => rw [map_smul, LinearMap.smul_apply, hy, smul_mul_assoc, tmul_smul, smul_comm]

/-- The bilinear map `a, b ↦ (a · ⊗ id) ∘ ρ(b)`. -/
def twistedMulAux :
    PreF k I →ₗ[k] PreF k I →ₗ[k] Module.End k (PreF k I ⊗[k] PreF k I) :=
  LinearMap.mk₂ k (fun a b ↦ (LinearMap.mulLeft k a).rTensor _ ∘ₗ twistAct χ b)
    (fun a a' b ↦ by
      rw [show LinearMap.mulLeft k (a + a') = LinearMap.mulLeft k a + LinearMap.mulLeft k a' from
        LinearMap.ext fun x ↦ add_mul _ _ _, LinearMap.rTensor_add, LinearMap.add_comp])
    (fun c a b ↦ by
      rw [show LinearMap.mulLeft k (c • a) = c • LinearMap.mulLeft k a from
        LinearMap.ext fun x ↦ smul_mul_assoc _ _ _, LinearMap.rTensor_smul, LinearMap.smul_comp])
    (fun a b b' ↦ by rw [map_add, LinearMap.comp_add])
    (fun c a b ↦ by rw [map_smul, LinearMap.comp_smul])

/-- The twisted multiplication on `'f ⊗ 'f` ([CHW1] §1.4, [BE2] §10): for homogeneous `x₂`,
`x₁'`, `(x₁ ⊗ x₂)(x₁' ⊗ x₂') = χ(|x₂|, |x₁'|) x₁x₁' ⊗ x₂x₂'`. -/
def twistedMul :
    PreF k I ⊗[k] PreF k I →ₗ[k] PreF k I ⊗[k] PreF k I →ₗ[k]
      PreF k I ⊗[k] PreF k I :=
  TensorProduct.lift (twistedMulAux χ)

lemma twistedMul_tmul (a b : PreF k I) (Z : PreF k I ⊗[k] PreF k I) :
    twistedMul χ (a ⊗ₜ b) Z = (LinearMap.mulLeft k a).rTensor _ (twistAct χ b Z) := by
  simp [twistedMul, twistedMulAux]

lemma twistedMul_tmul_tmul_θ (a c d : PreF k I) (i : I) :
    twistedMul χ (a ⊗ₜ θ k i) (c ⊗ₜ d) = (a * twist χ i c) ⊗ₜ (θ k i * d) := by
  simp [twistedMul_tmul, twistAct_θ]

/-- The twisted multiplication on homogeneous elements ([CHW1] §1.4):
`(x₁ ⊗ x₂)(x₁' ⊗ x₂') = χ(|x₂|, |x₁'|) x₁x₁' ⊗ x₂x₂'`. -/
theorem twistedMul_tmul_tmul {β γ : I →₀ ℕ} {x₂ x₁' : PreF k I}
    (h₂ : x₂ ∈ weightSpace k β) (h₁ : x₁' ∈ weightSpace k γ) (x₁ x₂' : PreF k I) :
    twistedMul χ (x₁ ⊗ₜ x₂) (x₁' ⊗ₜ x₂') =
      χ.wt β γ • ((x₁ * x₁') ⊗ₜ (x₂ * x₂')) := by
  rw [twistedMul_tmul, twistAct_tmul_of_mem h₂ h₁, map_smul, LinearMap.rTensor_tmul,
    LinearMap.mulLeft_apply]

@[simp] lemma twistedMul_one_left (Z : PreF k I ⊗[k] PreF k I) :
    twistedMul χ (1 ⊗ₜ 1) Z = Z := by
  rw [twistedMul_tmul, map_one, show LinearMap.mulLeft k (1 : PreF k I) = LinearMap.id from
    LinearMap.ext fun x ↦ one_mul x, LinearMap.rTensor_id]
  rfl

@[simp] lemma twistedMul_one_right (X : PreF k I ⊗[k] PreF k I) :
    twistedMul χ X (1 ⊗ₜ 1) = X := by
  induction X with
  | tmul a b => simp [twistedMul_tmul, twistAct_one_tmul]
  | add X Y hX hY => rw [map_add, LinearMap.add_apply, hX, hY]

lemma twistedMul_rTensor_mulLeft (a : PreF k I) (W : PreF k I ⊗[k] PreF k I) :
    twistedMul χ ((LinearMap.mulLeft k a).rTensor _ W) =
      (LinearMap.mulLeft k a).rTensor _ ∘ₗ twistedMul χ W := by
  induction W with
  | tmul c d =>
    refine LinearMap.ext fun Z ↦ ?_
    simp only [LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, twistedMul_tmul,
      LinearMap.coe_comp, Function.comp_apply]
    rw [show LinearMap.mulLeft k (a * c) = LinearMap.mulLeft k a ∘ₗ LinearMap.mulLeft k c from
      LinearMap.ext fun x ↦ mul_assoc _ _ _, LinearMap.rTensor_comp, LinearMap.comp_apply]
  | add X Y hX hY => simp only [map_add, hX, hY, LinearMap.comp_add]

lemma twistedMul_twistAct (b : PreF k I) (W : PreF k I ⊗[k] PreF k I) :
    twistedMul χ (twistAct χ b W) = twistAct χ b ∘ₗ twistedMul χ W := by
  induction b using FreeAlgebra.induction generalizing W with
  | grade0 c =>
    simp only [AlgHom.commutes, Module.algebraMap_end_eq_smul_id, LinearMap.smul_apply,
      LinearMap.id_apply, map_smul, LinearMap.smul_comp, LinearMap.id_comp]
  | grade1 i =>
    induction W with
    | tmul c d =>
      refine LinearMap.ext fun Z ↦ ?_
      simp only [twistAct_θ, map_tmul, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
        twistedMul_tmul, map_mul, LinearMap.coe_comp, Function.comp_apply, Module.End.mul_apply]
      generalize twistAct χ d Z = W
      induction W with
      | tmul e f => simp
      | add X Y hX hY => simp only [map_add, hX, hY]
    | add X Y hX hY => simp only [map_add, hX, hY, LinearMap.comp_add]
  | mul a b ha hb =>
    rw [map_mul, Module.End.mul_apply, ha, hb, Module.End.mul_eq_comp, LinearMap.comp_assoc]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, LinearMap.add_comp]

/-- The twisted multiplication is associative. -/
theorem twistedMul_assoc (X Y Z : PreF k I ⊗[k] PreF k I) :
    twistedMul χ (twistedMul χ X Y) Z = twistedMul χ X (twistedMul χ Y Z) := by
  induction X generalizing Z with
  | tmul a b =>
    rw [twistedMul_tmul, twistedMul_rTensor_mulLeft, LinearMap.comp_apply, twistedMul_twistAct,
      LinearMap.comp_apply, twistedMul_tmul]
  | add X X' hX hX' => simp only [map_add, LinearMap.add_apply, hX, hX']

/-- The action of `'f` on `'f ⊗ 'f` by twisted left multiplication, `θᵢ ↦ (θᵢ ⊗ 1 + 1 ⊗ θᵢ) ·`. -/
def rEnd : PreF k I →ₐ[k] Module.End k (PreF k I ⊗[k] PreF k I) :=
  FreeAlgebra.lift k fun i ↦ twistedMul χ (θ k i ⊗ₜ 1 + 1 ⊗ₜ θ k i)

/-- The twisted coproduct `r : 'f → 'f ⊗ 'f` ([CHW1] §1.4; [BE2] §10), `r(x) = x · (1 ⊗ 1)`
for the action `rEnd`; see `comul_θ` and `comul_mul`. -/
def comul : PreF k I →ₗ[k] PreF k I ⊗[k] PreF k I :=
  LinearMap.applyₗ (1 ⊗ₜ 1) ∘ₗ (rEnd χ).toLinearMap

lemma comul_apply (x : PreF k I) : comul χ x = rEnd χ x (1 ⊗ₜ 1) := rfl

lemma rEnd_θ_apply (i : I) (W : PreF k I ⊗[k] PreF k I) :
    rEnd χ (θ k i) W = (LinearMap.mulLeft k (θ k i)).rTensor _ W +
      TensorProduct.map (twist χ i).toLinearMap (LinearMap.mulLeft k (θ k i)) W := by
  simp only [rEnd, FreeAlgebra.lift_ι_apply, map_add, LinearMap.add_apply, twistedMul_tmul,
    map_one, Module.End.one_apply, twistAct_θ]
  congr 1
  rw [show LinearMap.mulLeft k (1 : PreF k I) = LinearMap.id from
    LinearMap.ext fun x ↦ one_mul x, LinearMap.rTensor_id, LinearMap.id_apply]

@[simp] lemma comul_one : comul χ (1 : PreF k I) = 1 ⊗ₜ 1 := by
  simp [comul_apply]

@[simp] lemma comul_algebraMap (c : k) :
    comul χ (algebraMap k (PreF k I) c) = c • ((1 : PreF k I) ⊗ₜ 1) := by
  simp [comul_apply, Module.algebraMap_end_apply]

/-- `r(θᵢ) = θᵢ ⊗ 1 + 1 ⊗ θᵢ`. -/
@[simp] theorem comul_θ (i : I) : comul χ (θ k i) = θ k i ⊗ₜ 1 + 1 ⊗ₜ θ k i := by
  simp [comul_apply, rEnd_θ_apply]

lemma comul_θ_mul (i : I) (x : PreF k I) :
    comul χ (θ k i * x) = (LinearMap.mulLeft k (θ k i)).rTensor _ (comul χ x) +
      TensorProduct.map (twist χ i).toLinearMap (LinearMap.mulLeft k (θ k i)) (comul χ x) := by
  rw [comul_apply, map_mul, Module.End.mul_apply, rEnd_θ_apply, ← comul_apply]

lemma twistedMul_comul (x : PreF k I) : twistedMul χ (comul χ x) = rEnd χ x := by
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    refine LinearMap.ext fun Z ↦ ?_
    simp [Module.algebraMap_end_apply]
  | grade1 i =>
    rw [comul_apply]
    simp only [rEnd, FreeAlgebra.lift_ι_apply, twistedMul_one_right]
  | mul a b ha hb =>
    have : comul χ (a * b) = rEnd χ a (comul χ b) := by
      rw [comul_apply, map_mul, Module.End.mul_apply, ← comul_apply]
    rw [this, map_mul, ← ha, ← hb]
    refine LinearMap.ext fun Z ↦ ?_
    rw [Module.End.mul_apply, twistedMul_assoc]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- `r` is multiplicative for the twisted multiplication ([CHW1] §1.4; [BE2] §10). -/
theorem comul_mul (x y : PreF k I) :
    comul χ (x * y) = twistedMul χ (comul χ x) (comul χ y) := by
  rw [twistedMul_comul, comul_apply, map_mul, Module.End.mul_apply, ← comul_apply]

/-! ### Counit, twists and skew derivations -/

/-- The counit law `(1 ⊗ ε) ∘ r = id`. -/
theorem rid_lTensor_counit_comul (x : PreF k I) :
    TensorProduct.rid k _ ((counit (k := k) (I := I)).toLinearMap.lTensor _ (comul χ x)) = x := by
  induction x using induction_left with
  | algebraMap c => simp [Algebra.algebraMap_eq_smul_one]
  | smul c x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]
  | θ_mul i x hx =>
    rw [comul_θ_mul, map_add, map_add]
    generalize comul χ x = W at hx
    have h1 : ∀ W : PreF k I ⊗[k] PreF k I,
        TensorProduct.rid k _ ((counit (k := k) (I := I)).toLinearMap.lTensor _
          ((LinearMap.mulLeft k (θ k i)).rTensor _ W)) =
        θ k i * TensorProduct.rid k _ ((counit (k := k) (I := I)).toLinearMap.lTensor _ W) := by
      intro W
      induction W with
      | tmul e f => simp
      | add X Y hX hY => simp only [map_add, hX, hY, mul_add]
    have h2 : ∀ W : PreF k I ⊗[k] PreF k I,
        (counit (k := k) (I := I)).toLinearMap.lTensor _
          (TensorProduct.map (twist χ i).toLinearMap (LinearMap.mulLeft k (θ k i)) W) = 0 := by
      intro W
      induction W with
      | tmul e f => simp
      | add X Y hX hY => simp only [map_add, hX, hY, add_zero]
    rw [h1, hx, h2, map_zero, add_zero]

/-- The counit law `(ε ⊗ 1) ∘ r = id`. -/
theorem lid_rTensor_counit_comul (x : PreF k I) :
    TensorProduct.lid k _ ((counit (k := k) (I := I)).toLinearMap.rTensor _ (comul χ x)) = x := by
  induction x using induction_left with
  | algebraMap c => simp [Algebra.algebraMap_eq_smul_one]
  | smul c x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]
  | θ_mul i x hx =>
    rw [comul_θ_mul, map_add, map_add]
    generalize comul χ x = W at hx
    have h1 : ∀ W : PreF k I ⊗[k] PreF k I,
        (counit (k := k) (I := I)).toLinearMap.rTensor _
          ((LinearMap.mulLeft k (θ k i)).rTensor _ W) = 0 := by
      intro W
      induction W with
      | tmul e f => simp
      | add X Y hX hY => simp only [map_add, hX, hY, add_zero]
    have h2 : ∀ W : PreF k I ⊗[k] PreF k I,
        TensorProduct.lid k _ ((counit (k := k) (I := I)).toLinearMap.rTensor _
          (TensorProduct.map (twist χ i).toLinearMap (LinearMap.mulLeft k (θ k i)) W)) =
        θ k i * TensorProduct.lid k _ ((counit (k := k) (I := I)).toLinearMap.rTensor _ W) := by
      intro W
      induction W with
      | tmul e f => simp
      | add X Y hX hY => simp only [map_add, hX, hY, mul_add]
    rw [h1, h2, hx, map_zero, zero_add]

/-- `r ∘ σⱼ = (σⱼ ⊗ σⱼ) ∘ r`. -/
theorem comul_twist (j : I) (x : PreF k I) :
    comul χ (twist χ j x) =
      TensorProduct.map (twist χ j).toLinearMap (twist χ j).toLinearMap (comul χ x) := by
  induction x using induction_left with
  | algebraMap c => simp [Algebra.algebraMap_eq_smul_one]
  | smul c x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]
  | θ_mul i x hx =>
    rw [map_mul, twist_θ, smul_mul_assoc, map_smul, comul_θ_mul, comul_θ_mul, hx]
    have e1 : ∀ W : PreF k I ⊗[k] PreF k I,
        TensorProduct.map (twist χ j).toLinearMap (twist χ j).toLinearMap
          ((LinearMap.mulLeft k (θ k i)).rTensor _ W) = χ j i •
          (LinearMap.mulLeft k (θ k i)).rTensor _
            (TensorProduct.map (twist χ j).toLinearMap (twist χ j).toLinearMap W) := by
      intro W
      induction W with
      | tmul e f => simp [TensorProduct.smul_tmul']
      | add X Y hX hY => simp only [map_add, smul_add, hX, hY]
    have e2 : ∀ W : PreF k I ⊗[k] PreF k I,
        TensorProduct.map (twist χ j).toLinearMap (twist χ j).toLinearMap
          (TensorProduct.map (twist χ i).toLinearMap (LinearMap.mulLeft k (θ k i)) W) =
        χ j i • TensorProduct.map (twist χ i).toLinearMap (LinearMap.mulLeft k (θ k i))
            (TensorProduct.map (twist χ j).toLinearMap (twist χ j).toLinearMap W) := by
      intro W
      induction W with
      | tmul e f => simp [twist_comm χ i j, TensorProduct.tmul_smul]
      | add X Y hX hY => simp only [map_add, smul_add, hX, hY]
    rw [map_add, e1, e2, smul_add]

/-- `(1 ⊗ rⱼ) ∘ r = r ∘ rⱼ` (from cf. [CHW1] §1.5). -/
theorem lTensor_rDeriv_comul [DecidableEq I] (j : I) (x : PreF k I) :
    (rDeriv χ j).lTensor _ (comul χ x) = comul χ (rDeriv χ j x) := by
  induction x using induction_left with
  | algebraMap c => simp [Algebra.algebraMap_eq_smul_one]
  | smul c x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]
  | θ_mul i x hx =>
    rw [comul_θ_mul, rDeriv_θ_mul, map_add, map_add, comul_θ_mul, ← hx]
    have key : ∀ W : PreF k I ⊗[k] PreF k I,
        (rDeriv χ j).lTensor _ ((LinearMap.mulLeft k (θ k i)).rTensor _ W) +
          (rDeriv χ j).lTensor _
            (TensorProduct.map (twist χ i).toLinearMap (LinearMap.mulLeft k (θ k i)) W) =
        (LinearMap.mulLeft k (θ k i)).rTensor _ ((rDeriv χ j).lTensor _ W) +
          TensorProduct.map (twist χ i).toLinearMap (LinearMap.mulLeft k (θ k i))
            ((rDeriv χ j).lTensor _ W) +
          if j = i then TensorProduct.map (twist χ j).toLinearMap (twist χ j).toLinearMap W
          else 0 := by
      intro W
      induction W with
      | tmul e f =>
        simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_tmul,
          LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, rDeriv_θ_mul]
        split_ifs with h
        · subst h; rw [tmul_add]; abel
        · simp
      | add X Y hX hY =>
        simp only [map_add] at hX hY ⊢
        split_ifs at hX hY ⊢ <;> [rw [← add_add_add_comm, hX, hY]; rw [← add_add_add_comm, hX, hY]]
        <;> abel
    rw [key]
    split_ifs with h
    · subst h; rw [comul_twist]
    · simp

/-- `(ε ∘ rᵢ ⊗ 1) ∘ r = ᵢr` (cf. [CHW1] §1.5). -/
theorem lid_rTensor_counit_rDeriv_comul [DecidableEq I] (i : I) (y : PreF k I) :
    TensorProduct.lid k _ (((counit (k := k) (I := I)).toLinearMap ∘ₗ rDeriv χ i).rTensor _
      (comul χ y)) = lDeriv χ i y := by
  induction y using induction_left with
  | algebraMap c => simp [Algebra.algebraMap_eq_smul_one]
  | smul c x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]
  | θ_mul j y hy =>
    rw [comul_θ_mul, map_add, map_add, lDeriv_θ_mul]
    have e1 : ∀ W : PreF k I ⊗[k] PreF k I,
        TensorProduct.lid k _ (((counit (k := k) (I := I)).toLinearMap ∘ₗ rDeriv χ i).rTensor _
          ((LinearMap.mulLeft k (θ k j)).rTensor _ W)) = (if i = j then (1 : k) else 0) •
          TensorProduct.lid k _ ((counit (k := k) (I := I)).toLinearMap.rTensor _ W) := by
      intro W
      induction W with
      | tmul e f =>
        simp only [LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, LinearMap.coe_comp,
          Function.comp_apply, AlgHom.toLinearMap_apply, counit_rDeriv_θ_mul, lid_tmul]
        split_ifs <;> simp
      | add X Y hX hY => simp only [map_add, smul_add, hX, hY]
    have e2 : ∀ W : PreF k I ⊗[k] PreF k I,
        TensorProduct.lid k _ (((counit (k := k) (I := I)).toLinearMap ∘ₗ rDeriv χ i).rTensor _
          (TensorProduct.map (twist χ j).toLinearMap (LinearMap.mulLeft k (θ k j)) W)) =
        χ i j • (θ k j * TensorProduct.lid k _
          (((counit (k := k) (I := I)).toLinearMap ∘ₗ rDeriv χ i).rTensor _ W)) := by
      intro W
      induction W with
      | tmul e f =>
        simp only [map_tmul, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, LinearMap.coe_comp,
          Function.comp_apply, AlgHom.toLinearMap_apply, lid_tmul, rDeriv_twist, map_smul,
          counit_twist, smul_eq_mul, mul_smul_comm, smul_smul]
      | add X Y hX hY => simp only [map_add, smul_add, mul_add, hX, hY]
    rw [e1, e2, hy, lid_rTensor_counit_comul]
    split_ifs <;> simp

end PreF

end OddMath.CoveringQuantum
