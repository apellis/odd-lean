/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Realization.Coefficients

/-!
# The twisted symmetric-group module

Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2, §3.2, Proposition 3.3 and its proof: for a ring
`A` with an action of the symmetric group and central elements `a_i` with
`w a_i = a_j` whenever `w {i, i+1} = {j, j+1}`, the operators

  `s̃_i (a ⊗ w) = s_i(a) a_i^{ε_i(w)} ⊗ s_i w`,  `ε_i(w) = 1` iff `ℓ(s_i w) < ℓ(w)`,

on `A ⊗ ℤ[S_n]` satisfy `s̃_i a = s_i(a) s̃_i`, the braid relations and `s̃_i² = a_i`.

Here `A` is the coefficient algebra of §3.4 (`Coeff`) and the module is
`M = (Perm ℕ →₀ Coeff)`. The operator `twist a r` is `s̃_a` with the central element `r`; the
relations are proved under the covariance conditions on the central elements that the proof of
Proposition 3.3 uses (`twist_mr`, `twist_mc`, `twist_twist`, `twist_comm`, `twist_braid`).
Since we use permutations of `ℕ`, `ε_a(w)` is the inversion condition `w⁻¹(a+1) < w⁻¹(a)`
(`Desc`), which agrees with the length condition on finite permutations.
-/

noncomputable section
open scoped TensorProduct
namespace OddMath.QuiverHecke.Realization

variable {k : Type*} [CommRing k]

/-! ## Adjacent transpositions of positions and of words -/

/-- The adjacent transposition `s_a = (a, a+1)` of positions. -/
abbrev sw (a : ℕ) : Equiv.Perm ℕ := Equiv.swap a (a + 1)

theorem sw_apply_of_ne {a p : ℕ} (h₁ : p ≠ a) (h₂ : p ≠ a + 1) : sw a p = p :=
  Equiv.swap_apply_of_ne_of_ne h₁ h₂

@[simp] theorem sw_apply_left (a : ℕ) : sw a a = a + 1 := Equiv.swap_apply_left _ _
@[simp] theorem sw_apply_right (a : ℕ) : sw a (a + 1) = a := Equiv.swap_apply_right _ _

@[simp] theorem sw_mul_self (a : ℕ) : sw a * sw a = 1 := Equiv.swap_mul_self _ _

theorem sw_comm {a b : ℕ} (h : a + 1 < b ∨ b + 1 < a) : sw a * sw b = sw b * sw a := by
  ext p
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, sw, Equiv.swap_apply_def]
  split_ifs <;> omega

theorem sw_braid (a : ℕ) : sw a * sw (a + 1) * sw a = sw (a + 1) * sw a * sw (a + 1) := by
  ext p
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, sw, Equiv.swap_apply_def]
  split_ifs <;> omega

/-! ## Descents -/

/-- `ε_a(w) = 1`: the left descent condition `w⁻¹(a+1) < w⁻¹(a)`. -/
def Desc (a : ℕ) (w : Equiv.Perm ℕ) : Prop := w⁻¹ (a + 1) < w⁻¹ a

instance (a : ℕ) (w : Equiv.Perm ℕ) : Decidable (Desc a w) := by unfold Desc; infer_instance

theorem desc_iff (a : ℕ) (σ w : Equiv.Perm ℕ) :
    Desc a (σ * w) ↔ w⁻¹ (σ⁻¹ (a + 1)) < w⁻¹ (σ⁻¹ a) := by
  simp [Desc, mul_inv_rev]

theorem desc_sw_mul (a : ℕ) (w : Equiv.Perm ℕ) : Desc a (sw a * w) ↔ ¬ Desc a w := by
  have hne : w⁻¹ a ≠ w⁻¹ (a + 1) := fun h => by simpa using w⁻¹.injective h
  rw [desc_iff, Desc]
  simp only [sw, Equiv.swap_inv, Equiv.swap_apply_left, Equiv.swap_apply_right, not_lt]
  omega

theorem desc_sw_mul_of_far {a b : ℕ} (h : a + 1 < b ∨ b + 1 < a) (w : Equiv.Perm ℕ) :
    Desc a (sw b * w) ↔ Desc a w := by
  rw [desc_iff, Desc, sw, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega),
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

theorem desc_braid (a : ℕ) (w : Equiv.Perm ℕ) :
    Desc a (sw (a + 1) * w) ↔ Desc (a + 1) (sw a * w) := by
  rw [desc_iff, desc_iff]
  simp only [sw, Equiv.swap_inv, Equiv.swap_apply_def]
  simp [show a ≠ a + 1 + 1 by omega, show a + 1 + 1 ≠ a by omega]

theorem desc_sw_sw_mul (a : ℕ) (w : Equiv.Perm ℕ) :
    Desc a (sw (a + 1) * sw a * w) ↔ Desc (a + 1) w := by
  rw [desc_iff, Desc]
  simp only [sw, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  simp [show a ≠ a + 1 + 1 by omega, show a + 1 + 1 ≠ a by omega]

theorem desc_sw_sw_mul' (a : ℕ) (w : Equiv.Perm ℕ) :
    Desc (a + 1) (sw a * sw (a + 1) * w) ↔ Desc a w := by
  rw [desc_iff, Desc]
  simp only [sw, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  simp [show a ≠ a + 1 + 1 by omega, show a + 1 + 1 ≠ a by omega]

/-! ## Operators on `Perm ℕ →₀ Coeff` -/

variable (k) in
/-- `A ⊗ ℤ[S_∞]` for the coefficient module `A = Coeff`. -/
abbrev M := Equiv.Perm ℕ →₀ Coeff k

/-- Recorded once: instance search does not find it through `Coeff` when the ring is still
unknown, as in `Module.End ?R (M k)`. -/
instance : AddCommGroup (M k) := Finsupp.instAddCommGroup

theorem M.ext {f g : M k →ₗ[k] M k}
    (h : ∀ w x, f (Finsupp.single w x) = g (Finsupp.single w x)) : f = g :=
  Finsupp.lhom_ext h

/-- Componentwise left multiplication by a scalar. -/
def mr (g : K k) : M k →ₗ[k] M k := Finsupp.mapRange.linearMap (scalar g)

/-- Componentwise left multiplication by `c_p`. -/
def mc (p : ℕ) : M k →ₗ[k] M k := Finsupp.mapRange.linearMap (cliff p)

/-- The scalar `r^{ε_a(w)}`. -/
def epow (a : ℕ) (w : Equiv.Perm ℕ) (r : K k) : K k := if Desc a w then r else 1

theorem permK_epow (σ : Equiv.Perm ℕ) (a : ℕ) (w : Equiv.Perm ℕ) (r : K k) :
    permK σ (epow a w r) = epow a w (permK σ r) := by
  unfold epow; split_ifs <;> simp

/-- KKT's `s̃_a` with central element `r`: `x ⊗ w ↦ s_a(x) r^{ε_a(w)} ⊗ s_a w`. -/
def twist (a : ℕ) (r : K k) : M k →ₗ[k] M k :=
  Finsupp.lsum k fun w => Finsupp.lsingle (sw a * w) ∘ₗ (scalar (epow a w r) * perm (sw a))

@[simp] theorem mr_single (g : K k) (w : Equiv.Perm ℕ) (x : Coeff k) :
    mr g (Finsupp.single w x) = Finsupp.single w (scalar g x) := by
  simp [mr]

@[simp] theorem mc_single (p : ℕ) (w : Equiv.Perm ℕ) (x : Coeff k) :
    mc p (Finsupp.single w x) = Finsupp.single w (cliff p x) := by
  simp [mc]

@[simp] theorem twist_single (a : ℕ) (r : K k) (w : Equiv.Perm ℕ) (x : Coeff k) :
    twist a r (Finsupp.single w x) =
      Finsupp.single (sw a * w) (scalar (epow a w r) (perm (sw a) x)) := by
  simp [twist]

theorem mr_mul (f g : K k) : mr (f * g) = mr f ∘ₗ mr g := by
  refine M.ext fun w x => ?_; simp [scalar_mul]

theorem mr_add (f g : K k) : mr (f + g) = mr f + mr g := by
  refine M.ext fun w x => ?_; simp [scalar_add]

@[simp] theorem mr_one : mr (1 : K k) = LinearMap.id := by refine M.ext fun w x => ?_; simp

/-- Scalars pass through permutations. -/
theorem perm_scalar_apply (σ : Equiv.Perm ℕ) (g : K k) (x : Coeff k) :
    perm σ (scalar g x) = scalar (permK σ g) (perm σ x) := by
  rw [← Module.End.mul_apply, perm_scalar, Module.End.mul_apply]

theorem scalar_scalar_apply (f g : K k) (x : Coeff k) :
    scalar f (scalar g x) = scalar (f * g) x := by
  rw [scalar_mul, Module.End.mul_apply]

theorem perm_perm_apply (σ τ : Equiv.Perm ℕ) (x : Coeff k) :
    perm σ (perm τ x) = perm (σ * τ) x := by
  rw [perm_mul, Module.End.mul_apply]

theorem twist_mr (a : ℕ) (r g : K k) :
    twist a r ∘ₗ mr g = mr (permK (sw a) g) ∘ₗ twist a r := by
  refine M.ext fun w x => ?_
  simp only [LinearMap.comp_apply, mr_single, twist_single, perm_scalar_apply,
    scalar_scalar_apply, mul_comm]

theorem twist_mc (a : ℕ) (r : K k) (p : ℕ) (hr : reflect (sw a p) r = r) :
    twist a r ∘ₗ mc p = mc (sw a p) ∘ₗ twist a r := by
  refine M.ext fun w x => ?_
  simp only [LinearMap.comp_apply, mc_single, twist_single]
  congr 1
  have hε : reflect (sw a p) (epow a w r) = epow a w r := by
    unfold epow; split_ifs <;> simp [hr]
  rw [← Module.End.mul_apply (perm (sw a)), perm_cliff, Module.End.mul_apply,
    ← Module.End.mul_apply (scalar _), ← Module.End.mul_apply (cliff _), cliff_scalar, hε]

theorem twist_twist (a : ℕ) (r r' : K k) (h : permK (sw a) r' = r) :
    twist a r ∘ₗ twist a r' = mr r := by
  refine M.ext fun w x => ?_
  simp only [LinearMap.comp_apply, twist_single, mr_single, perm_scalar_apply,
    scalar_scalar_apply, perm_perm_apply, permK_epow, h, sw_mul_self, perm_one,
    Module.End.one_apply, ← mul_assoc, one_mul]
  congr 2
  unfold epow
  have := desc_sw_mul a w
  split_ifs <;> simp_all

theorem twist_comm {a b : ℕ} (hab : a + 1 < b ∨ b + 1 < a) (r₁ r₂ r₃ r₄ : K k)
    (h₁ : permK (sw a) r₂ = r₃) (h₂ : permK (sw b) r₄ = r₁) :
    twist a r₁ ∘ₗ twist b r₂ = twist b r₃ ∘ₗ twist a r₄ := by
  refine M.ext fun w x => ?_
  simp only [LinearMap.comp_apply, twist_single, perm_scalar_apply, scalar_scalar_apply,
    perm_perm_apply, permK_epow, h₁, h₂, ← mul_assoc, sw_comm hab]
  congr 2
  simp only [epow, desc_sw_mul_of_far hab, desc_sw_mul_of_far (Or.symm hab)]
  ac_rfl

theorem twist_braid (a : ℕ) (r₁ r₂ r₃ r₄ r₅ r₆ : K k)
    (h₁ : r₁ = permK (sw (a + 1) * sw a) r₆) (h₂ : permK (sw a) r₂ = permK (sw (a + 1)) r₅)
    (h₃ : permK (sw a * sw (a + 1)) r₃ = r₄) :
    twist a r₁ ∘ₗ twist (a + 1) r₂ ∘ₗ twist a r₃ =
      twist (a + 1) r₄ ∘ₗ twist a r₅ ∘ₗ twist (a + 1) r₆ := by
  refine M.ext fun w x => ?_
  simp only [LinearMap.comp_apply, twist_single, perm_scalar_apply, scalar_scalar_apply,
    perm_perm_apply, permK_epow, ← mul_assoc, sw_braid]
  congr 2
  simp only [map_mul, permK_epow, ← permK_mul, h₂, ← h₁, h₃]
  simp only [epow, desc_sw_sw_mul, desc_sw_sw_mul', desc_braid]
  ac_rfl

end OddMath.QuiverHecke.Realization
