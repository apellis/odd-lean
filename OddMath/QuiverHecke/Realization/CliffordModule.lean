/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Realization.Coefficients

/-!
# A module for the Clifford algebra, and coordinates on the coefficients

The Clifford algebra `Cl` on the orthonormal generators `c_p` acts on the free module with basis
`e_S`, `S` a finite set of positions: `c_p e_S = ± e_{S △ {p}}`, the sign counting the elements
of `S` below `p` (`gen`). Evaluating at `e_∅` gives coordinates `Φ_S : K ⊗ Cl → K` on the
coefficient module (`coord`); left multiplication by a scalar and by `c_p` act on them by
explicit formulas (`coord_scalar`, `coord_cliff`). These are used to read off coefficients in
the polynomial–Clifford representation of the quiver Hecke supercategory (Kang–Kashiwara–
Tsuchioka, arXiv:1107.1039v2, §3).
-/

noncomputable section
open scoped TensorProduct
namespace OddMath.QuiverHecke.Realization

variable {k : Type*} [CommRing k]

/-! ## Toggling a position -/

/-- `S △ {p}`. -/
def tog (p : ℕ) (S : Finset ℕ) : Finset ℕ := if p ∈ S then S.erase p else insert p S

@[simp] theorem mem_tog {p q : ℕ} {S : Finset ℕ} : q ∈ tog p S ↔ (q ∈ S ↔ q ≠ p) := by
  unfold tog; split_ifs with h
  · simp only [Finset.mem_erase]; constructor
    · rintro ⟨h₁, h₂⟩; exact ⟨fun _ => h₁, fun _ => h₂⟩
    · intro h'; by_cases hq : q = p
      · subst hq; exact absurd (h'.mp h) (by simp)
      · exact ⟨hq, h'.mpr hq⟩
  · simp only [Finset.mem_insert]; constructor
    · rintro (rfl | h₁)
      · exact ⟨fun h' => absurd h' h, fun h' => absurd rfl h'⟩
      · exact ⟨fun _ => fun e => h (e ▸ h₁), fun _ => h₁⟩
    · intro h'; by_cases hq : q = p
      · exact Or.inl hq
      · exact Or.inr (h'.mpr hq)

@[simp] theorem tog_tog (p : ℕ) (S : Finset ℕ) : tog p (tog p S) = S := by
  ext q; simp only [mem_tog]; by_cases h : q = p <;> simp [h]

theorem tog_comm (p q : ℕ) (S : Finset ℕ) : tog p (tog q S) = tog q (tog p S) := by
  ext r; simp only [mem_tog]
  by_cases h : r = p <;> by_cases h' : r = q <;> by_cases hr : r ∈ S <;> simp_all

theorem tog_injective (p : ℕ) : Function.Injective (tog p) := fun S T h => by
  rw [← tog_tog p S, h, tog_tog]

theorem filter_tog_of_lt {p r : ℕ} (h : p < r) (S : Finset ℕ) :
    (tog p S).filter (· < r) = tog p (S.filter (· < r)) := by
  ext q; simp only [Finset.mem_filter, mem_tog]; by_cases hq : q = p
  · subst hq; simp [h]
  · simp [hq]

theorem filter_tog_of_le {p r : ℕ} (h : r ≤ p) (S : Finset ℕ) :
    (tog p S).filter (· < r) = S.filter (· < r) := by
  ext q; simp only [Finset.mem_filter, mem_tog]; by_cases hq : q = p
  · subst hq; simp; omega
  · simp [hq]

theorem neg_one_pow_card_tog (p : ℕ) (S : Finset ℕ) :
    ((-1 : k) ^ (tog p S).card) = -(-1) ^ S.card := by
  unfold tog; split_ifs with h
  · obtain ⟨n, hn⟩ : ∃ n, S.card = n + 1 := ⟨S.card - 1, by have := Finset.card_pos.mpr ⟨p, h⟩; omega⟩
    rw [Finset.card_erase_of_mem h, hn, pow_succ]; simp
  · rw [Finset.card_insert_of_notMem h, pow_succ]; simp

/-! ## The module -/

/-- The sign `(-1)^{#{q ∈ S | q < p}}`. -/
def sgn (p : ℕ) (S : Finset ℕ) : k := (-1) ^ (S.filter (· < p)).card

theorem sgn_mul_self (p : ℕ) (S : Finset ℕ) : sgn (k := k) p S * sgn p S = 1 := by
  rw [sgn, ← pow_add, ← two_mul, pow_mul]; simp

theorem isUnit_sgn (p : ℕ) (S : Finset ℕ) : IsUnit (sgn (k := k) p S) :=
  (Units.mk _ _ (sgn_mul_self p S) (sgn_mul_self p S)).isUnit

@[simp] theorem sgn_tog_self (p : ℕ) (S : Finset ℕ) : sgn (k := k) p (tog p S) = sgn p S := by
  rw [sgn, sgn, filter_tog_of_le le_rfl]

theorem sgn_tog_of_lt {p q : ℕ} (h : q < p) (S : Finset ℕ) :
    sgn (k := k) p (tog q S) = -sgn p S := by
  rw [sgn, sgn, filter_tog_of_lt h, neg_one_pow_card_tog]

theorem sgn_tog_of_le {p q : ℕ} (h : p ≤ q) (S : Finset ℕ) :
    sgn (k := k) p (tog q S) = sgn p S := by
  rw [sgn, sgn, filter_tog_of_le h]

variable (k) in
/-- The free module on finite sets of positions. -/
abbrev Ext := Finset ℕ →₀ k

/-- The generator `c_p` on `Ext`: `e_S ↦ sgn p S • e_{S △ {p}}`. -/
def gen (p : ℕ) : Module.End k (Ext k) :=
  Finsupp.lsum k fun S => (sgn p S : k) • Finsupp.lsingle (tog p S)

@[simp] theorem gen_single (p : ℕ) (S : Finset ℕ) (a : k) :
    gen p (Finsupp.single S a) = Finsupp.single (tog p S) (sgn p S * a) := by
  simp [gen, Finsupp.smul_single]

theorem gen_apply (p : ℕ) (v : Ext k) (S : Finset ℕ) :
    gen p v S = sgn p (tog p S) * v (tog p S) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw, mul_add]
  | single T a =>
    rw [gen_single, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : tog p T = S
    · subst h; simp
    · have h' : T ≠ tog p S := fun e => h (by rw [e, tog_tog])
      simp [h, h']

theorem gen_mul_self (p : ℕ) : gen (k := k) p * gen p = 1 := by
  refine Finsupp.lhom_ext fun S a => ?_
  simp [← mul_assoc, sgn_mul_self]

theorem gen_anticomm {p q : ℕ} (h : p ≠ q) : gen (k := k) p * gen q = -(gen q * gen p) := by
  refine Finsupp.lhom_ext fun S a => ?_
  simp only [Module.End.mul_apply, gen_single, LinearMap.neg_apply, ← Finsupp.single_neg,
    tog_comm p q]
  congr 1
  rcases Nat.lt_or_gt_of_ne h with h | h
  · rw [sgn_tog_of_le h.le, sgn_tog_of_lt h]; ring
  · rw [sgn_tog_of_lt h, sgn_tog_of_le h.le]; ring

theorem dot_single_left (p : ℕ) (a : k) (v : ℕ →₀ k) :
    dot k (Finsupp.single p a) v = a * v p := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw, mul_add]
  | single q b =>
    rw [dot_single, Finsupp.single_apply]
    by_cases h : p = q
    · subst h; simp
    · simp [h, Ne.symm h]

theorem dot_symm (u v : ℕ →₀ k) : dot k u v = dot k v u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => simp [hu, hw]
  | single p a =>
    rw [dot_single_left]
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp [hv, hw, mul_add]
    | single q b => rw [dot_single, Finsupp.single_apply]; by_cases h : q = p <;> simp [h, mul_comm]

/-- `v ↦ ∑ v_p c_p` on `Ext`. -/
def genL : (ℕ →₀ k) →ₗ[k] Module.End k (Ext k) := Finsupp.linearCombination k gen

theorem genL_sq (v : ℕ →₀ k) :
    genL v * genL v = algebraMap k (Module.End k (Ext k)) (form k v) := by
  induction v using Finsupp.induction with
  | zero => simp
  | single_add p a v hp _ ih =>
    have hc : gen p * genL v + genL v * gen (k := k) p = 0 := by
      simp only [genL, Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum,
        Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun q hq => ?_
      have hpq : p ≠ q := fun e => hp (e ▸ hq)
      rw [mul_smul_comm, smul_mul_assoc, ← smul_add, gen_anticomm hpq]
      abel_nf; exact smul_zero _
    have hv : v p = 0 := Finsupp.notMem_support_iff.mp hp
    have hf : form k (Finsupp.single p a + v) = a * a + form k v := by
      simp only [form, LinearMap.BilinMap.toQuadraticMap_apply, map_add, LinearMap.add_apply,
        dot_single_left, hv, dot_symm v (Finsupp.single p a)]
      simp
    have hL : genL (Finsupp.single p a + v) = a • gen (k := k) p + genL v := by
      simp [genL, Finsupp.linearCombination_single]
    rw [hL, hf, map_add, ← ih]
    have hgg : (a • gen (k := k) p) * (a • gen p) = algebraMap k _ (a * a) := by
      rw [smul_mul_smul_comm, gen_mul_self, Algebra.algebraMap_eq_smul_one]
    calc (a • gen p + genL v) * (a • gen p + genL v)
        = (a • gen p) * (a • gen p) + a • (gen p * genL v + genL v * gen p) + genL v * genL v := by
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add]; abel
      _ = _ := by rw [hgg, hc, smul_zero, add_zero]

/-- The representation of the Clifford algebra on `Ext`. -/
def cliffordRep : Cl k →ₐ[k] Module.End k (Ext k) := CliffordAlgebra.lift (form k) ⟨genL, genL_sq⟩

@[simp] theorem cliffordRep_c (p : ℕ) : cliffordRep (c (k := k) p) = gen p := by
  rw [cliffordRep, c, CliffordAlgebra.lift_ι_apply]
  simp [genL, Finsupp.linearCombination_single]

/-- `u ↦ u · e_∅`. -/
def vac : Cl k →ₗ[k] Ext k :=
  (LinearMap.applyₗ (Finsupp.single ∅ 1)) ∘ₗ cliffordRep.toLinearMap

theorem vac_c_mul (p : ℕ) (u : Cl k) : vac (c p * u) = gen p (vac u) := by
  simp [vac]

@[simp] theorem vac_one : vac (1 : Cl k) = Finsupp.single ∅ 1 := by simp [vac]

/-! ## Coordinates on `K ⊗ Cl` -/

/-- The coordinate `Φ_S : K ⊗ Cl → K`, `f ⊗ u ↦ (u e_∅)_S f`. -/
def coord (S : Finset ℕ) : Coeff k →ₗ[k] K k :=
  TensorProduct.lift (LinearMap.mk₂ k (fun f u => vac u S • f)
    (fun f f' u => smul_add _ _ _) (fun a f u => smul_comm _ _ _)
    (fun f u u' => by simp [add_smul]) (fun a f u => by simp [smul_smul]))

@[simp] theorem coord_tmul (S : Finset ℕ) (f : K k) (u : Cl k) :
    coord S (f ⊗ₜ u) = vac u S • f := by
  simp [coord]

theorem coord_scalar (S : Finset ℕ) (g : K k) (x : Coeff k) :
    coord S (scalar g x) = g * coord S x := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp [hx, hx', mul_add]
  | tmul f u => simp

theorem coord_cliff (S : Finset ℕ) (p : ℕ) (x : Coeff k) :
    coord S (cliff p x) = (sgn p (tog p S) : k) • reflect p (coord (tog p S) x) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp [hx, hx', smul_add]
  | tmul f u => simp [vac_c_mul, gen_apply, mul_smul, map_smul]

end OddMath.QuiverHecke.Realization
