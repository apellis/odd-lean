import OddMath.Frontier.EKFreeCoproduct
import OddMath.Frontier.EKPairingMatrices

/-!
EK 1107.5610v2 §2.1 (2.2), Proposition 2.2 (2.3), integer q=-1.
The form here is defined by the genuine nonnegative-margin matrix coefficients.
Identification with the source double cosets is a separate obligation. No quotient
or general-q assertion is made. Tensor pairing is UNSIGNED, unlike multiplication.
-/
noncomputable section
open scoped TensorProduct BigOperators
namespace OddMath.Frontier.EKPairingAdjoint
open CompleteElementary EKFreeCoproduct
attribute [local instance] Classical.propDecidable

/-- Ordered product, including empty products and zero parts h₀=1. -/
def vWord {n : ℕ} (α : Fin n → ℕ) : A := hWord (List.ofFn α)

def parts (w : W) : Fin w.toList.length → ℕ := fun i => w.toList.get i + 1

def pairing : A →ₗ[ℤ] A →ₗ[ℤ] ℤ :=
  wordBasis.constr ℤ fun v => wordBasis.constr ℤ fun w => EKPairingMatrices.pairing (parts v) (parts w)

@[simp] theorem pairing_basis (v w : W) :
    pairing (wordBasis v) (wordBasis w) = EKPairingMatrices.pairing (parts v) (parts w) := by
  simp [pairing]

theorem basis_induction {I X : Type*} [AddCommGroup X] (b : Basis I ℤ X)
    (P : X → Prop) (hz : P 0) (ha : ∀ x y, P x → P y → P (x+y))
    (hb : ∀ i (r : ℤ), P (r • b i)) (x : X) : P x := by
  obtain ⟨f, rfl⟩ := b.repr.symm.surjective x
  induction f using Finsupp.induction_linear with
  | zero => simpa using hz
  | add f g hf hg => simpa using ha _ _ hf hg
  | single i r => simpa using hb i r

theorem pairing_symm (x y : A) : pairing x y = pairing y x := by
  induction x using basis_induction wordBasis with
  | hz => simp
  | ha x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | hb v r =>
    induction y using basis_induction wordBasis with
    | hz => simp
    | ha y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
    | hb w s => simp only [map_smul, LinearMap.smul_apply, pairing_basis, smul_eq_mul,
        EKPairingMatrices.pairing_transpose (parts v) (parts w)]; ring

@[simp] theorem vWord_nil (α : Fin 0 → ℕ) : vWord α = 1 := by
  simp [vWord, hWord]

@[simp] theorem vWord_cons {n : ℕ} (a : ℕ) (α : Fin n → ℕ) :
    vWord (Fin.cons a α) = h a * vWord α := by
  simp [vWord, List.ofFn_succ, hWord]

theorem vWord_succ {n : ℕ} (α : Fin (n+1) → ℕ) :
    vWord α = h (α 0) * vWord (fun i => α i.succ) := by
  simp [vWord, List.ofFn_succ, hWord]

theorem vWord_erase_zero {n : ℕ} (α : Fin (n+1) → ℕ) (p : Fin (n+1)) (hp : α p = 0) :
    vWord α = vWord (fun i => α (p.succAbove i)) := by
  induction n with
  | zero =>
    have hα : α = fun _ => 0 := by funext i; have hi : i = p := Fin.ext (by omega); simpa [hi] using hp
    simp [hα, vWord, List.ofFn_succ, hWord]
  | succ n ih =>
    revert hp
    refine Fin.cases ?_ (fun p => ?_) p
    · intro hp
      rw [vWord_succ, hp, h_zero, one_mul]
      rfl
    · intro hp
      conv_lhs => rw [vWord_succ]
      conv_rhs => rw [vWord_succ]
      simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
      rw [ih (fun i => α i.succ) p hp]

@[simp] theorem vWord_parts (w : W) : vWord (parts w) = wordBasis w := by
  have hl : List.ofFn (parts w) = w.toList.map (·+1) := by
    exact List.ext_get (by simp) (by intro n h₁ h₂; simp [parts])
  rw [vWord, hl, ← partWord_value]
  congr 1
  clear hl
  induction w using FreeMonoid.recOn with
  | h0 => rfl
  | ih i w ih => simpa [partWord] using congrArg (FreeMonoid.of i * ·) ih

theorem partWord_positive (α : List ℕ) (hα : ∀ a ∈ α, 0 < a) :
    (partWord α).toList = α.map Nat.pred := by
  induction α with
  | nil => rfl
  | cons a α ih =>
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hα a (by simp)))
    simp only [partWord, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append,
      List.map_cons, Nat.pred_succ]
    rw [ih (by intro b hb; exact hα b (by simp [hb]))]

theorem pairing_vWord_positive {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (hβ : ∀ i, 0 < β i) (hα : ∀ i, 0 < α i) :
    pairing (vWord β) (vWord α) = EKPairingMatrices.pairing β α := by
  have hb := partWord_positive (List.ofFn β) (by simpa using hβ)
  have ha := partWord_positive (List.ofFn α) (by simpa using hα)
  rw [vWord, vWord, ← partWord_value, ← partWord_value, pairing_basis]
  unfold parts
  simp only [hb, ha, List.length_map, List.length_ofFn, List.get_eq_getElem,
    List.getElem_map, List.getElem_ofFn]
  congr 1
  · simp [hb]
  · simp [ha]
  · apply Function.hfunext (by simp [hb])
    intro i j hij
    have hv : i.val = j.val := Fin.val_eq_val_of_heq hij
    have he : (⟨i.val, by simpa [hb] using i.isLt⟩ : Fin r) = j := Fin.ext hv
    simpa only [he, heq_eq_eq] using Nat.succ_pred_eq_of_pos (hβ j)
  · apply Function.hfunext (by simp [ha])
    intro i j hij
    have hv : i.val = j.val := Fin.val_eq_val_of_heq hij
    have he : (⟨i.val, by simpa [ha] using i.isLt⟩ : Fin c) = j := Fin.ext hv
    simpa only [he, heq_eq_eq] using Nat.succ_pred_eq_of_pos (hα j)

/-- Zero platforms are erased, not treated as extra free generators. -/
theorem pairing_vWord {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    pairing (vWord β) (vWord α) = EKPairingMatrices.pairing β α := by
  induction r generalizing c with
  | zero =>
    induction c with
    | zero => exact pairing_vWord_positive β α (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    | succ c ih =>
      by_cases hz : ∃ p, α p = 0
      · obtain ⟨p, hp⟩ := hz
        rw [vWord_erase_zero α p hp, EKPairingMatrices.pairing_erase_zero_column β α p hp]
        exact ih _
      · exact pairing_vWord_positive β α (fun i => Fin.elim0 i)
          (fun i => Nat.pos_of_ne_zero (fun h => hz ⟨i,h⟩))
  | succ r ih =>
    by_cases hz : ∃ p, β p = 0
    · obtain ⟨p, hp⟩ := hz
      rw [vWord_erase_zero β p hp, EKPairingMatrices.pairing_erase_zero_row β α p hp]
      exact ih _ _
    · have hb : ∀ i, 0 < β i := fun i => Nat.pos_of_ne_zero (fun h => hz ⟨i,h⟩)
      induction c with
      | zero => exact pairing_vWord_positive β α hb (fun i => Fin.elim0 i)
      | succ c ihc =>
        by_cases hz : ∃ p, α p = 0
        · obtain ⟨p, hp⟩ := hz
          rw [vWord_erase_zero α p hp, EKPairingMatrices.pairing_erase_zero_column β α p hp]
          exact ihc _
        · exact pairing_vWord_positive β α hb (fun i => Nat.pos_of_ne_zero (fun h => hz ⟨i,h⟩))

/-- Source (2.2): the tensor form has no extra Koszul sign. -/
def tensorPairing : T →ₗ[ℤ] T →ₗ[ℤ] ℤ := TensorProduct.lift
  { toFun := fun a =>
      { toFun := fun b => TensorProduct.lift
          ((LinearMap.mul ℤ ℤ).compl₁₂ (pairing a) (pairing b))
        map_add' := by intros b c; ext x y; simp [mul_add]
        map_smul' := by
          intros r b; ext x y
          change pairing a x * pairing (r • b) y = r • (pairing a x * pairing b y)
          simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
          ring }
    map_add' := by intros a b; ext c x y; simp [add_mul]
    map_smul' := by
      intros r a; ext b x y
      change pairing (r • a) x * pairing b y = r • (pairing a x * pairing b y)
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring }

@[simp] theorem tensorPairing_tmul (a b c d : A) :
    tensorPairing (a ⊗ₜ[ℤ] b) (c ⊗ₜ[ℤ] d) = pairing a c * pairing b d := by
  simp [tensorPairing]

theorem vWord_join {r s : ℕ} (β : Fin r → ℕ) (γ : Fin s → ℕ) :
    vWord (Fin.addCases β γ) = vWord β * vWord γ := by
  have hw (a b : List ℕ) : hWord (a ++ b) = hWord a * hWord b := by
    induction a with
    | nil => simp [hWord]
    | cons n a ih => simp [hWord, ih, mul_assoc]
  unfold vWord
  rw [List.ofFn_add]
  simpa using hw (List.ofFn β) (List.ofFn γ)

@[simp] theorem vWord_singleton (n : ℕ) : vWord (fun _ : Fin 1 => n) = h n := by
  simp [vWord, List.ofFn_succ, hWord]

theorem tensorMul_vWords {r s c d : ℕ} (α : Fin r → ℕ) (β : Fin s → ℕ)
    (γ : Fin c → ℕ) (δ : Fin d → ℕ) :
    tensorMul (vWord α ⊗ₜ[ℤ] vWord β) (vWord γ ⊗ₜ[ℤ] vWord δ) =
      (-1 : ℤ)^((∑ i, β i)*(∑ j, γ j)) •
        ((vWord α * vWord γ) ⊗ₜ[ℤ] (vWord β * vWord δ)) := by
  simpa only [vWord, List.sum_ofFn] using
    tensorMul_hWords (List.ofFn α) (List.ofFn β) (List.ofFn γ) (List.ofFn δ)

theorem crossCols_succ {n : ℕ} (u v : Fin (n+1) → ℕ) :
    EKPairingMatrices.crossCols u v =
      (∑ j : Fin n, u j.succ) * v 0 +
        EKPairingMatrices.crossCols (fun j => u j.succ) (fun j => v j.succ) := by
  simp only [EKPairingMatrices.crossCols, Fin.sum_univ_succ, Fin.not_lt_zero,
    if_false, Finset.sum_const_zero, zero_add, Fin.succ_pos, if_true,
    Fin.succ_lt_succ_iff, Finset.sum_add_distrib, Finset.sum_mul]

/-- All coordinate splits, with the crossings forced by signed multiplication. -/
theorem coproduct_vWord {c : ℕ} (α : Fin c → ℕ) :
    coproduct (vWord α) =
      ∑ u : EKPairingMatrices.Splits α,
        (-1 : ℤ)^EKPairingMatrices.crossCols (EKPairingMatrices.upper u) (EKPairingMatrices.lower u) •
          (vWord (EKPairingMatrices.upper u) ⊗ₜ[ℤ] vWord (EKPairingMatrices.lower u)) := by
  induction c with
  | zero => simp [EKPairingMatrices.crossCols, tensorOne]
  | succ c ih =>
    rw [vWord_succ, coproduct_mul, coproduct_h, ih]
    rw [← (Fin.insertNthEquiv (fun j => Fin (α j + 1)) 0).sum_comp]
    simp only [Fintype.sum_prod_type]
    simp only [tensorMul, map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro u _
    change tensorMul _ _ = _
    rw [tensorMul_smul_right]
    have hm := tensorMul_vWords (fun _ : Fin 1 => i.val)
      (fun _ : Fin 1 => α 0-i.val) (EKPairingMatrices.upper u) (EKPairingMatrices.lower u)
    simp only [vWord_singleton, Fin.sum_univ_one] at hm
    rw [hm]
    simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero, crossCols_succ,
      Fin.cons_zero, Fin.cons_succ, vWord_succ, pow_add, smul_smul]
    congr 1
    change (-1 : ℤ)^EKPairingMatrices.crossCols (EKPairingMatrices.upper u) (EKPairingMatrices.lower u) *
      (-1)^((α 0-i.val)*(∑ j, (u j).val)) =
      (-1)^((∑ j, (u j).val)*(α 0-i.val)) *
      (-1)^EKPairingMatrices.crossCols (EKPairingMatrices.upper u) (EKPairingMatrices.lower u)
    rw [Nat.mul_comm]
    ring

/-- Matrix convolution evaluated on actual ordered products. -/
theorem adjointness_vWords {r s c : ℕ} (β : Fin r → ℕ) (γ : Fin s → ℕ) (α : Fin c → ℕ) :
    tensorPairing (vWord β ⊗ₜ[ℤ] vWord γ) (coproduct (vWord α)) =
      pairing (vWord β * vWord γ) (vWord α) := by
  rw [coproduct_vWord, ← vWord_join, pairing_vWord, EKPairingMatrices.pairing_convolution]
  simp only [map_sum, map_smul, tensorPairing_tmul, pairing_vWord, smul_eq_mul, mul_assoc]

theorem adjointness_basis (u v w : W) :
    tensorPairing (wordBasis u ⊗ₜ[ℤ] wordBasis v) (coproduct (wordBasis w)) =
      pairing (wordBasis u * wordBasis v) (wordBasis w) := by
  simpa only [vWord_parts] using adjointness_vWords (parts u) (parts v) (parts w)

/-- Genuine universal bilinear adjointness on the actual free algebra and tensor module. -/
theorem adjointness (x y₁ y₂ : A) :
    tensorPairing (y₁ ⊗ₜ[ℤ] y₂) (coproduct x) = pairing (y₁*y₂) x := by
  induction x using basis_induction wordBasis with
  | hz => simp
  | ha x z hx hz => simp only [map_add, hx, hz]
  | hb w r =>
    simp only [map_smul]
    congr 1
    induction y₁ using basis_induction wordBasis with
    | hz => simp
    | ha a b ha hb =>
      simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, add_mul, ha, hb]
    | hb u s =>
      simp only [← TensorProduct.smul_tmul', map_smul, LinearMap.smul_apply, smul_mul_assoc]
      congr 1
      induction y₂ using basis_induction wordBasis with
      | hz => simp
      | ha a b ha hb =>
        simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, mul_add, ha, hb]
      | hb v t =>
        simp only [TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply, mul_smul_comm]
        rw [adjointness_basis]

@[simp] theorem parts_sum (w : W) : (∑ i, parts w i) = degree w := by
  rw [← List.sum_ofFn]
  have hl : List.ofFn (parts w) = w.toList.map (·+1) := by
    exact List.ext_get (by simp) (by intro n h₁ h₂; simp [parts])
  rw [hl]
  rfl

theorem pairing_degree_mismatch (v w : W) (hne : degree v ≠ degree w) :
    pairing (wordBasis v) (wordBasis w) = 0 := by
  rw [pairing_basis]
  apply EKPairingMatrices.pairing_degree_mismatch
  simpa only [parts_sum] using hne

theorem pairing_one_one : pairing (1 : A) 1 = 1 := by
  have hh := EKPairingMatrices.pairing_zero_zero 0 0
  have e : parts (1 : W) = (fun _ : Fin 0 => 0) := funext fun i => Fin.elim0 i
  simpa only [← wordBasis_one, pairing_basis, e] using hh

theorem pairing_one_basis (w : W) : pairing 1 (wordBasis w) = counit (wordBasis w) := by
  by_cases hw : w = 1
  · subst w; simpa using pairing_one_one
  · rw [counit_word, if_neg hw]
    rw [← wordBasis_one]
    apply pairing_degree_mismatch
    have hd : degree w ≠ 0 := by
      intro he
      apply hw
      induction w using FreeMonoid.recOn with
      | h0 => rfl
      | ih i w ih =>
        simp only [degree_mul] at he
        have hi : degree (FreeMonoid.of i) = i+1 := rfl
        rw [hi] at he
        omega
    simpa only [degree_one, ne_eq, eq_comm] using hd

theorem pairing_one (x : A) : pairing 1 x = counit x := by
  induction x using basis_induction wordBasis with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx, hy]
  | hb w r => simp only [map_smul, pairing_one_basis]

theorem pairing_right_one (x : A) : pairing x 1 = counit x := by
  rw [pairing_symm, pairing_one]

/-- Literal lists, with every zero part retained as the unit in the statement. -/
theorem pairing_hWords (β α : List ℕ) :
    pairing (hWord β) (hWord α) = EKPairingMatrices.pairing β.get α.get := by
  simpa only [vWord, List.ofFn_get] using pairing_vWord β.get α.get

theorem pairing_vWord_degree_mismatch {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (hne : (∑ i, β i) ≠ ∑ j, α j) : pairing (vWord β) (vWord α) = 0 := by
  rw [pairing_vWord]
  exact EKPairingMatrices.pairing_degree_mismatch β α hne

@[simp] theorem pairing_h_self (n : ℕ) : pairing (h n) (h n) = 1 := by
  have hh := EKPairingMatrices.pairing_single_row (fun _ : Fin 1 => n)
  simpa only [Fin.sum_univ_one, ← pairing_vWord, vWord_singleton] using hh

/-- A genuine consumer: arbitrary left factors paired against any complete generator. -/
theorem pairing_product_h (y₁ y₂ : A) (n : ℕ) :
    pairing (y₁*y₂) (h n) =
      ∑ i : Fin (n+1), pairing y₁ (h i.val) * pairing y₂ (h (n-i.val)) := by
  rw [← adjointness, coproduct_h]
  simp only [map_sum, tensorPairing_tmul]

theorem tensorPairing_symm (x y : T) : tensorPairing x y = tensorPairing y x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
    | tmul c d => simp only [tensorPairing_tmul, pairing_symm a c, pairing_symm b d]

/-- Distinct actual homogeneous word spans are orthogonal, including sums and scalars. -/
theorem pairing_homogeneous_orthogonal {m n : ℕ} {x y : A} (hne : m ≠ n)
    (hx : x ∈ Submodule.span ℤ {z | ∃ w : W, degree w = m ∧ wordBasis w = z})
    (hy : y ∈ Submodule.span ℤ {z | ∃ w : W, degree w = n ∧ wordBasis w = z}) :
    pairing x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, hv, rfl⟩ := hz
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      exact pairing_degree_mismatch v w (by simpa only [hv, hw] using hne)
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, ha, hb, add_zero]
    | smul r a _ ha => simp only [map_smul, ha, smul_zero]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul r a _ ha => simp only [map_smul, LinearMap.smul_apply, ha, smul_zero]

end OddMath.Frontier.EKPairingAdjoint
