import OddMath.Frontier.EKSignedQuotient
import Mathlib.RingTheory.PowerSeries.Inverse

/-! EK 1107.5610v2 §2.2, Proposition 2.5, over ℤ at q=-1.
The formal series below are only a proof device in the actual free algebra.
The public results descend to the inherited actual radical quotient. -/
noncomputable section
open scoped BigOperators TensorProduct
namespace OddMath.Frontier.EKElementaryQuotient
open CompleteElementary EKFreeCoproduct EKPairingAdjoint EKRadicalQuotient EKCoideal

/-- The actual elementary image, with the inherited EK normalization. -/
def e (n : ℕ) : Q := pi (elementary n)
/-- The actual complete image. -/
def h (n : ℕ) : Q := pi (CompleteElementary.h n)

private theorem tensorMul_outer (a b : A) :
    tensorMul (a ⊗ₜ[ℤ] 1) (1 ⊗ₜ[ℤ] b) = a ⊗ₜ[ℤ] b := by
  induction a using EKPairingAdjoint.basis_induction wordBasis with
  | hz => simp
  | ha a c ha hc => simp [ha, hc, TensorProduct.add_tmul]
  | hb u r =>
    induction b using EKPairingAdjoint.basis_induction wordBasis with
    | hz => simp
    | ha b c hb hc => simp only [hb, hc, tensorMul_add_right, TensorProduct.tmul_add]
    | hb v s =>
      simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
        tensorMul_smul_left, tensorMul_smul_right]
      congr 1; congr 1
      have hh := tensorMul_basis (u,1) (1,v)
      simpa using hh

private theorem tensorMul_left (a b : A) :
    tensorMul (a ⊗ₜ[ℤ] 1) (b ⊗ₜ[ℤ] 1) = (a*b) ⊗ₜ[ℤ] 1 := by
  induction a using EKPairingAdjoint.basis_induction wordBasis with
  | hz => simp
  | ha a c ha hc => simp [ha, hc, TensorProduct.add_tmul, add_mul]
  | hb u r =>
    induction b using EKPairingAdjoint.basis_induction wordBasis with
    | hz => simp
    | ha b c hb hc => simp only [hb, hc, tensorMul_add_right, TensorProduct.add_tmul, mul_add]
    | hb v s =>
      simp only [← TensorProduct.smul_tmul', tensorMul_smul_left,
        tensorMul_smul_right, smul_mul_assoc, mul_smul_comm]
      have hh := tensorMul_basis (u,1) (v,1)
      simpa using congrArg (fun z => s • r • z) hh

private theorem tensorMul_right (a b : A) :
    tensorMul (1 ⊗ₜ[ℤ] a) (1 ⊗ₜ[ℤ] b) = 1 ⊗ₜ[ℤ] (a*b) := by
  induction a using EKPairingAdjoint.basis_induction wordBasis with
  | hz => simp
  | ha a c ha hc => simp [ha, hc, TensorProduct.tmul_add, add_mul]
  | hb u r =>
    induction b using EKPairingAdjoint.basis_induction wordBasis with
    | hz => simp
    | ha b c hb hc => simp only [hb, hc, tensorMul_add_right, TensorProduct.tmul_add, mul_add]
    | hb v s =>
      simp only [TensorProduct.tmul_smul, tensorMul_smul_left,
        tensorMul_smul_right, smul_mul_assoc, mul_smul_comm]
      have hh := tensorMul_basis (1,u) (1,v)
      simpa using congrArg (fun z => s • r • z) hh

private def leftIn : A →+* SignedTensor where
  toFun a := a ⊗ₜ[ℤ] 1
  map_zero' := TensorProduct.zero_tmul _ _
  map_one' := rfl
  map_add' _ _ := TensorProduct.add_tmul _ _ _
  map_mul' a b := (tensorMul_left a b).symm

private def rightIn : A →+* SignedTensor where
  toFun a := 1 ⊗ₜ[ℤ] a
  map_zero' := TensorProduct.tmul_zero _ _
  map_one' := rfl
  map_add' _ _ := TensorProduct.tmul_add _ _ _
  map_mul' a b := (tensorMul_right a b).symm

private def H : PowerSeries A := PowerSeries.mk CompleteElementary.h
private def I : PowerSeries A := PowerSeries.mk inverseCoeff

private theorem coeff_mul_fin {R : Type*} [Semiring R]
    (f g : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff R n (f*g) =
      ∑ i : Fin (n+1), PowerSeries.coeff R i f * PowerSeries.coeff R (n-i) g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Fin.sum_univ_eq_sum_range]

private theorem I_mul_H : I * H = 1 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_mul_fin, PowerSeries.coeff_one]
  simp only [I, H, PowerSeries.coeff_mk]
  cases n with
  | zero => simp [inverseCoeff]
  | succ n =>
    rw [if_neg (Nat.succ_ne_zero n), Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last, Nat.sub_self,
      CompleteElementary.h_zero, mul_one]
    rw [inverseCoeff]
    exact add_neg_cancel _

private theorem H_mul_I : H * I = 1 := by
  have hh := PowerSeries.mul_invOfUnit H 1 (by rfl)
  have hi : I = PowerSeries.invOfUnit H 1 := by
    calc
      I = I * (H * PowerSeries.invOfUnit H 1) := by rw [hh, mul_one]
      _ = PowerSeries.invOfUnit H 1 := by rw [← mul_assoc, I_mul_H, one_mul]
  rw [hi]; exact hh

private theorem delta_H :
    PowerSeries.map coproductAlg.toRingHom H =
      PowerSeries.map leftIn H * PowerSeries.map rightIn H := by
  apply PowerSeries.ext
  intro n
  rw [coeff_mul_fin]
  simp only [PowerSeries.coeff_map, H, PowerSeries.coeff_mk]
  change coproduct (CompleteElementary.h n) = _
  rw [coproduct_h]
  apply Finset.sum_congr rfl
  intro i _
  exact (tensorMul_outer _ _).symm

/-- Inverse order is essential: Δ(I)=R(I)L(I), not L(I)R(I). -/
private theorem delta_I :
    PowerSeries.map coproductAlg.toRingHom I =
      PowerSeries.map rightIn I * PowerSeries.map leftIn I := by
  let D := PowerSeries.map coproductAlg.toRingHom
  let L := PowerSeries.map leftIn
  let R := PowerSeries.map rightIn
  have hd : D I * D H = 1 := by rw [← map_mul, I_mul_H, map_one]
  have he : D H * (R I * L I) = 1 := by
    change (PowerSeries.map coproductAlg.toRingHom H) * _ = _
    rw [delta_H]
    change (L H * R H) * (R I * L I) = 1
    calc
      _ = L H * (R H * R I) * L I := by simp only [mul_assoc]
      _ = 1 := by rw [← map_mul, H_mul_I, map_one, mul_one,
        ← map_mul, H_mul_I, map_one]
  change D I = R I * L I
  calc
    D I = D I * (D H * (R I * L I)) := by rw [he, mul_one]
    _ = _ := by rw [← mul_assoc, hd, one_mul]

/-- Homogeneous submodule of the actual free word algebra. -/
def weight (n : ℕ) : Submodule ℤ A :=
  Submodule.span ℤ {z | ∃ w : W, degree w = n ∧ wordBasis w = z}

private theorem hWord_weight (α : List ℕ) : hWord α ∈ weight α.sum :=
  Submodule.subset_span ⟨partWord α, partWord_degree α, partWord_value α⟩

private theorem inverseCoeff_weight (n : ℕ) : inverseCoeff n ∈ weight n := by
  rw [inverseCoeff_composition_expansion]
  apply Submodule.sum_mem
  intro α hα
  have hh := hWord_weight α
  rw [(composition_sound n α hα).2] at hh
  have he : signedWord α = (-1 : ℤ)^α.length • hWord α := by
    simp [signedWord, zsmul_eq_mul]
  rw [he]
  exact Submodule.smul_mem _ _ hh

/-- Inherited elementary elements are genuinely homogeneous, not assumed so. -/
theorem elementary_weight (n : ℕ) : elementary n ∈ weight n := by
  have he : elementary n = (-1 : ℤ)^((n+1).choose 2) • inverseCoeff n := by
    simp [elementary, ekSign, zsmul_eq_mul]
  rw [he]
  exact Submodule.smul_mem _ _ (inverseCoeff_weight n)

private theorem tensorMul_reverse {m n : ℕ} {a b : A}
    (ha : a ∈ weight m) (hb : b ∈ weight n) :
    tensorMul (1 ⊗ₜ[ℤ] b) (a ⊗ₜ[ℤ] 1) = (-1 : ℤ)^(n*m) • (a ⊗ₜ[ℤ] b) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨v, hv, rfl⟩ := hb
      have hh := tensorMul_basis (1,v) (u,1)
      simpa only [tensorBasis_apply, wordBasis_one, one_mul, mul_one, hu, hv] using hh
    | zero => simp
    | add b c _ _ hb hc =>
      simp only [TensorProduct.tmul_add, tensorMul_add_left, hb, hc, smul_add]
    | smul r b _ hb =>
      simp only [TensorProduct.tmul_smul, tensorMul_smul_left, hb, smul_comm r]
  | zero => simp
  | add a c _ _ ha hc =>
    simp only [TensorProduct.add_tmul, tensorMul_add_right, ha, hc, smul_add]
  | smul r a _ ha =>
    simp only [← TensorProduct.smul_tmul', tensorMul_smul_right, ha, smul_comm r]

private theorem coproduct_inverseCoeff (n : ℕ) :
    coproduct (inverseCoeff n) = ∑ i : Fin (n+1),
      (-1 : ℤ)^(i.val*(n-i.val)) • (inverseCoeff (n-i.val) ⊗ₜ[ℤ] inverseCoeff i.val) := by
  have hh := congrArg (PowerSeries.coeff SignedTensor n) delta_I
  rw [coeff_mul_fin] at hh
  simp only [PowerSeries.coeff_map, I, PowerSeries.coeff_mk] at hh
  change coproduct (inverseCoeff n) = _ at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro i _
  exact tensorMul_reverse (inverseCoeff_weight _) (inverseCoeff_weight _)

private theorem tri_add (a b : ℕ) :
    (a+b+1).choose 2 = (a+1).choose 2 + (b+1).choose 2 + a*b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hh := Nat.choose_succ_succ (a+b+1) 1
    have hk := Nat.choose_succ_succ (b+1) 1
    simp only [Nat.choose_one_right] at hh hk
    simp only [Nat.succ_eq_add_one] at *
    have he : a + (b+1) + 1 = a+b+1+1 := by omega
    rw [he, hh, hk, ih]
    ring

private theorem sign_square (n : ℕ) : (-1 : ℤ)^n * (-1 : ℤ)^n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/-- Stronger free-algebra identity, proved by reversed formal-series inversion.
No quotient relation is used in this statement or its proof. -/
theorem coproduct_elementary (n : ℕ) :
    coproduct (elementary n) = ∑ i : Fin (n+1), elementary i ⊗ₜ[ℤ] elementary (n-i) := by
  have norm (k : ℕ) : elementary k = (-1 : ℤ)^((k+1).choose 2) • inverseCoeff k := by
    simp [elementary, ekSign, zsmul_eq_mul]
  rw [norm, map_smul, coproduct_inverseCoeff, Finset.smul_sum]
  have hr : (∑ i : Fin (n+1), elementary (n-i) ⊗ₜ[ℤ] elementary i) =
      ∑ i : Fin (n+1), elementary i ⊗ₜ[ℤ] elementary (n-i) := by
    apply Fintype.sum_equiv (Equiv.refl (Fin (n+1)) |>.trans (Fin.revPerm))
    intro i
    simp only [Equiv.trans_apply, Equiv.refl_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 2 <;> omega
  rw [← hr]
  apply Finset.sum_congr rfl
  intro i _
  rw [norm, norm, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
    smul_smul]
  congr 1
  have he : n = (n-i.val)+i.val := by omega
  have ht := tri_add (n-i.val) i.val
  rw [← he] at ht
  rw [ht, pow_add, pow_add]
  have hs := sign_square (i.val*(n-i.val))
  rw [Nat.mul_comm (n-i.val) i.val]
  calc
    _ = ((-1 : ℤ)^((n-i.val+1).choose 2) * (-1 : ℤ)^((i.val+1).choose 2)) *
      ((-1 : ℤ)^(i.val*(n-i.val)) * (-1 : ℤ)^(i.val*(n-i.val))) := by ring
    _ = _ := by rw [hs, mul_one]

/-- EK Proposition 2.5(1), on precisely the actual radical quotient. -/
theorem quotientCoproduct_e (n : ℕ) :
    quotientCoproduct (e n) = ∑ i : Fin (n+1), e i ⊗ₜ[ℤ] e (n-i) := by
  simp only [e, quotientCoproduct_pi, coproduct_elementary, map_sum,
    quotientTensorMap_tmul]

private def character : A →ₐ[ℤ] ℤ := FreeAlgebra.lift ℤ (fun _ => 1)

private theorem character_h (n : ℕ) : character (CompleteElementary.h n) = 1 := by
  cases n with
  | zero => exact character.map_one
  | succ n => exact FreeAlgebra.lift_ι_apply _ n

private theorem character_word (w : W) : character (wordBasis w) = 1 := by
  induction w using FreeMonoid.recOn with
  | h0 => simp
  | ih i w ih => rw [wordBasis_mul, map_mul, wordBasis_of, character_h, ih, one_mul]

private theorem pairing_h_weight {n : ℕ} {x : A} (hx : x ∈ weight n) :
    pairing (CompleteElementary.h n) x = character x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [character_word]
    have hh := EKPairingMatrices.pairing_single_row (parts w)
    rw [← pairing_vWord, vWord_singleton, vWord_parts, EKPairingAdjoint.parts_sum, hw] at hh
    exact hh
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, ha, hb]
  | smul r a _ ha => simp only [map_smul, ha]

private theorem character_I : PowerSeries.map character.toRingHom I = 1 - PowerSeries.X := by
  let C := PowerSeries.map character.toRingHom
  have hi : C I * C H = 1 := by rw [← map_mul, I_mul_H, map_one]
  have hh : C H * (1 - PowerSeries.X) = 1 := by
    apply PowerSeries.ext
    intro n
    rw [mul_sub, mul_one, map_sub]
    cases n with
    | zero => simp [C, H, PowerSeries.coeff_map, PowerSeries.coeff_zero_mul_X, character_h]
    | succ n =>
      rw [PowerSeries.coeff_succ_mul_X]
      simp [C, H, PowerSeries.coeff_map, PowerSeries.coeff_mk, character_h,
        PowerSeries.coeff_one]
  change C I = _
  calc
    C I = C I * (C H * (1 - PowerSeries.X)) := by rw [hh, mul_one]
    _ = _ := by rw [← mul_assoc, hi, one_mul]

private theorem character_elementary (n : ℕ) :
    character (elementary n) = if n ≤ 1 then 1 else 0 := by
  have hh := congrArg (PowerSeries.coeff ℤ n) character_I
  simp only [PowerSeries.coeff_map, I, PowerSeries.coeff_mk, map_sub,
    PowerSeries.coeff_one, PowerSeries.coeff_X] at hh
  change character (inverseCoeff n) = _ at hh
  rw [elementary, map_mul, ekSign, map_pow, map_neg, map_one, hh]
  by_cases hn : n ≤ 1
  · interval_cases n <;> norm_num
  · have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp [hn, h0, h1]

/-- Complete-versus-elementary pairing, with every weight explicit. -/
theorem pairing_h_elementary (m n : ℕ) :
    pairing (CompleteElementary.h m) (elementary n) =
      if m = n ∧ n ≤ 1 then 1 else 0 := by
  by_cases hm : m = n
  · subst m
    rw [pairing_h_weight (elementary_weight n), character_elementary]
    simp
  · rw [if_neg (fun hh => hm hh.1)]
    apply pairing_homogeneous_orthogonal hm
    · simpa [hWord] using hWord_weight [m]
    · exact elementary_weight n

/-- Multiplication adjointness plus the proved coproduct gives the actual recursion. -/
theorem pairing_cons (m : ℕ) (α : List ℕ) (n : ℕ) :
    pairing (hWord (m :: α)) (elementary n) =
      ∑ i : Fin (n+1), pairing (CompleteElementary.h m) (elementary i) *
        pairing (hWord α) (elementary (n-i)) := by
  have hh : hWord (m :: α) = CompleteElementary.h m * hWord α := by simp [hWord]
  rw [hh, ← adjointness, coproduct_elementary]
  simp only [map_sum, tensorPairing_tmul]

/-- All positive compositions in all weights, not just the weight-n tests. -/
theorem pairing_hWord_elementary (α : List ℕ) (hp : ∀ a ∈ α, 0 < a) (n : ℕ) :
    pairing (hWord α) (elementary n) =
      if α.sum = n ∧ (∀ a ∈ α, a = 1) then 1 else 0 := by
  classical
  induction α generalizing n with
  | nil =>
    have hh := pairing_h_elementary 0 n
    by_cases hn : n = 0
    · subst n; simpa [hWord] using hh
    · simpa [hWord, hn, Ne.symm hn] using hh
  | cons m α ih =>
    have hm : 0 < m := hp m (by simp)
    have hα : ∀ a ∈ α, 0 < a := fun a ha => hp a (by simp [ha])
    rw [pairing_cons]
    by_cases hm1 : m = 1
    · subst m
      cases n with
      | zero =>
        simp only [Fin.sum_univ_one, Fin.val_zero, Nat.sub_zero, pairing_h_elementary]
        simp
      | succ n =>
        rw [Finset.sum_eq_single (⟨1, by omega⟩ : Fin (n+1+1))]
        · simp only [Fin.val_mk, pairing_h_elementary, le_refl, and_self, ↓reduceIte,
            one_mul, Nat.add_sub_cancel]
          rw [ih hα]
          have he : (1 + α.sum = n + 1) ↔ α.sum = n := by omega
          simp [he]
        · intro i _ hi
          rw [pairing_h_elementary, if_neg, zero_mul]
          intro hh
          apply hi
          apply Fin.ext
          exact hh.1.symm
        · simp
    · have hbad : ¬ (∀ a ∈ m :: α, a = 1) := fun hh => hm1 (hh m (by simp))
      rw [if_neg (fun hh => hbad hh.2)]
      apply Finset.sum_eq_zero
      intro i _
      rw [pairing_h_elementary, if_neg, zero_mul]
      rintro ⟨he, hi⟩
      omega

/-- EK Proposition 2.5(2), all weights and the empty composition included. -/
theorem quotientPairing_hWord_e (α : List ℕ) (hp : ∀ a ∈ α, 0 < a) (n : ℕ) :
    quotientPairing (pi (hWord α)) (e n) =
      if α.sum = n ∧ (∀ a ∈ α, a = 1) then 1 else 0 :=
  pairing_hWord_elementary α hp n

/-- Literal weight-n version of (2.8); the previous theorem also fixes off-weight tests. -/
theorem quotientPairing_composition_e (n : ℕ) (α : List ℕ)
    (hp : ∀ a ∈ α, 0 < a) (hs : α.sum = n) :
    quotientPairing (pi (hWord α)) (e n) = if (∀ a ∈ α, a = 1) then 1 else 0 := by
  rw [quotientPairing_hWord_e α hp n]
  simp only [hs, true_and]

/-- Positive complete words of ALL weights separate arbitrary quotient elements.
This uses actual word spanning and nondegeneracy, not a perfect-form premise. -/
theorem quotient_ext_hWords (x y : Q)
    (hh : ∀ m : ℕ, ∀ α : List ℕ, (∀ a ∈ α, 0 < a) → α.sum = m →
      quotientPairing (pi (hWord α)) x = quotientPairing (pi (hWord α)) y) : x = y := by
  apply sub_eq_zero.mp
  apply quotientPairing_nondegenerate_right
  intro a
  obtain ⟨a, rfl⟩ := pi_surjective a
  change quotientPairing (piAlg a) (x-y) = 0
  induction a using EKPairingAdjoint.basis_induction wordBasis with
  | hz => simp
  | ha a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | hb w r =>
    simp only [map_smul, LinearMap.smul_apply]
    have hp : ∀ a ∈ List.ofFn (parts w), 0 < a := by
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact Nat.succ_pos _
    have he := hh _ (List.ofFn (parts w)) hp rfl
    change quotientPairing (pi (vWord (parts w))) x =
      quotientPairing (pi (vWord (parts w))) y at he
    rw [vWord_parts] at he
    simp only [piAlg_apply, map_sub, he, sub_self, smul_zero]

/-- Uniqueness of e_n in Q from all weights, without a hidden homogeneous hypothesis. -/
theorem e_unique (n : ℕ) (x : Q)
    (hx : ∀ m : ℕ, ∀ α : List ℕ, (∀ a ∈ α, 0 < a) → α.sum = m →
      quotientPairing (pi (hWord α)) x =
        if m = n ∧ (∀ a ∈ α, a = 1) then 1 else 0) : x = e n := by
  apply quotient_ext_hWords
  intro m α hp hs
  rw [hx m α hp hs, quotientPairing_hWord_e α hp n, hs]

private theorem quotient_pairing_product_e (m n : ℕ) (x : Q) :
    quotientPairing (h m * x) (e n) = ∑ i : Fin (n+1),
      (if m = i.val ∧ i.val ≤ 1 then (1 : ℤ) else 0) *
      quotientPairing x (e (n-i)) := by
  obtain ⟨x, rfl⟩ := pi_surjective x
  change quotientPairing (pi (CompleteElementary.h m) * pi x) (pi (elementary n)) = _
  rw [← pi.map_mul, quotientPairing_pi, ← adjointness, coproduct_elementary]
  simp only [map_sum, tensorPairing_tmul, pairing_h_elementary, e, quotientPairing_pi]

/-- General consumer: stripping a positive complete generator from any quotient
factor. The factor need not be homogeneous or a single complete word. -/
theorem quotientPairing_strip (m n : ℕ) (hm : 0 < m) (x : Q) :
    quotientPairing (h m * x) (e (n+1)) =
      if m = 1 then quotientPairing x (e n) else 0 := by
  rw [quotient_pairing_product_e]
  by_cases he : m = 1
  · subst m
    rw [if_pos rfl, Finset.sum_eq_single (⟨1, by omega⟩ : Fin (n+1+1))]
    · simp
    · intro i _ hi
      rw [if_neg, zero_mul]
      intro hh
      exact hi (Fin.ext hh.1.symm)
    · simp
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg, zero_mul]
    rintro ⟨hh, hi⟩
    omega

end OddMath.Frontier.EKElementaryQuotient
