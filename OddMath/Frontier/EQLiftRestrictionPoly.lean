import OddMath.Frontier.EQLiftAll
import OddMath.Frontier.EQRestrictionFunctor

/-!
# Polynomial identities for `P^A` in all ranks

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, (4.32) and the proof of Corollary 4.21, for all ranks `A`, `B`.

With `P = y_1 ⋯ y_B` and `P^A ∈ OPol_{A+B}` (`PAG`):

* `PAG_mul`: `P^A f = χ(f) P^A`, `χ` the sign twist `x_i ↦ ((-1)^B)^A x_i`, `y_j ↦ ((-1)^{B-1})^A y_j`
  (`chiG`);
* `dAlpha_PAG`: `d(P^A 1_z) = s_β P^A 1_z` in `Z_{A+B}`, `β = (0,1,0,…) ⊔ (0,1,0,…)`;
* `tau_blockRev_swapG`: `(θ_A ⊗ θ_B) ∘ (w₀ × w₀) ∘ swap = ι^{AB} ∘ χ ∘ (θ ∘ w₀)`.

These are the identities of `EQRestrictionFunctor` (ranks `a + 2`, `b + 2`) in every rank.
-/

noncomputable section

namespace OddMath.Frontier.EQLift

open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.EQSkewDifferential
open OddMath.Frontier.EQZab (inclX inclY osymAB par)
open OddMath.Frontier.EQFunctor
open DG

variable (A B : ℕ)

/-- `P^A = (y_1 ⋯ y_B)^A ∈ OPol_{A+B}`. -/
abbrev PAG : SkewPolynomial (A + B) := topY A B ^ A

/-- The signs of `P^A f = χ(f) P^A`. -/
def chiCoeffG (i : Fin (A + B)) : ℤ :=
  if i.val < A then ((-1 : ℤ) ^ B) ^ A else ((-1 : ℤ) ^ (B - 1)) ^ A

/-- `χ`. -/
def chiG : SkewPolynomial (A + B) →+* SkewPolynomial (A + B) := EQZab.diagHom _ (chiCoeffG A B)

variable {A B}

theorem chiCoeffG_sq (i : Fin (A + B)) : chiCoeffG A B i * chiCoeffG A B i = 1 := by
  unfold chiCoeffG
  split_ifs <;> rw [← mul_pow, ← mul_pow] <;> simp

theorem generator_mul_PAG (i : Fin (A + B)) :
    generator i * PAG A B = chiCoeffG A B i • (PAG A B * generator i) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have h := mul_topY_pow (inclX_generator_mul_topY (A := A) (B := B) i) A
    rw [EQZab.inclX_generator] at h
    rw [h, chiCoeffG]
    simp
  · have h := mul_topY_pow (inclY_generator_mul_topY (A := A) (B := B) j) A
    rw [EQZab.inclY_generator] at h
    rw [h, chiCoeffG]
    simp

theorem PAG_mul_generator (i : Fin (A + B)) :
    PAG A B * generator i = chiCoeffG A B i • (generator i * PAG A B) := by
  rw [generator_mul_PAG, smul_smul, chiCoeffG_sq, one_smul]

/-- `P^A f = χ(f) P^A`. -/
theorem PAG_mul (f : SkewPolynomial (A + B)) : PAG A B * f = chiG A B f * PAG A B := by
  induction f using induction_generator with
  | hgen i => rw [PAG_mul_generator, chiG, EQZab.diagHom_generator, smul_mul_assoc]
  | h0 => rw [map_zero, EQBorel.sp_mul_zero, EQBorel.sp_zero_mul]
  | h1 => rw [map_one, sp_mul_one', sp_one_mul']
  | hadd f g hf hg => rw [mul_add, hf, hg, map_add, add_mul]
  | hneg f hf => rw [mul_neg, hf, map_neg, neg_mul]
  | hmul f g hf hg => rw [← EQBorel.sp_mul_assoc, hf, EQBorel.sp_mul_assoc, hg, ← EQBorel.sp_mul_assoc, map_mul]

theorem chiG_chiG (f : SkewPolynomial (A + B)) : chiG A B (chiG A B f) = f := by
  have h : (chiG A B).comp (chiG A B) = RingHom.id _ := ringHom_ext fun j => by
    rw [RingHom.comp_apply, chiG, EQZab.diagHom_generator, map_zsmul, EQZab.diagHom_generator, smul_smul,
      chiCoeffG_sq, one_smul, RingHom.id_apply]
  exact RingHom.congr_fun h f

theorem chiG_mem_grading {k : ℤ} {f : SkewPolynomial (A + B)} (hf : f ∈ grading _ k) :
    chiG A B f ∈ grading _ k :=
  ringHom_mem_grading _ (fun j => by
    rw [chiG, EQZab.diagHom_generator]; exact AddSubgroup.zsmul_mem _ (generator_mem_grading _) _) hf

theorem mul_PAG_eq (f : SkewPolynomial (A + B)) : f * PAG A B = PAG A B * chiG A B f := by
  rw [PAG_mul, chiG_chiG]

theorem neg_one_pow_mod_two (n : ℕ) : (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul]
  norm_num

/-- `d_α(P^A) = s_β P^A`. -/
theorem dAlpha_PAG : dAlpha (zAlpha (A + B)) (PAG A B) = sAlpha (zAB A B) * PAG A B := by
  rw [dAlpha_apply, d_topY_pow, parityInv_of_mem (topY_pow_mem_grading _), smul_mul_assoc, PAG_mul,
    ← smul_mul_assoc, ← smul_mul_assoc, ← add_mul]
  congr 1
  rw [chiG, diagHom_sAlpha, e1Y_eq_sAlpha, zsmul_sAlpha, zsmul_sAlpha, sAlpha_add']
  refine sAlpha_ext fun i => ?_
  simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, chiCoeffG, zAlpha, zAB, par]
  rw [koszulSign_eq_neg_one_pow_natAbs, show (B : ℤ) * (A : ℤ) = ((B * A : ℕ) : ℤ) by push_cast; ring,
    Int.natAbs_natCast]
  by_cases hi : i.val < A
  · simp only [show ¬ (A ≤ i.val) by omega, hi, ↓reduceIte]
    ring_nf
    rw [mul_comm (B * A) 2, pow_mul]
    norm_num
  · simp only [show A ≤ i.val by omega, hi, ↓reduceIte]
    have hB : 1 ≤ B := by have := i.isLt; omega
    obtain ⟨m, hm⟩ : ∃ m, i.val = A + m := ⟨i.val - A, by omega⟩
    rw [hm, show A + m - A = m by omega, neg_one_pow_mod_two (B * A), ← pow_mul,
      neg_one_pow_mod_two ((B - 1) * A)]
    rcases Nat.mod_two_eq_zero_or_one A with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one B with hb | hb <;>
      rcases Nat.mod_two_eq_zero_or_one m with hm2 | hm2 <;>
      · have e1 : (B * A) % 2 = (B % 2) * (A % 2) % 2 := Nat.mul_mod _ _ _
        have e2 : ((B - 1) * A) % 2 = ((B - 1) % 2) * (A % 2) % 2 := Nat.mul_mod _ _ _
        have e3 : (B - 1) % 2 = (B % 2 + 1) % 2 := by omega
        have e4 : (A + m) % 2 = (A % 2 + m % 2) % 2 := Nat.add_mod _ _ _
        simp only [e1, e2, e3, e4, ha, hb, hm2]
        norm_num

theorem dAlpha_mul_PAG (g : SkewPolynomial (A + B)) :
    dAlpha (zAlpha (A + B)) (g * PAG A B) = dAlpha (zAB A B) g * PAG A B := by
  rw [dAlpha_mul, dAlpha_PAG, dAlpha_apply, add_mul, EQBorel.sp_mul_assoc]

/-- `(θ_A ⊗ θ_B) ∘ (w₀ × w₀) ∘ swap = ι^{AB} ∘ χ ∘ (θ ∘ w₀)` on `OPol_{A+B}`. -/
theorem tau_blockRev_swapG :
    (EQZab.tauAB A B).comp ((blockRev A B).comp (swapPoly A B)) =
      (parityInv (A + B) ^ (A * B)).comp ((chiG A B).comp (twistRev (A + B))) := by
  refine ringHom_ext fun j => ?_
  simp only [RingHom.comp_apply, swapPoly_generator, blockRev_generator, tauAB_generator, twistRev_generator,
    map_zsmul, chiG, EQZab.diagHom_generator, smul_smul, pow_parityInv_generator]
  have hperm : blockRevPerm A B (swapFin A B j) = j.rev := by
    apply Fin.ext
    unfold swapFin
    split_ifs with h
    · have := blockRevPerm_natAdd A B ⟨j.val, h⟩
      rw [show (⟨A + j.val, by omega⟩ : Fin (A + B)) = Fin.natAdd A ⟨j.val, h⟩ from rfl, this]
      simp; omega
    · have := blockRevPerm_castAdd A B ⟨j.val - B, by omega⟩
      rw [show (⟨j.val - B, by omega⟩ : Fin (A + B)) = Fin.castAdd B ⟨j.val - B, by omega⟩ from rfl, this]
      simp; omega
  rw [hperm]
  congr 1
  generalize j.rev = k
  unfold EQZab.tauCoeff chiCoeffG
  by_cases hk : k.val < A
  · simp only [show ¬ (A ≤ k.val) by omega, hk, ↓reduceIte]
    rw [mul_assoc, ← pow_mul, ← pow_add, show B * A + A * B = 2 * (A * B) by ring, pow_mul]
    norm_num
  · simp only [show A ≤ k.val by omega, hk, ↓reduceIte]
    have hB : 1 ≤ B := by have := k.isLt; omega
    obtain ⟨m, hm⟩ : ∃ m, k.val = A + m := ⟨k.val - A, by omega⟩
    rw [hm, show A + m - A = m by omega, ← pow_mul, mul_assoc, ← pow_add, ← pow_add,
      show A + m + ((B - 1) * A + A * B) = m + 2 * (A * B) by
        obtain ⟨c, rfl⟩ : ∃ c, B = c + 1 := ⟨B - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring,
      pow_add, pow_mul]
    norm_num

end OddMath.Frontier.EQLift
