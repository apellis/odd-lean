/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.UDot.Symmetries

/-!
# The antiautomorphism `ρ` of `U̇_{q,π}(𝔤)`, and `∗`, `!`

Brundan–Ellis, arXiv:1701.04133v2 ([BE2]), §9, (9.8)–(9.10): the linear algebra
antiautomorphism `ρ` of `U̇_{q,π}(𝔤)` with
```
ρ(1_λ) = 1_λ,  ρ(eᵢ1_λ) = qᵢ^{-⟨hᵢ,λ⟩-1} 1_λ fᵢ,  ρ(fᵢ1_λ) = qᵢ^{⟨hᵢ,λ⟩-1} 1_λ eᵢ,
```
and `∗ = ρ ∘ ψ`, `! = ψ ∘ ρ`. Here `1_λ fᵢ = fᵢ 1_{λ+αᵢ}` and `1_λ eᵢ = eᵢ 1_{λ-αᵢ}`.

`ρ` is constructed as a `k`-algebra map into the opposite algebra. The Serre relation (9.3) is
sent to a multiple of (9.4) (and conversely): the `q`-power picked up by
`eᵢ^{N-r} eⱼ eᵢʳ 1_λ` does not depend on `r` (using `dᵢ aᵢⱼ = dⱼ aⱼᵢ`), and the Serre coefficients
satisfy `c_{N-r} = (-1)^N πᵢ^{N|j| + N(N-1)/2} c_r` (`serreCoeff_reflect`).

## Main definitions

* `UDot.rho`: `ρ`, as a ring homomorphism `U̇ →+* U̇ᵐᵒᵖ`; `UDot.star`, `UDot.shriek`: `∗`, `!`.

## Main results

* `UDot.rho_one`, `UDot.rho_E`, `UDot.rho_F`, `UDot.rho_smul`, `UDot.rho_rho`.
* `UDot.star_E`, `UDot.star_F`, `UDot.shriek_E`, `UDot.shriek_F` ((9.9), (9.10)),
  `UDot.star_shriek`, `UDot.shriek_star`.
-/

noncomputable section

namespace OddMath.CoveringQuantum

open Finset

theorem choose_two_add (r m : ℕ) : (r + m).choose 2 = r.choose 2 + m.choose 2 + r * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ',
      Nat.choose_succ_succ' m, Nat.choose_one_right, Nat.choose_one_right,
      ← show (2 : ℕ) = 1 + 1 from rfl, ih]
    ring

namespace SuperCartanDatum

variable {I k : Type*} [CommRing k] (C : SuperCartanDatum I) (q : kˣ) (π : k)

/-- `c_{N-r} = (-1)^N πᵢ^{N|j| + N(N-1)/2} c_r` for the Serre coefficients `c_r` of (10.1),
`N = dᵢⱼ + 1`, `r ≤ N`, given `π² = 1`. -/
theorem serreCoeff_reflect (hπ : π ^ 2 = 1) {i j : I} (hij : i ≠ j) {r : ℕ}
    (hr : r ≤ C.serreDeg i j) :
    C.serreCoeff q π i j (C.serreDeg i j - r) =
      (-1) ^ C.serreDeg i j *
        C.pii π i ^ (C.serreDeg i j * (C.parity j).val + (C.serreDeg i j).choose 2) *
        C.serreCoeff q π i j r := by
  have hP2 := C.pii_sq π hπ i
  have hodd := C.odd_serreDeg_or π hij
  rw [serreCoeff, serreCoeff, qpBinom_symm hr]
  obtain ⟨m, hm⟩ : ∃ m, C.serreDeg i j = r + m := ⟨_, (Nat.add_sub_cancel' hr).symm⟩
  rw [hm] at hodd ⊢
  rw [Nat.add_sub_cancel_left, choose_two_add]
  set P := C.pii π i
  set e := (C.parity j).val
  have hP : P ^ (r * m) = 1 := by
    rcases hodd with h | h
    · have h2 : Even r ∨ Even m := by
        rcases Nat.even_or_odd r with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ((Nat.odd_add.1 h).1 h1)
      obtain ⟨t, ht⟩ := Nat.even_mul.2 h2
      rw [ht, ← two_mul, pow_mul, hP2, one_pow]
    · rw [h, one_pow]
  calc (-1) ^ m * P ^ (m * e + m.choose 2) * qpBinom (C.qi q i) P (r + m) r
      = (-1) ^ m * P ^ (m * e + m.choose 2) * qpBinom (C.qi q i) P (r + m) r *
          P ^ (r * m) * ((-1) ^ r) ^ 2 * (P ^ 2) ^ (r * e + r.choose 2) := by
        have hs : ((-1 : k) ^ r) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
        rw [hP, hP2, hs, one_pow, mul_one, mul_one, mul_one]
    _ = _ := by ring

end SuperCartanDatum

namespace UDot

variable {k : Type*} [CommRing k] {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  (D : RootDatum I X) (q : kˣ) (π : k)

/-- `q^z ∈ k` for `z ∈ ℤ`. -/
def qp (z : ℤ) : k := ((q ^ z : kˣ) : k)

variable {q} in
theorem qp_mul (a b : ℤ) : qp q a * qp q b = qp q (a + b) := by
  simp only [qp, zpow_add, Units.val_mul]

variable {q} in
@[simp] theorem qp_zero : qp q 0 = 1 := by simp [qp]

omit [DecidableEq I] [DecidableEq X] in
variable {D} in
theorem h_add_nsmul (i j : I) (μ : X) (n : ℕ) : D.h i (μ + n • D.α j) = D.h i μ + n * D.a i j := by
  have := D.h_α i j
  simp only [RootDatum.h] at this ⊢
  rw [map_add, map_nsmul, this, nsmul_eq_mul]

omit [DecidableEq I] [DecidableEq X] in
variable {D} in
theorem h_sub_nsmul (i j : I) (μ : X) (n : ℕ) : D.h i (μ - n • D.α j) = D.h i μ - n * D.a i j := by
  have := D.h_α i j
  simp only [RootDatum.h] at this ⊢
  rw [map_sub, map_nsmul, this, nsmul_eq_mul]

omit [DecidableEq I] [DecidableEq X] in
variable {D} in
theorem h_add_α (i j : I) (μ : X) : D.h i (μ + D.α j) = D.h i μ + D.a i j := by
  simpa using h_add_nsmul i j μ 1

omit [DecidableEq I] [DecidableEq X] in
variable {D} in
theorem h_sub_α (i j : I) (μ : X) : D.h i (μ - D.α j) = D.h i μ - D.a i j := by
  simpa using h_sub_nsmul i j μ 1

theorem mk_fpow_succ' (i : I) (n : ℕ) (ν : X) :
    mk D q π (fpow D i (n + 1) ν) = mk D q π (fpow D i n (ν - D.α i)) * F D q π i ν := by
  induction n generalizing ν with
  | zero =>
    simp only [fpow, zero_smul, sub_zero, map_mul]
    exact (F_mul_one_self D q π i ν).trans (one_mul_F_self D q π i ν).symm
  | succ n ih =>
    rw [fpow, map_mul, ih, fpow, map_mul, ← mul_assoc, succ_nsmul', sub_sub]

theorem mk_epow_succ' (i : I) (n : ℕ) (μ : X) :
    mk D q π (epow D i (n + 1) μ) = mk D q π (epow D i n (μ + D.α i)) * E D q π i μ := by
  induction n generalizing μ with
  | zero =>
    simp only [epow, zero_smul, add_zero, map_mul]
    exact (E_mul_one_self D q π i μ).trans (one_mul_E_self D q π i μ).symm
  | succ n ih =>
    rw [epow, map_mul, ih, epow, map_mul, ← mul_assoc, succ_nsmul, add_assoc, add_comm (D.α i)]

/-- `ρ` on generators. -/
def rhoGen : Gen I X → CoveringUDot k D q π
  | .one μ => one D q π μ
  | .e i μ => qp q (-(D.d i * (D.h i μ + 1))) • F D q π i (μ + D.α i)
  | .f i μ => qp q (D.d i * (D.h i μ - 1)) • E D q π i (μ - D.α i)

/-- `ρ` on the free algebra, into the opposite algebra. -/
def rhoFree : Free k I X →ₐ[k] (CoveringUDot k D q π)ᵐᵒᵖ :=
  FreeAlgebra.lift k fun g ↦ MulOpposite.op (rhoGen D q π g)

/-- `ρ` on the free algebra, as a function to `U̇`. -/
def rhoU (x : Free k I X) : CoveringUDot k D q π := (rhoFree D q π x).unop

variable {D q π}

theorem rhoU_mul (x y : Free k I X) : rhoU D q π (x * y) = rhoU D q π y * rhoU D q π x := by
  simp [rhoU]

theorem rhoU_add (x y : Free k I X) : rhoU D q π (x + y) = rhoU D q π x + rhoU D q π y := by
  simp [rhoU]

theorem rhoU_sub (x y : Free k I X) : rhoU D q π (x - y) = rhoU D q π x - rhoU D q π y := by
  simp [rhoU]

theorem rhoU_smul (c : k) (x : Free k I X) : rhoU D q π (c • x) = c • rhoU D q π x := by
  simp [rhoU]

@[simp] theorem rhoU_zero : rhoU D q π (0 : Free k I X) = 0 := by simp [rhoU]

theorem rhoU_sum {ι : Type*} (s : Finset ι) (f : ι → Free k I X) :
    rhoU D q π (∑ x ∈ s, f x) = ∑ x ∈ s, rhoU D q π (f x) := by
  simp only [rhoU, map_sum]
  exact map_sum (MulOpposite.opAddEquiv : CoveringUDot k D q π ≃+ _).symm _ _

@[simp] theorem rhoU_one (μ : X) : rhoU D q π (Free.one k μ) = one D q π μ := by
  simp [rhoU, rhoFree, Free.one, rhoGen]

@[simp] theorem rhoU_E (i : I) (μ : X) :
    rhoU D q π (Free.E k i μ) = qp q (-(D.d i * (D.h i μ + 1))) • F D q π i (μ + D.α i) := by
  simp [rhoU, rhoFree, Free.E, rhoGen]

@[simp] theorem rhoU_F (i : I) (μ : X) :
    rhoU D q π (Free.F k i μ) = qp q (D.d i * (D.h i μ - 1)) • E D q π i (μ - D.α i) := by
  simp [rhoU, rhoFree, Free.F, rhoGen]

theorem rhoU_epow (i : I) (n : ℕ) (μ : X) :
    rhoU D q π (epow D i n μ) =
      qp q (-(D.d i * (n * D.h i μ + n ^ 2))) • mk D q π (fpow D i n (μ + n • D.α i)) := by
  induction n with
  | zero => simp [epow, fpow, one]
  | succ n ih =>
    rw [epow, rhoU_mul, ih, rhoU_E, mk_fpow_succ', smul_mul_smul_comm, qp_mul, succ_nsmul,
      ← add_assoc, add_sub_cancel_right, h_add_nsmul, D.isGCM.diag]
    congr 1
    push_cast; ring_nf

theorem rhoU_fpow (i : I) (n : ℕ) (μ : X) :
    rhoU D q π (fpow D i n μ) =
      qp q (D.d i * (n * D.h i μ - n ^ 2)) • mk D q π (epow D i n (μ - n • D.α i)) := by
  induction n with
  | zero => simp [epow, fpow, one]
  | succ n ih =>
    rw [fpow, rhoU_mul, ih, rhoU_F, mk_epow_succ', smul_mul_smul_comm, qp_mul, succ_nsmul,
      ← sub_sub, sub_add_cancel, h_sub_nsmul, D.isGCM.diag]
    congr 1
    push_cast; ring_nf

theorem qp_eq_one {z : ℤ} (hz : z = 0) : qp q z = 1 := by rw [hz, qp_zero]

omit [DecidableEq I] [DecidableEq X] in
theorem weight_aux (μ : X) (a b : X) (r m : ℕ) :
    μ + (r + m) • a + b - m • a - b = μ + r • a ∧ μ + (r + m) • a + b - m • a = μ + r • a + b ∧
      μ + r • a + b + m • a = μ + (r + m) • a + b := by
  refine ⟨?_, ?_, ?_⟩ <;> (rw [add_nsmul]; abel)

omit [DecidableEq I] [DecidableEq X] in
theorem weight_aux' (μ : X) (a b : X) (r m : ℕ) :
    μ - (r + m) • a - b + m • a + b = μ - r • a ∧ μ - (r + m) • a - b + m • a = μ - r • a - b ∧
      μ - r • a - b - m • a = μ - (r + m) • a - b := by
  refine ⟨?_, ?_, ?_⟩ <;> (rw [add_nsmul]; abel)

theorem rhoU_rel {x y : Free k I X} (hπ : π ^ 2 = 1) (h : Rel D q π x y) :
    rhoU D q π x = rhoU D q π y := by
  cases h with
  | one_one μ ν =>
    rw [rhoU_mul, rhoU_one, rhoU_one, one_mul_one]
    split_ifs with h₁ h₂ h₂
    · rw [rhoU_one, h₁]
    · exact absurd h₁.symm h₂
    · exact absurd h₂.symm h₁
    · rw [rhoU_zero]
  | one_E i μ => rw [rhoU_mul, rhoU_E, rhoU_one, smul_mul_assoc, F_mul_one_self]
  | E_one i μ =>
    rw [rhoU_mul, rhoU_E, rhoU_one, mul_smul_comm, one_mul_F,
      if_pos (add_sub_cancel_right μ (D.α i)).symm]
  | one_F i μ => rw [rhoU_mul, rhoU_F, rhoU_one, smul_mul_assoc, E_mul_one_self]
  | F_one i μ =>
    rw [rhoU_mul, rhoU_F, rhoU_one, mul_smul_comm, one_mul_E, if_pos (sub_add_cancel μ (D.α i)).symm]
  | comm i j μ =>
    obtain ⟨μ', hμ'⟩ : ∃ μ', μ' = μ + D.α i - D.α j := ⟨_, rfl⟩
    have w1 : μ - D.α j = μ' - D.α i := by rw [hμ']; abel
    have w2 : μ - D.α j + D.α i = μ' := by rw [hμ']; abel
    have w3 : μ + D.α i = μ' + D.α j := by rw [hμ']; abel
    rw [rhoU_sub, rhoU_mul, rhoU_smul, rhoU_mul, rhoU_E, rhoU_F, rhoU_E, rhoU_F, h_sub_α, h_add_α,
      w2, ← hμ', w3, w1, smul_mul_smul_comm, smul_mul_smul_comm, qp_mul, qp_mul]
    have hK : -(D.d i * (D.h i μ + 1)) + D.d j * (D.h j μ + D.a j i - 1) =
        D.d j * (D.h j μ - 1) + -(D.d i * (D.h i μ - D.a i j + 1)) := by
      linear_combination D.d_mul_symm i j
    rw [hK, smul_comm (π ^ _) (qp q _), ← smul_sub, mul_comm (D.parity i), comm_rel]
    split_ifs with h₁ h₂ h₂
    · subst h₁
      rw [hμ', add_sub_cancel_right, rhoU_smul, rhoU_one, qp_eq_one, one_smul]
      rw [D.isGCM.diag]; ring
    · exact absurd h₁.symm h₂
    · exact absurd h₂.symm h₁
    · rw [smul_zero, rhoU_zero]
  | serreE i j μ h =>
    rw [rhoU_zero, serreE, rhoU_sum]
    set N := D.serreDeg i j with hN
    set ν := μ + N • D.α i + D.α j
    set K : ℤ := -(D.d i * (N * D.h i μ + N ^ 2 + N * D.a i j)) - D.d j * (D.h j μ + 1)
    set fw : ℕ → Free k I X := fun s ↦
      fpow D i (N - s) (ν - s • D.α i - D.α j) * Free.F k j (ν - s • D.α i) * fpow D i s ν
    have key : ∀ r ∈ range (N + 1), rhoU D q π (D.serreCoeff q π i j r •
        (epow D i (N - r) (μ + r • D.α i + D.α j) * Free.E k j (μ + r • D.α i) * epow D i r μ)) =
        (qp q K * D.serreCoeff q π i j (N - (N - r))) • mk D q π (fw (N - r)) := by
      intro r hr
      obtain ⟨m, hm⟩ : ∃ m, N = r + m := ⟨N - r, by have := mem_range.1 hr; omega⟩
      have e1 : N - r = m := by omega
      have e2 : N - m = r := by omega
      obtain ⟨w1, w2, w3⟩ := weight_aux μ (D.α i) (D.α j) r m
      simp only [fw, ν, e1, e2, hm] at *
      rw [rhoU_smul, rhoU_mul, rhoU_mul, rhoU_epow, rhoU_E, rhoU_epow, w1, w2, w3, map_mul, map_mul,
        smul_mul_smul_comm, smul_mul_smul_comm, qp_mul, qp_mul, smul_smul, ← mul_assoc]
      congr 3
      rw [h_add_nsmul, h_add_α, h_add_nsmul, D.isGCM.diag]
      push_cast
      linear_combination (-(r : ℤ)) * D.d_mul_symm i j
    rw [sum_congr rfl key]
    have refl := sum_range_reflect (fun s ↦ (qp q K * D.serreCoeff q π i j (N - s)) •
      mk D q π (fw s)) (N + 1)
    simp only [Nat.add_sub_cancel] at refl
    rw [refl]
    have key2 : ∀ s ∈ range (N + 1), (qp q K * D.serreCoeff q π i j (N - s)) • mk D q π (fw s) =
        (qp q K * ((-1) ^ N * D.pii π i ^ (N * (D.parity j).val + N.choose 2))) •
          mk D q π (D.serreCoeff q π i j s • fw s) := by
      intro s hs
      rw [D.serreCoeff_reflect q π hπ h (Nat.lt_succ_iff.1 (mem_range.1 hs)), map_smul, smul_smul,
        ← mul_assoc]
    rw [sum_congr rfl key2, ← smul_sum, ← map_sum]
    have : ∑ s ∈ range (N + 1), D.serreCoeff q π i j s • fw s = serreF D q π i j ν := rfl
    rw [this, serreF_rel D q π h, smul_zero]
  | serreF i j μ h =>
    rw [rhoU_zero, serreF, rhoU_sum]
    set N := D.serreDeg i j with hN
    set ν := μ - N • D.α i - D.α j
    set K : ℤ := D.d i * (N * D.h i μ - N ^ 2 - N * D.a i j) + D.d j * (D.h j μ - 1)
    set ew : ℕ → Free k I X := fun s ↦
      epow D i (N - s) (ν + s • D.α i + D.α j) * Free.E k j (ν + s • D.α i) * epow D i s ν
    have key : ∀ r ∈ range (N + 1), rhoU D q π (D.serreCoeff q π i j r •
        (fpow D i (N - r) (μ - r • D.α i - D.α j) * Free.F k j (μ - r • D.α i) * fpow D i r μ)) =
        (qp q K * D.serreCoeff q π i j (N - (N - r))) • mk D q π (ew (N - r)) := by
      intro r hr
      obtain ⟨m, hm⟩ : ∃ m, N = r + m := ⟨N - r, by have := mem_range.1 hr; omega⟩
      have e1 : N - r = m := by omega
      have e2 : N - m = r := by omega
      obtain ⟨w1, w2, w3⟩ := weight_aux' μ (D.α i) (D.α j) r m
      simp only [ew, ν, e1, e2, hm] at *
      rw [rhoU_smul, rhoU_mul, rhoU_mul, rhoU_fpow, rhoU_F, rhoU_fpow, w1, w2, w3, map_mul, map_mul,
        smul_mul_smul_comm, smul_mul_smul_comm, qp_mul, qp_mul, smul_smul, ← mul_assoc]
      congr 3
      rw [h_sub_nsmul, h_sub_α, h_sub_nsmul, D.isGCM.diag]
      push_cast
      linear_combination (r : ℤ) * D.d_mul_symm i j
    rw [sum_congr rfl key]
    have refl := sum_range_reflect (fun s ↦ (qp q K * D.serreCoeff q π i j (N - s)) •
      mk D q π (ew s)) (N + 1)
    simp only [Nat.add_sub_cancel] at refl
    rw [refl]
    have key2 : ∀ s ∈ range (N + 1), (qp q K * D.serreCoeff q π i j (N - s)) • mk D q π (ew s) =
        (qp q K * ((-1) ^ N * D.pii π i ^ (N * (D.parity j).val + N.choose 2))) •
          mk D q π (D.serreCoeff q π i j s • ew s) := by
      intro s hs
      rw [D.serreCoeff_reflect q π hπ h (Nat.lt_succ_iff.1 (mem_range.1 hs)), map_smul, smul_smul,
        ← mul_assoc]
    rw [sum_congr rfl key2, ← smul_sum, ← map_sum]
    have : ∑ s ∈ range (N + 1), D.serreCoeff q π i j s • ew s = serreE D q π i j ν := rfl
    rw [this, serreE_rel D q π h, smul_zero]

end UDot

end OddMath.CoveringQuantum
