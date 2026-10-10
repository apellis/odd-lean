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

* `UDot.rho`: `ρ`, as an algebra homomorphism `U̇ →ₐ[k] U̇ᵐᵒᵖ`; `UDot.star`, `UDot.shriek`: `∗`, `!`.

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
      add_sub_cancel_right]
    simp only [ite_true, eq_self]
  | one_F i μ => rw [rhoU_mul, rhoU_F, rhoU_one, smul_mul_assoc, E_mul_one_self]
  | F_one i μ =>
    rw [rhoU_mul, rhoU_F, rhoU_one, mul_smul_comm, one_mul_E, sub_add_cancel]
    simp only [ite_true, eq_self]
  | comm i j μ =>
    obtain ⟨μ', hμ'⟩ : ∃ μ', μ' = μ + D.α i - D.α j := ⟨_, rfl⟩
    have w1 : μ - D.α j = μ' - D.α i := by rw [hμ']; abel
    have w2 : μ - D.α j + D.α i = μ' := by rw [hμ']; abel
    have w3 : μ + D.α i = μ' + D.α j := by rw [hμ']; abel
    rw [rhoU_sub, rhoU_mul, rhoU_smul, rhoU_mul, rhoU_E, rhoU_F, rhoU_E, rhoU_F, h_sub_α, h_add_α,
      w2, ← hμ', w3, w1, smul_mul_smul_comm, smul_mul_smul_comm, qp_mul, qp_mul]
    have hK : -(D.d i * (D.h i μ + 1)) + D.d j * (D.h j μ + D.a j i - 1) =
        D.d j * (D.h j μ - 1) + -(D.d i * (D.h i μ - D.a i j + 1)) := by
      linear_combination -D.d_mul_symm i j
    rw [hK]
    rw [smul_comm (π ^ (D.parity i * D.parity j).val) (qp q _)]
    rw [← smul_sub (qp q (D.d j * (D.h j μ - 1) + -(D.d i * (D.h i μ - D.a i j + 1))))
      (E D q π j (μ' - D.α i) * F D q π i μ')
      (π ^ (D.parity i * D.parity j).val • (F D q π i (μ' + D.α j) * E D q π j μ'))]
    rw [mul_comm (D.parity i), comm_rel]
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
      simp only [fw, e1, e2]
      dsimp only [ν]
      rw [hm]
      rw [rhoU_smul, rhoU_mul, rhoU_mul, rhoU_epow, rhoU_E, rhoU_epow, w1, w2, w3, map_mul, map_mul,
        smul_mul_smul_comm, smul_mul_smul_comm, qp_mul, qp_mul, smul_smul, ← mul_assoc]
      rw [mul_comm (D.serreCoeff q π i j r)]
      congr 3
      dsimp only [K]
      rw [hm]
      rw [h_add_nsmul, h_add_α, h_add_nsmul, D.isGCM.diag]
      push_cast
      linear_combination (r : ℤ) * D.d_mul_symm i j
    rw [sum_congr rfl key]
    have hreflect := sum_range_reflect (fun s ↦ (qp q K * D.serreCoeff q π i j (N - s)) •
      mk D q π (fw s)) (N + 1)
    simp only [Nat.add_sub_cancel] at hreflect
    rw [hreflect]
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
      simp only [ew, e1, e2]
      dsimp only [ν]
      rw [hm]
      rw [rhoU_smul, rhoU_mul, rhoU_mul, rhoU_fpow, rhoU_F, rhoU_fpow, w1, w2, w3, map_mul, map_mul,
        smul_mul_smul_comm, smul_mul_smul_comm, qp_mul, qp_mul, smul_smul, ← mul_assoc]
      rw [mul_comm (D.serreCoeff q π i j r)]
      congr 3
      dsimp only [K]
      rw [hm]
      rw [h_sub_nsmul, h_sub_α, h_sub_nsmul, D.isGCM.diag]
      push_cast
      linear_combination (r : ℤ) * D.d_mul_symm i j
    rw [sum_congr rfl key]
    have hreflect := sum_range_reflect (fun s ↦ (qp q K * D.serreCoeff q π i j (N - s)) •
      mk D q π (ew s)) (N + 1)
    simp only [Nat.add_sub_cancel] at hreflect
    rw [hreflect]
    have key2 : ∀ s ∈ range (N + 1), (qp q K * D.serreCoeff q π i j (N - s)) • mk D q π (ew s) =
        (qp q K * ((-1) ^ N * D.pii π i ^ (N * (D.parity j).val + N.choose 2))) •
          mk D q π (D.serreCoeff q π i j s • ew s) := by
      intro s hs
      rw [D.serreCoeff_reflect q π hπ h (Nat.lt_succ_iff.1 (mem_range.1 hs)), map_smul, smul_smul,
        ← mul_assoc]
    rw [sum_congr rfl key2, ← smul_sum, ← map_sum]
    have : ∑ s ∈ range (N + 1), D.serreCoeff q π i j s • ew s = serreE D q π i j ν := rfl
    rw [this, serreE_rel D q π h, smul_zero]

variable (D q π)

/-- The linear antiautomorphism (9.8), with codomain the opposite algebra. -/
def rho (hπ : π ^ 2 = 1) : CoveringUDot k D q π →ₐ[k] (CoveringUDot k D q π)ᵐᵒᵖ :=
  RingQuot.liftAlgHom k ⟨rhoFree D q π, fun _ _ h ↦
    MulOpposite.unop_injective (rhoU_rel hπ h)⟩

variable {D q π}

@[simp] theorem rho_mk (hπ : π ^ 2 = 1) (x : Free k I X) :
    (rho D q π hπ (mk D q π x)).unop = rhoU D q π x := by
  simp only [rho, mk, RingQuot.liftAlgHom_mkAlgHom_apply, rhoU]

@[simp] theorem rho_one (hπ : π ^ 2 = 1) (μ : X) :
    (rho D q π hπ (one D q π μ)).unop = one D q π μ := by
  rw [one, rho_mk, rhoU_one]; rfl

@[simp] theorem rho_E (hπ : π ^ 2 = 1) (i : I) (μ : X) :
    (rho D q π hπ (E D q π i μ)).unop =
      qp q (-(D.d i * (D.h i μ + 1))) • F D q π i (μ + D.α i) := by
  rw [E, rho_mk, rhoU_E]

@[simp] theorem rho_F (hπ : π ^ 2 = 1) (i : I) (μ : X) :
    (rho D q π hπ (F D q π i μ)).unop =
      qp q (D.d i * (D.h i μ - 1)) • E D q π i (μ - D.α i) := by
  rw [F, rho_mk, rhoU_F]

theorem rho_smul (hπ : π ^ 2 = 1) (c : k) (x : CoveringUDot k D q π) :
    (rho D q π hπ (c • x)).unop = c • (rho D q π hπ x).unop := by simp

theorem rho_mul (hπ : π ^ 2 = 1) (x y : CoveringUDot k D q π) :
    (rho D q π hπ (x * y)).unop = (rho D q π hπ y).unop * (rho D q π hπ x).unop := by simp

/-- The antiautomorphism `ρ` is involutive. -/
theorem rho_rho (hπ : π ^ 2 = 1) (x : CoveringUDot k D q π) :
    (rho D q π hπ (rho D q π hπ x).unop).unop = x := by
  obtain ⟨y, rfl⟩ := mk_surjective D q π x
  induction y using FreeAlgebra.induction with
  | grade0 c => simp only [AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
  | grade1 g =>
    cases g with
    | one μ => rw [← Free.one, ← one, rho_one, rho_one]
    | e i μ =>
      rw [← Free.E, ← E, rho_E, rho_smul, rho_F, add_sub_cancel_right, smul_smul,
        qp_mul, h_add_α, D.isGCM.diag, qp_eq_one, one_smul]
      ring
    | f i μ =>
      rw [← Free.F, ← F, rho_F, rho_smul, rho_E, sub_add_cancel, smul_smul,
        qp_mul, h_sub_α, D.isGCM.diag, qp_eq_one, one_smul]
      ring
  | add a b ha hb => simpa only [map_add, MulOpposite.unop_add] using congrArg₂ (· + ·) ha hb
  | mul a b ha hb => rw [map_mul, rho_mul, rho_mul, ha, hb]

variable {σ : k →+* k}

theorem BarData.map_qp (hσ : BarData q π σ) (z : ℤ) : σ (qp q z) = qp q (-z) := by
  have hq : Units.map σ.toMonoidHom q = q⁻¹ := Units.ext hσ.map_q
  change (↑(Units.map σ.toMonoidHom (q ^ z)) : k) = (↑(q ^ (-z)) : k)
  rw [map_zpow, hq, inv_zpow, zpow_neg]

variable (D q π σ)

/-- The antilinear antiautomorphism `∗ = ρ ∘ ψ` of (9.9). -/
def star (hσ : BarData q π σ) : CoveringUDot k D q π →+* (CoveringUDot k D q π)ᵐᵒᵖ :=
  (rho D q π hσ.π_sq).toRingHom.comp (psi D q π σ hσ)

/-- The antilinear antiautomorphism `! = ψ ∘ ρ` of (9.10). -/
def shriek (hσ : BarData q π σ) : CoveringUDot k D q π →+* (CoveringUDot k D q π)ᵐᵒᵖ :=
  (psi D q π σ hσ).op.comp (rho D q π hσ.π_sq).toRingHom

variable {D q π σ}

theorem star_apply (hσ : BarData q π σ) (x : CoveringUDot k D q π) :
    (star D q π σ hσ x).unop = (rho D q π hσ.π_sq (psi D q π σ hσ x)).unop := rfl

theorem shriek_apply (hσ : BarData q π σ) (x : CoveringUDot k D q π) :
    (shriek D q π σ hσ x).unop = psi D q π σ hσ (rho D q π hσ.π_sq x).unop := rfl

@[simp] theorem star_one (hσ : BarData q π σ) (μ : X) :
    (star D q π σ hσ (one D q π μ)).unop = one D q π μ := by
  rw [star_apply, psi_one, rho_one]

@[simp] theorem shriek_one (hσ : BarData q π σ) (μ : X) :
    (shriek D q π σ hσ (one D q π μ)).unop = one D q π μ := by
  rw [shriek_apply, rho_one, psi_one]

@[simp] theorem star_E (hσ : BarData q π σ) (i : I) (μ : X) :
    (star D q π σ hσ (E D q π i μ)).unop =
      qp q (-(D.d i * (D.h i μ + 1))) • F D q π i (μ + D.α i) := by
  rw [star_apply, psi_E, rho_E]

@[simp] theorem star_F (hσ : BarData q π σ) (i : I) (μ : X) :
    (star D q π σ hσ (F D q π i μ)).unop =
      (qp q (D.d i * (D.h i μ - 1)) * π ^ (D.parl i μ).val) • E D q π i (μ - D.α i) := by
  rw [star_apply, psi_F, rho_smul, rho_F, smul_smul, mul_comm]

@[simp] theorem shriek_E (hσ : BarData q π σ) (i : I) (μ : X) :
    (shriek D q π σ hσ (E D q π i μ)).unop =
      (π ^ (D.parl i μ).val * qp q (D.d i * (D.h i μ + 1))) • F D q π i (μ + D.α i) := by
  rw [shriek_apply, rho_E, psi_smul, psi_F, hσ.map_qp, neg_neg, D.parl_add_α, smul_smul, mul_comm]

@[simp] theorem shriek_F (hσ : BarData q π σ) (i : I) (μ : X) :
    (shriek D q π σ hσ (F D q π i μ)).unop =
      qp q (D.d i * (1 - D.h i μ)) • E D q π i (μ - D.α i) := by
  rw [shriek_apply, rho_F, psi_smul, psi_E, hσ.map_qp]
  congr 2
  ring

theorem star_smul (hσ : BarData q π σ) (c : k) (x : CoveringUDot k D q π) :
    (star D q π σ hσ (c • x)).unop = σ c • (star D q π σ hσ x).unop := by
  rw [star_apply, psi_smul, rho_smul, star_apply]

theorem shriek_smul (hσ : BarData q π σ) (c : k) (x : CoveringUDot k D q π) :
    (shriek D q π σ hσ (c • x)).unop = σ c • (shriek D q π σ hσ x).unop := by
  rw [shriek_apply, rho_smul, psi_smul, shriek_apply]

/-- `∗` and `!` are mutually inverse when the scalar bar is involutive. -/
theorem star_shriek (hσ : BarData q π σ) (hσσ : ∀ c, σ (σ c) = c) (x : CoveringUDot k D q π) :
    (star D q π σ hσ (shriek D q π σ hσ x).unop).unop = x := by
  rw [star_apply, shriek_apply, psi_psi hσ hσσ, rho_rho]

/-- `!` and `∗` are mutually inverse when the scalar bar is involutive. -/
theorem shriek_star (hσ : BarData q π σ) (hσσ : ∀ c, σ (σ c) = c) (x : CoveringUDot k D q π) :
    (shriek D q π σ hσ (star D q π σ hσ x).unop).unop = x := by
  rw [shriek_apply, star_apply, rho_rho, psi_psi hσ hσσ]

end UDot

end OddMath.CoveringQuantum
