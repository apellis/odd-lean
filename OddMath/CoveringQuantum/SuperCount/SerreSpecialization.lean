/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.HalfAlgebra
import LieLean.Algebra.Lie.KacMoody.Super.SerreAssociative

/-!
# The quantum Serre elements at `q = 1`, `π = -1`

At `q = 1` and `π = -1` the quantum Serre element (10.1) of [BE2] (Brundan–Ellis, *Super
Kac–Moody 2-categories*, arXiv:1701.04133v2) becomes the super Serre element
`(ad vᵢ)^{1 - aᵢⱼ} vⱼ` of the free algebra, the iterated super commutator for the parity
`|vᵢ| = |i|` (`SuperCartanDatum.serreElt_one_neg_one`). This identifies the specialization of
the covering half algebra `f` at `q = 1`, `π = -1` with the positive part of the
contragredient Lie superalgebra `G(A, τ)` of Kac (Adv. Math. 30 (1978)), as presented in
`LieLean` (`Matrix.Realization.SuperEnveloping.superSerreIdeal`).

## Main results

* `SuperCartanDatum.sLie_replicate_eq_sum`: the expansion of `(ad vᵢ)^N vⱼ`.
* `SuperCartanDatum.serreElt_one_neg_one`.
-/

namespace OddMath.CoveringQuantum

open PreF Matrix.Realization Matrix.Realization.SuperEnveloping

variable {I k : Type*} [Field k] (C : SuperCartanDatum I)

private lemma zSign_add (a b : ZMod 2) : zSign k (a + b) = zSign k a * zSign k b := by
  fin_cases a <;> fin_cases b <;> simp [zSign]

private lemma neg_one_pow_val_one : (-1 : k) ^ (1 : ZMod 2).val = -1 := by
  rw [ZMod.val_one, pow_one]

private lemma zSign_eq_pow (a : ZMod 2) : zSign k a = (-1 : k) ^ a.val := by
  fin_cases a
  · simp [zSign]
  · exact (neg_one_pow_val_one).symm

private lemma zSign_nsmul_one (N : ℕ) : zSign k (N • (1 : ZMod 2)) = (-1 : k) ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [succ_nsmul, zSign_add, ih, zSign_one, pow_succ]

namespace SuperCartanDatum

/-- The sign of the `N`-th step of `(ad vᵢ)^N vⱼ`: `zSign(|i| (N |i| + |j|)) = πᵢ^{N + |j|}` at
`π = -1`. -/
private lemma zSign_step (i j : I) (N : ℕ) :
    zSign k (C.parity i * (((List.replicate N i).map C.parity).sum + C.parity j)) =
      C.pii (-1 : k) i ^ N * C.pii (-1 : k) i ^ (C.parity j).val := by
  simp only [List.map_replicate, List.sum_replicate, pii]
  generalize C.parity i = a
  generalize C.parity j = b
  fin_cases a
  · simp
  · simp only [Fin.mk_one, one_mul]
    rw [zSign_add, zSign_nsmul_one, zSign_eq_pow, neg_one_pow_val_one]

/-- The coefficient `(-1)ʳ πᵢ^{r|j| + r(r-1)/2} [N, r]_{1,πᵢ}` at `π = -1`. -/
private def sCoeff (i j : I) (N r : ℕ) : k :=
  (-1) ^ r * C.pii (-1 : k) i ^ (r * (C.parity j).val + r.choose 2) *
    qpBinom (1 : kˣ) (C.pii (-1 : k) i) N r

private lemma sCoeff_succ (i j : I) (N r : ℕ) :
    C.sCoeff (k := k) i j (N + 1) (r + 1) = C.sCoeff (k := k) i j N (r + 1) -
      C.pii (-1 : k) i ^ N * C.pii (-1 : k) i ^ (C.parity j).val * C.sCoeff (k := k) i j N r := by
  rcases lt_or_ge N r with h | h
  · simp only [sCoeff, qpBinom_eq_zero_of_lt h, qpBinom_eq_zero_of_lt (by omega : N < r + 1),
      qpBinom_eq_zero_of_lt (by omega : N + 1 < r + 1), mul_zero, sub_zero]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [sCoeff, qpBinom_succ_succ', Units.val_one, inv_one, one_pow, one_mul, mul_one,
    Nat.choose_succ_succ', Nat.choose_one_right]
  rw [show r + m - r = m by omega]
  set s := C.pii (-1 : k) i
  set t := (C.parity j).val
  have e : s ^ ((r + 1) * t + (r.choose 2 + r)) * s ^ m =
      s ^ (r + m) * s ^ t * s ^ (r * t + r.choose 2) := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  linear_combination (-1 : k) ^ (r + 1) * qpBinom (1 : kˣ) s (r + m) r * e

/-- **The expansion of `(ad vᵢ)^N vⱼ`** in the free algebra, for the parity `|vᵢ| = |i|`:
`Σ_{r ≤ N} (-1)ʳ πᵢ^{r|j| + r(r-1)/2} [N, r]_{1,πᵢ} vᵢ^{N-r} vⱼ vᵢʳ` at `π = -1`. -/
theorem sLie_replicate_eq_sum (i j : I) (N : ℕ) :
    sLie (K := k) C.parity j (List.replicate N i) =
      ∑ r ∈ Finset.range (N + 1),
        C.sCoeff (k := k) i j N r • (θ k i ^ (N - r) * θ k j * θ k i ^ r) := by
  induction N with
  | zero => simp [sLie, sCoeff, θ]
  | succ N ih =>
    set M : ℕ → ℕ → PreF k I := fun n r ↦ θ k i ^ (n - r) * θ k j * θ k i ^ r with hM
    set ε := C.pii (-1 : k) i ^ N * C.pii (-1 : k) i ^ (C.parity j).val
    have h1 : ∀ x ∈ Finset.range (N + 1), FreeAlgebra.ι k i * (C.sCoeff (k := k) i j N x • M N x) =
        C.sCoeff (k := k) i j N x • M (N + 1) x := fun x hx ↦ by
      have hx := Finset.mem_range.1 hx
      rw [mul_smul_comm]; congr 1
      simp only [hM, ← mul_assoc, θ, ← pow_succ']
      rw [show N - x + 1 = N + 1 - x by omega]
    have h2 : ∀ x, ε • (C.sCoeff (k := k) i j N x • M N x * FreeAlgebra.ι k i) =
        (ε * C.sCoeff (k := k) i j N x) • M (N + 1) (x + 1) := fun x ↦ by
      rw [smul_mul_assoc, smul_smul]; congr 1
      simp only [hM, mul_assoc, θ, ← pow_succ, Nat.add_sub_add_right]
    have e : ∀ x, C.sCoeff (k := k) i j (N + 1) (x + 1) • M (N + 1) (x + 1) =
        C.sCoeff (k := k) i j N (x + 1) • M (N + 1) (x + 1) -
          (ε * C.sCoeff (k := k) i j N x) • M (N + 1) (x + 1) := fun x ↦ by
      rw [sCoeff_succ, sub_smul]
    have h0 : C.sCoeff (k := k) i j (N + 1) 0 = C.sCoeff (k := k) i j N 0 := by simp [sCoeff]
    have hN : C.sCoeff (k := k) i j N (N + 1) = 0 := by
      simp [sCoeff, qpBinom_eq_zero_of_lt (Nat.lt_succ_self N)]
    show _ = ∑ x ∈ Finset.range (N + 1 + 1), C.sCoeff (k := k) i j (N + 1) x • M (N + 1) x
    rw [List.replicate_succ, sLie, zSign_step, ih, Finset.mul_sum, Finset.sum_mul,
      Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun x hx ↦ by
        rw [h1 x hx, h2 x], Finset.sum_sub_distrib,
      Finset.sum_range_succ' (fun x ↦ C.sCoeff (k := k) i j (N + 1) x • M (N + 1) x),
      Finset.sum_congr rfl fun x _ ↦ e x, Finset.sum_sub_distrib, h0,
      Finset.sum_range_succ (fun x ↦ C.sCoeff (k := k) i j N (x + 1) • M (N + 1) (x + 1)), hN,
      zero_smul, add_zero,
      Finset.sum_range_succ' (fun x ↦ C.sCoeff (k := k) i j N x • M (N + 1) x)]
    abel

/-- **The quantum Serre elements at `q = 1`, `π = -1` are the super Serre elements** of the
contragredient Lie superalgebra: `serreElt 1 (-1) i j = (ad vᵢ)^{1 - aᵢⱼ} vⱼ` for `i ≠ j`. -/
theorem serreElt_one_neg_one {i j : I} (hij : i ≠ j) :
    C.serreElt (1 : kˣ) (-1) i j = superSerreFree k C.a C.parity i j := by
  have hN : C.serreDeg i j = (-C.a i j).toNat + 1 := by
    have := C.isGCM.offDiag_nonpos i j hij
    simp only [serreDeg]; omega
  rw [superSerreFree, ← hN, sLie_replicate_eq_sum, serreElt]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  simp [serreCoeff, sCoeff, qi, θ]

end SuperCartanDatum

end OddMath.CoveringQuantum
