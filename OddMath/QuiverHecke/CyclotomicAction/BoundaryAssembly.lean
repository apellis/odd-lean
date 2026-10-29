/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.BoundaryWindow

/-!
# From the Mackey boundary to the window matrix

The abstract part of `docs/Nondegeneracy/DeformedMackeyBoundary.md` §3 and
`docs/Nondegeneracy/DeformedBoundaryDivision.md` §§4–5: the recurrence (8) and the norm (7)
for every corrected iterate, derived from the operator identities of the boundary, and their
consequence for the window matrix of `BoundaryWindow.lean`.

`MackeyBoundary` records the data of the boundary, as additive maps:

* `P : L₁ → L₀` with `P ρ = R_t P` (`P_ρ`);
* the split decomposition `L₀ = F(L₀') ⊕ j(V₀)` (`direct`), with the equal-colour dot slide
  `F(u) t = F(X u) + j(E u)` (`Rt_F`) and `j(f) t = j(f t)` (`Rt_j`);
* the extraction `B₁ : L₁ → V₁`, in the corrected coordinates `w_k` (so `V₁ = ⊕_k w_k B` is
  `ℕ →₀ B` and `ρ̄` is `tShift σ`), intertwining `ρ` and `ρ̄` (`B₁_ρ`) and surjective
  (`B₁_surjective`, the compatible lifts);
* the boundary `A_∂ : V₁ → V₀`, right `B`-linear (`A_rsmul`), with `C₀ P = A_∂ B₁` (`P_split`:
  the polynomial component of `P z` is `A_∂(B₁ z)`).

`MackeyBoundary.recurrence` is (8): `φ_(k+1) − φ_k t ∈ B` for `φ_k = A_∂(w_k)`.
`MackeyBoundary.norm` is (7) for every `k`, from one lift `z₀` of `S(ρ̄) w₀` whose `P`-image is
`j(c F)` (the reverse norm identity (5) of `DeformedBoundaryDivision.md` at `k = 0`); the
coefficients of `S` are `σ`-fixed (they are even). The headline `MackeyBoundary.window_pos`
and `MackeyBoundary.window_neg` then give displays (2) and (4) of
`DeformedMatrixComparison.md`: for `D ≤ N` (`a = N − D ≥ 0`) every `p` is uniquely
`A_∂ w + r` with `deg r < a`; for `N < D` (`m = D − N`), `v ↦ (A_∂ v, (G_r v)_(r<m))` is
bijective.

The concrete instances of these fields (the affine Mackey PBW decomposition after tensoring
with the cyclotomic quotient, the short-coset extraction, `P ρ = R_t P` and the reverse norm)
are not formalized here.
-/

noncomputable section
open Finsupp
namespace OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

variable {B : Type*} [Ring B] (σ : B →+* B)

/-- The operator data of the first-order Mackey boundary. -/
structure MackeyBoundary (L₁ L₀ L₀' : Type*) [AddCommGroup L₁] [AddCommGroup L₀]
    [AddCommGroup L₀'] where
  /-- The map `P(h ⊗ b) = h f_i(x₁) T ⊗ b`. -/
  P : L₁ →+ L₀
  /-- The corrected operator `ρ` on the source. -/
  ρ : L₁ →+ L₁
  /-- The target right-dot action `R_t`. -/
  Rt : L₀ →+ L₀
  /-- The crossing summand `F : L₀' → L₀`. -/
  F : L₀' →+ L₀
  /-- The polynomial summand `j(t^l b) = x_(n+1)^l e ⊗ b`. -/
  j : (ℕ →₀ B) →+ L₀
  /-- The crossing-contraction operator `X` on `L₀'`. -/
  X : L₀' →+ L₀'
  /-- The degree-zero operator `E : L₀' → B`. -/
  E : L₀' →+ B
  /-- The extraction `B₁`, in the corrected coordinates `w_k`. -/
  B₁ : L₁ →+ (ℕ →₀ B)
  /-- The boundary `A_∂`. -/
  A : (ℕ →₀ B) →+ (ℕ →₀ B)
  P_ρ : ∀ z, P (ρ z) = Rt (P z)
  Rt_F : ∀ u, Rt (F u) = F (X u) + j (single 0 (E u))
  Rt_j : ∀ f, Rt (j f) = j (tShift σ f)
  direct : ∀ u f, F u + j f = 0 → u = 0 ∧ f = 0
  B₁_ρ : ∀ z, B₁ (ρ z) = tShift σ (B₁ z)
  B₁_surjective : Function.Surjective B₁
  P_split : ∀ z, ∃ u, P z = F u + j (A (B₁ z))
  A_rsmul : ∀ (b : B) v, A (rsmul b v) = rsmul b (A v)

namespace MackeyBoundary

variable {σ} {L₁ L₀ L₀' : Type*} [AddCommGroup L₁] [AddCommGroup L₀] [AddCommGroup L₀']
  (M : MackeyBoundary σ L₁ L₀ L₀')

/-- The images `φ_k = A_∂(w_k)` of the corrected coordinates. -/
def φ (k : ℕ) : ℕ →₀ B := M.A (single k 1)

theorem eq_of_direct {u u' : L₀'} {f f' : ℕ →₀ B} (h : M.F u + M.j f = M.F u' + M.j f') :
    u = u' ∧ f = f' := by
  have := M.direct (u - u') (f - f') (by
    rw [map_sub, map_sub, sub_add_sub_comm, h, sub_self])
  exact ⟨sub_eq_zero.mp this.1, sub_eq_zero.mp this.2⟩

theorem Rt_pow_j (k : ℕ) (f : ℕ →₀ B) : (M.Rt^[k]) (M.j f) = M.j (tPow σ k f) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, M.Rt_j, tPow_succ]

theorem P_ρ_pow (k : ℕ) (z : L₁) : M.P ((M.ρ)^[k] z) = (M.Rt^[k]) (M.P z) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', M.P_ρ, ih]

theorem B₁_ρ_pow (k : ℕ) (z : L₁) : M.B₁ ((M.ρ)^[k] z) = tPow σ k (M.B₁ z) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', M.B₁_ρ, ih, tPow_succ]

/-- The first-order defect: `A_∂(ρ̄ v) − A_∂(v) t = E ψ(v)` lies in degree zero. -/
theorem A_tShift (v : ℕ →₀ B) : ∃ e : B, M.A (tShift σ v) = single 0 e + tShift σ (M.A v) := by
  obtain ⟨z, rfl⟩ := M.B₁_surjective v
  obtain ⟨u, hu⟩ := M.P_split z
  obtain ⟨u', hu'⟩ := M.P_split (M.ρ z)
  refine ⟨M.E u, ?_⟩
  have h : M.F u' + M.j (M.A (M.B₁ (M.ρ z))) =
      M.F (M.X u) + M.j (single 0 (M.E u) + tShift σ (M.A (M.B₁ z))) := by
    rw [← hu', M.P_ρ, hu, map_add, M.Rt_F, M.Rt_j, map_add, add_assoc]
  rw [← M.B₁_ρ]
  exact (M.eq_of_direct h).2

/-- **(8)**: `deg(φ_(k+1) − φ_k t) < 1`. -/
theorem recurrence (k : ℕ) : DegLT (M.φ (k + 1) - tShift σ (M.φ k)) 1 := by
  obtain ⟨e, he⟩ := M.A_tShift (single k 1)
  have hs : tShift σ (single k (1 : B)) = single (k + 1) 1 := by
    rw [tShift_single, map_one]
  unfold φ
  rw [← hs, he, add_sub_cancel_right]
  intro l hl
  rw [single_eq_of_ne (by omega)]

theorem A_eq_windowMap : M.A = windowMap M.φ := by
  refine Finsupp.addHom_ext fun k b => ?_
  rw [windowMap_single, φ, ← M.A_rsmul]
  congr 1
  ext l
  simp [single_apply]

/-- **(7) for every corrected iterate.** If a lift `z₀` of `S(ρ̄) w₀ = Σ_j w_j b_j` has
`P z₀ = j(c F)`, with `σ`-fixed coefficients `b_j` and `c`, then
`Σ_j φ_(k+j) b_j = c F t^k` for every `k`. -/
theorem norm {S F : ℕ →₀ B} {D : ℕ} (hS : DegLT S (D + 1)) (hSσ : ∀ j, σ (S j) = S j)
    {c : B} (hc : σ c = c) {z₀ : L₁} (hz₁ : M.B₁ z₀ = S) (hz₀ : M.P z₀ = M.j (lsmul c F))
    (k : ℕ) :
    ∑ j ∈ Finset.range (D + 1), rsmul (S j) (M.φ (k + j)) = lsmul c (tPow σ k F) := by
  obtain ⟨u, hu⟩ := M.P_split ((M.ρ)^[k] z₀)
  have h : M.F u + M.j (M.A (tPow σ k S)) = M.F 0 + M.j (lsmul c (tPow σ k F)) := by
    rw [M.B₁_ρ_pow, hz₁] at hu
    rw [← hu, M.P_ρ_pow, hz₀, M.Rt_pow_j, map_zero, zero_add, lsmul_tPow σ hc]
  rw [← (M.eq_of_direct h).2]
  have hpow : tPow σ k S = ∑ j ∈ Finset.range (D + 1), rsmul (S j) (single (k + j) 1) := by
    ext l
    rw [Finsupp.finsetSum_apply]
    simp only [rsmul_apply, single_apply]
    by_cases hl : k ≤ l
    · obtain ⟨j, rfl⟩ : ∃ j, l = j + k := ⟨l - k, by omega⟩
      rw [tPow_add_apply, Function.iterate_fixed (hSσ j)]
      by_cases hj : j < D + 1
      · rw [Finset.sum_eq_single j]
        · simp [add_comm]
        · intro j' _ hj'
          rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), zero_mul]
        · intro hj'; simp at hj'; omega
      · rw [hS j (by omega), Finset.sum_eq_zero]
        intro j' hj'
        simp at hj'
        rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), zero_mul]
    · rw [tPow_apply_of_lt σ k S (by omega), Finset.sum_eq_zero]
      intro j' _
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), zero_mul]
  rw [hpow, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [M.A_rsmul]; rfl

/-- The division conclusion (12) for the boundary. -/
theorem division (hσ : Function.Injective σ) {S F : ℕ →₀ B} {D N : ℕ} (hS : MonicDeg S D)
    (hF : MonicDeg F N) (hSσ : ∀ j, σ (S j) = S j) (c : Bˣ) (hc : σ c = c) {z₀ : L₁}
    (hz₁ : M.B₁ z₀ = S) (hz₀ : M.P z₀ = M.j (lsmul (c : B) F)) (k : ℕ) :
    (N + k < D → M.φ k = 0) ∧
      (D ≤ N + k → MonicDeg (lsmul (↑c⁻¹ : B) (M.φ k)) (N + k - D)) :=
  boundary_division σ hσ M.φ M.recurrence hS hF c hc
    (M.norm hS.2 hSσ hc hz₁ hz₀) k

/-- **Display (2), `a = N − D ≥ 0`.** Every `p` is uniquely `A_∂ w + r` with `deg r < a`. -/
theorem window_pos (hσ : Function.Injective σ) {S F : ℕ →₀ B} {D N : ℕ} (hS : MonicDeg S D)
    (hF : MonicDeg F N) (hSσ : ∀ j, σ (S j) = S j) (c : Bˣ) (hc : σ c = c) {z₀ : L₁}
    (hz₁ : M.B₁ z₀ = S) (hz₀ : M.P z₀ = M.j (lsmul (c : B) F)) (hDN : D ≤ N)
    (p : ℕ →₀ B) :
    ∃! wr : (ℕ →₀ B) × (ℕ →₀ B), DegLT wr.2 (N - D) ∧ M.A wr.1 + wr.2 = p := by
  have hlead : LeadsAt M.φ (c : B) (N - D) := leadsAt_of_monicDeg c fun k => by
    have := (M.division hσ hS hF hSσ c hc hz₁ hz₀ k).2 (by omega)
    rwa [show N + k - D = N - D + k by omega] at this
  rw [M.A_eq_windowMap]
  exact windowMap_add_low_existsUnique c.isUnit hlead p

/-- **Display (4), `a = N − D < 0`.** With `m = D − N` and `σ` bijective,
`v ↦ (A_∂ v, (G_r v)_(r<m))` is bijective. -/
theorem window_neg (hσ : Function.Bijective σ) {S F : ℕ →₀ B} {D N : ℕ} (hS : MonicDeg S D)
    (hF : MonicDeg F N) (hSσ : ∀ j, σ (S j) = S j) (c : Bˣ) (hc : σ c = c) {z₀ : L₁}
    (hz₁ : M.B₁ z₀ = S) (hz₀ : M.P z₀ = M.j (lsmul (c : B) F)) (hND : N < D)
    (p : ℕ →₀ B) (x : ℕ → B) :
    ∃! v : ℕ →₀ B, M.A v = p ∧ ∀ r < D - N, capRow σ M.φ r v = x r := by
  have hdiv := M.division hσ.1 hS hF hSσ c hc hz₁ hz₀
  have hzero : ∀ k < D - N, M.φ k = 0 := fun k hk => (hdiv k).1 (by omega)
  have hlead : LeadsAt (fun j => M.φ (D - N + j)) (c : B) 0 := leadsAt_of_monicDeg c fun j => by
    have := (hdiv (D - N + j)).2 (by omega)
    rwa [show N + (D - N + j) - D = 0 + j by omega] at this
  rw [M.A_eq_windowMap]
  exact windowMap_cap_existsUnique σ hσ c.isUnit hzero hlead p x

end MackeyBoundary

end OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial
