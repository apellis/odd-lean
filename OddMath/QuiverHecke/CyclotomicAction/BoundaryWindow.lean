/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.BoundaryDivision
import Mathlib.Tactic.Abel

/-!
# The window matrix of the boundary map

The window matrix of displays (2) and (4) of `docs/Nondegeneracy/DeformedMatrixComparison.md`,
in the abstract polynomial window of `BoundaryDivision.lean`. The boundary map
`A_∂ : ⊕_k w_k B → ⊕_l t^l B` sends `Σ_k w_k b_k` to `Σ_k φ_k b_k` (`windowMap`), where
`φ_k = A_∂(w_k)` is the output of `boundary_division`: either `φ_k` has leading coefficient
`c` in degree `a + k` (`LeadsAt φ c a`, the case `a ≥ 0`), or `φ_k = 0` for `k < m` and
`φ_(m+j)` has leading coefficient `c` in degree `j` (the case `a = −m < 0`).

* `a ≥ 0` (`windowMap_add_low_existsUnique`): every `p` is uniquely `A_∂ w + r` with
  `deg r < a`. So `A_∂` is injective and its cokernel is the window `t^0 B, …, t^(a−1) B`;
  display (2) is bijective.
* `a = −m < 0` (`windowMap_cap_existsUnique`): `A_∂` is surjective, its kernel is
  `⊕_(k<m) w_k B` (`windowMap_eq_zero_iff`), and with the cap rows
  `G_r(v) = A_∂(v t^(r+1))(0)`, `r < m` (`capRow`), the map
  `v ↦ (A_∂ v, (G_r v)_(r<m))` is bijective; display (4) is bijective. On the kernel the cap
  matrix `G_r(w_k b) = φ_(r+k+1)(0) σ^(r+1)(b)` (`capRow_single`) vanishes above the
  anti-diagonal `r + k = m − 1` and is `c σ^(r+1)` on it.

`B` is an arbitrary ring and `c` a unit. The case `a ≥ 0` uses no hypothesis on `σ`; the cap
rows use that `σ` is bijective (for the source, `σ` is the identity or the parity involution).
-/

noncomputable section
open Finsupp
namespace OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

variable {B : Type*} [Ring B] (σ : B →+* B)

/-! ### The boundary map and the dot on the source -/

theorem rsmul_add_left (b b' : B) (p : ℕ →₀ B) : rsmul (b + b') p = rsmul b p + rsmul b' p := by
  ext l; simp [mul_add]

theorem rsmul_zero_left (p : ℕ →₀ B) : rsmul 0 p = 0 := by ext l; simp

/-- The boundary map `Σ_k w_k b_k ↦ Σ_k φ_k b_k`. -/
def windowMap (φ : ℕ → ℕ →₀ B) : (ℕ →₀ B) →+ (ℕ →₀ B) :=
  Finsupp.liftAddHom fun k =>
    { toFun := fun b => rsmul b (φ k)
      map_zero' := rsmul_zero_left _
      map_add' := fun b b' => rsmul_add_left b b' _ }

theorem windowMap_single (φ : ℕ → ℕ →₀ B) (k : ℕ) (b : B) :
    windowMap φ (single k b) = rsmul b (φ k) :=
  Finsupp.liftAddHom_apply_single _ k b

theorem windowMap_eq_sum (φ : ℕ → ℕ →₀ B) (w : ℕ →₀ B) :
    windowMap φ w = w.sum fun k b => rsmul b (φ k) := by
  conv_lhs => rw [← Finsupp.sum_single w]
  rw [map_finsuppSum]
  exact Finsupp.sum_congr fun k _ => windowMap_single φ k (w k)

theorem tShift_single (k : ℕ) (b : B) : tShift σ (single k b) = single (k + 1) (σ b) := by
  ext l
  rcases l with _ | l
  · simp
  · rw [tShift_succ]
    by_cases h : k = l
    · subst h; simp
    · rw [single_eq_of_ne (Ne.symm h), single_eq_of_ne (by omega), map_zero]

theorem tPow_single (j k : ℕ) (b : B) : tPow σ j (single k b) = single (k + j) (σ^[j] b) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [tPow_succ, ih, tShift_single, Function.iterate_succ_apply', add_assoc]

/-! ### Leading coefficients -/

/-- `φ_k` has leading coefficient `c` in degree `a + k` for every `k`. -/
def LeadsAt (φ : ℕ → ℕ →₀ B) (c : B) (a : ℕ) : Prop :=
  ∀ k, φ k (a + k) = c ∧ DegLT (φ k) (a + k + 1)

/-- The output of `boundary_division` in the case `D ≤ N` leads at `a = N − D`. -/
theorem leadsAt_of_monicDeg {φ : ℕ → ℕ →₀ B} (c : Bˣ) {a : ℕ}
    (h : ∀ k, MonicDeg (lsmul (↑c⁻¹ : B) (φ k)) (a + k)) : LeadsAt φ (c : B) a := by
  intro k
  have hk : ∀ l, φ k l = c * lsmul (↑c⁻¹ : B) (φ k) l := fun l => by
    rw [lsmul_apply, ← mul_assoc, c.mul_inv, one_mul]
  refine ⟨by rw [hk, (h k).1, mul_one], fun l hl => by rw [hk, (h k).2 l hl, mul_zero]⟩

/-- Leading term of `A_∂ w` when `deg w < K + 1`. -/
theorem windowMap_top {φ : ℕ → ℕ →₀ B} {c : B} {a : ℕ} (h : LeadsAt φ c a) {w : ℕ →₀ B}
    {K : ℕ} (hw : DegLT w (K + 1)) :
    windowMap φ w (a + K) = c * w K ∧ DegLT (windowMap φ w) (a + K + 1) := by
  have hsum : ∀ l, windowMap φ w l = ∑ k ∈ Finset.range (K + 1), φ k l * w k := by
    intro l
    rw [windowMap_eq_sum]
    rw [Finsupp.sum_of_support_subset w (s := Finset.range (K + 1)) (fun k hk => by
      rw [Finsupp.mem_support_iff] at hk
      rw [Finset.mem_range]
      by_contra hk'
      exact hk (hw k (by omega))) _ (fun k _ => rsmul_zero_left _)]
    rw [Finsupp.finsetSum_apply]
    simp
  refine ⟨?_, fun l hl => ?_⟩
  · rw [hsum, Finset.sum_eq_single K]
    · rw [(h K).1]
    · intro k hk hkK
      rw [(h k).2 (a + K) (by simp at hk; omega), zero_mul]
    · intro hK; simp at hK
  · rw [hsum]
    exact Finset.sum_eq_zero fun k hk => by
      rw [(h k).2 l (by simp at hk; omega), zero_mul]

/-- Every `w` has a degree bound. -/
theorem exists_degLT (w : ℕ →₀ B) : ∃ n, DegLT w n := by
  refine ⟨w.support.sup id + 1, fun l hl => ?_⟩
  by_contra h
  have := Finset.le_sup (f := id) (Finsupp.mem_support_iff.mpr h)
  simp at this
  omega

/-- If `A_∂ w + r = 0` with `deg r < a`, then `w = 0`. -/
theorem windowMap_eq_zero_of_add {φ : ℕ → ℕ →₀ B} {c : B} (hc : IsUnit c) {a : ℕ}
    (h : LeadsAt φ c a) {w r : ℕ →₀ B} (hr : DegLT r a) (hwr : windowMap φ w + r = 0) :
    w = 0 := by
  obtain ⟨n, hn⟩ := exists_degLT w
  induction n with
  | zero => exact (degLT_zero_iff w).mp hn
  | succ K ih =>
    apply ih
    intro l hl
    rcases Nat.lt_or_ge K l with hlt | hle
    · exact hn l hlt
    · have hl' : l = K := le_antisymm hle hl
      subst hl'
      have h0 := congrArg (· (a + l)) hwr
      simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply,
        hr (a + l) (by omega), add_zero, (windowMap_top h hn).1] at h0
      exact (hc.mul_right_eq_zero).mp h0

/-! ### The case `a ≥ 0`: display (2) -/

/-- **Window matrix, `a ≥ 0`.** Every `p` is uniquely `A_∂ w + r` with `deg r < a`: the
boundary map is injective with cokernel the window `t^0 B, …, t^(a−1) B`. -/
theorem windowMap_add_low_existsUnique {φ : ℕ → ℕ →₀ B} {c : B} (hc : IsUnit c) {a : ℕ}
    (h : LeadsAt φ c a) (p : ℕ →₀ B) :
    ∃! wr : (ℕ →₀ B) × (ℕ →₀ B), DegLT wr.2 a ∧ windowMap φ wr.1 + wr.2 = p := by
  obtain ⟨u, rfl⟩ := hc
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨n, hn⟩ := exists_degLT p
    induction n generalizing p with
    | zero => exact ⟨(0, 0), DegLT.zero _, by rw [(degLT_zero_iff p).mp hn]; simp⟩
    | succ n ih =>
      by_cases hna : n < a
      · exact ⟨(0, p), hn.mono (by omega), by simp⟩
      obtain ⟨K, rfl⟩ : ∃ K, n = a + K := ⟨n - a, by omega⟩
      set w₁ := single K ((↑u⁻¹ : B) * p (a + K))
      have hw₁ : DegLT w₁ (K + 1) := fun l hl => single_eq_of_ne (by omega)
      obtain ⟨htop, habove⟩ := windowMap_top h hw₁
      obtain ⟨⟨w, r⟩, hr, hwr⟩ := ih (p - windowMap φ w₁) (by
        intro l hl
        rcases Nat.lt_or_ge (a + K) l with hlt | hle
        · simp [hn l hlt, habove l hlt]
        · have : l = a + K := by omega
          subst this
          simp [htop, w₁, ← mul_assoc])
      exact ⟨(w + w₁, r), hr, by rw [map_add, add_right_comm, hwr]; abel⟩
  · rintro ⟨w, r⟩ ⟨w', r'⟩ ⟨hr, hp⟩ ⟨hr', hp'⟩
    have hdiff : windowMap φ (w - w') + (r - r') = 0 := by
      rw [map_sub, sub_add_sub_comm, hp, hp', sub_self]
    have hw := windowMap_eq_zero_of_add u.isUnit h (hr.sub hr') hdiff
    rw [hw, map_zero, zero_add, sub_eq_zero] at hdiff
    rw [sub_eq_zero.mp hw, hdiff]

/-! ### The case `a = −m < 0`: display (4) -/

section Negative

variable {φ : ℕ → ℕ →₀ B} {c : B} {m : ℕ}

theorem windowMap_shift_eq (w : ℕ →₀ B) :
    windowMap φ (tPow (RingHom.id B) m w) = windowMap (fun j => φ (m + j)) w := by
  have : (windowMap φ).comp (tPow (RingHom.id B) m) = windowMap (fun j => φ (m + j)) :=
    Finsupp.addHom_ext fun k b => by
      simp [tPow_single, windowMap_single, add_comm k m, RingHom.coe_id, Function.iterate_id]
  exact DFunLike.congr_fun this w

/-- `A_∂` kills `w_k` for `k < m`. -/
theorem windowMap_eq_of_low (hzero : ∀ k < m, φ k = 0) {w : ℕ →₀ B} (hw : DegLT w m) :
    windowMap φ w = 0 := by
  rw [windowMap_eq_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finsupp.mem_support_iff] at hk
  have hkm : k < m := by by_contra h; exact hk (hw k (by omega))
  show rsmul (w k) (φ k) = 0
  rw [hzero k hkm, map_zero]

/-- Splitting `w` into its part below `m` and the shift of its part at and above `m`. -/
theorem exists_split (w : ℕ →₀ B) :
    ∃ u v : ℕ →₀ B, DegLT u m ∧ w = u + tPow (RingHom.id B) m v := by
  classical
  refine ⟨w.filter (· < m), Finsupp.comapDomain (· + m) w (fun _ _ _ _ h => by
      simpa using h), fun l hl => by simp [Finsupp.filter_apply]; omega, ?_⟩
  ext l
  rw [Finsupp.add_apply, Finsupp.filter_apply]
  split_ifs with hl
  · rw [tPow_apply_of_lt _ _ _ hl, add_zero]
  · obtain ⟨j, rfl⟩ : ∃ j, l = j + m := ⟨l - m, by omega⟩
    rw [tPow_add_apply, Finsupp.comapDomain_apply]
    simp

/-- **Kernel, `a = −m < 0`.** `A_∂ w = 0` iff `w` lies in `⊕_(k<m) w_k B`. -/
theorem windowMap_eq_zero_iff (hc : IsUnit c) (hzero : ∀ k < m, φ k = 0)
    (h : LeadsAt (fun j => φ (m + j)) c 0) (w : ℕ →₀ B) :
    windowMap φ w = 0 ↔ DegLT w m := by
  refine ⟨fun hw => ?_, windowMap_eq_of_low hzero⟩
  obtain ⟨u, v, hu, rfl⟩ := exists_split (m := m) w
  rw [map_add, windowMap_eq_of_low hzero hu, zero_add, windowMap_shift_eq] at hw
  have hv : v = 0 := windowMap_eq_zero_of_add hc h (DegLT.zero 0) (by rw [hw, add_zero])
  rw [hv, map_zero, add_zero]
  exact hu

/-- **Surjectivity, `a = −m < 0`.** -/
theorem windowMap_surjective (hc : IsUnit c)
    (h : LeadsAt (fun j => φ (m + j)) c 0) (p : ℕ →₀ B) : ∃ w, windowMap φ w = p := by
  obtain ⟨⟨v, r⟩, ⟨hr, hp⟩, -⟩ := windowMap_add_low_existsUnique hc h p
  rw [(degLT_zero_iff r).mp hr, add_zero] at hp
  exact ⟨tPow (RingHom.id B) m v, by rw [windowMap_shift_eq, hp]⟩

/-- The cap row `G_r(v) = A_∂(v t^(r+1))(0)`. -/
def capRow (φ : ℕ → ℕ →₀ B) (r : ℕ) : (ℕ →₀ B) →+ B :=
  (Finsupp.applyAddHom 0).comp ((windowMap φ).comp (tPow σ (r + 1)))

theorem capRow_single (φ : ℕ → ℕ →₀ B) (r k : ℕ) (b : B) :
    capRow σ φ r (single k b) = φ (k + r + 1) 0 * σ^[r + 1] b := by
  simp [capRow, tPow_single, windowMap_single, add_assoc]

theorem capRow_eq_sum (φ : ℕ → ℕ →₀ B) (r : ℕ) (w : ℕ →₀ B) :
    capRow σ φ r w = w.sum fun k b => φ (k + r + 1) 0 * σ^[r + 1] b := by
  conv_lhs => rw [← Finsupp.sum_single w]
  rw [map_finsuppSum]
  exact Finsupp.sum_congr fun k _ => capRow_single σ φ r k (w k)

/-- The cap matrix on the kernel is anti-triangular: for `deg w < K + 1 ≤ m`, the row
`r = m − 1 − K` sees only `w_K`, through `c σ^(r+1)`. -/
theorem capRow_antidiagonal (hzero : ∀ k < m, φ k = 0) (h : LeadsAt (fun j => φ (m + j)) c 0)
    {w : ℕ →₀ B} {K : ℕ} (hw : DegLT w (K + 1)) (hK : K < m) :
    capRow σ φ (m - 1 - K) w = c * σ^[m - K] (w K) := by
  rw [capRow_eq_sum, Finsupp.sum_eq_single K]
  · have hidx : K + (m - 1 - K) + 1 = m + 0 := by omega
    rw [hidx, (h 0).1, show m - 1 - K + 1 = m - K by omega]
  · intro k hk hkK
    have hkK' : k < K := by
      by_contra h'
      exact hk (hw k (by omega))
    rw [hzero _ (by omega)]
    simp
  · intro _; simp

/-- Rows `r < j` do not see `w_k` for `k + j < m`: `capRow` of `w_k` vanishes in those rows. -/
theorem capRow_single_eq_zero (hzero : ∀ k < m, φ k = 0) {r k : ℕ} (hrk : k + r + 1 < m)
    (b : B) : capRow σ φ r (single k b) = 0 := by
  rw [capRow_single, hzero _ hrk]
  simp

/-- **Cap rows, `a = −m < 0`.** For `σ` bijective, `v ↦ (A_∂ v, (G_r v)_(r<m))` is bijective:
every `p` and every row vector `x` have a unique `v` with `A_∂ v = p` and `G_r v = x_r` for
`r < m`. -/
theorem windowMap_cap_existsUnique (hσ : Function.Bijective σ) (hc : IsUnit c)
    (hzero : ∀ k < m, φ k = 0) (h : LeadsAt (fun j => φ (m + j)) c 0) (p : ℕ →₀ B)
    (x : ℕ → B) :
    ∃! v : ℕ →₀ B, windowMap φ v = p ∧ ∀ r < m, capRow σ φ r v = x r := by
  obtain ⟨u, rfl⟩ := hc
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨w₀, hw₀⟩ := windowMap_surjective u.isUnit h p
    -- correct the rows `r < j` by a kernel element supported on `[m − j, m)`
    have key : ∀ j ≤ m, ∃ u' : ℕ →₀ B, DegLT u' m ∧
        ∀ r < j, capRow σ φ r (w₀ + u') = x r := by
      intro j
      induction j with
      | zero => exact fun _ => ⟨0, DegLT.zero _, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
      | succ j ih =>
        intro hj
        obtain ⟨u', hu', hrows⟩ := ih (by omega)
        set y := capRow σ φ j (w₀ + u')
        obtain ⟨b, hb⟩ := (hσ.iterate (j + 1)).2 ((↑u⁻¹ : B) * (x j - y))
        refine ⟨u' + single (m - 1 - j) b, DegLT.add hu' (fun l hl =>
          single_eq_of_ne (by omega)), fun r hr => ?_⟩
        rw [← add_assoc, map_add]
        rcases Nat.lt_or_ge r j with hrj | hrj
        · rw [hrows r hrj, capRow_single_eq_zero σ hzero (by omega), add_zero]
        · have hrj' : r = j := by omega
          subst hrj'
          rw [capRow_single, show m - 1 - r + r + 1 = m + 0 by omega, (h 0).1, hb,
            ← mul_assoc, u.mul_inv, one_mul]
          abel
    obtain ⟨u', hu', hrows⟩ := key m le_rfl
    exact ⟨w₀ + u', by rw [map_add, windowMap_eq_of_low hzero hu', add_zero, hw₀], hrows⟩
  · rintro v v' ⟨hv, hrv⟩ ⟨hv', hrv'⟩
    rw [← sub_eq_zero]
    have hker : windowMap φ (v - v') = 0 := by rw [map_sub, hv, hv', sub_self]
    have hlow := (windowMap_eq_zero_iff u.isUnit hzero h _).mp hker
    have hrows : ∀ r < m, capRow σ φ r (v - v') = 0 := fun r hr => by
      rw [map_sub, hrv r hr, hrv' r hr, sub_self]
    -- descending induction on the degree bound inside `[0, m)`
    have : ∀ n ≤ m, DegLT (v - v') n → v - v' = 0 := by
      intro n
      induction n with
      | zero => exact fun _ hn => (degLT_zero_iff _).mp hn
      | succ K ih =>
        intro hK hn
        apply ih (by omega)
        intro l hl
        rcases Nat.lt_or_ge K l with hlt | hle
        · exact hn l hlt
        · have hl' : l = K := le_antisymm hle hl
          subst hl'
          have h0 := hrows (m - 1 - l) (by omega)
          rw [capRow_antidiagonal σ hzero h hn (by omega)] at h0
          have h1 : σ^[m - l] ((v - v') l) = 0 := (u.isUnit.mul_right_eq_zero).mp h0
          exact (hσ.1.iterate (m - l)) (by rw [h1, iterate_map_zero])
    exact this m le_rfl hlow

end Negative

end OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial
