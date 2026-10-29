/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Group.Units.Basic

/-!
# Finite monic division in the moving-dot polynomial window

The division step of `docs/Nondegeneracy/DeformedBoundaryDivision.md` §5 (cf. KKO I,
arXiv:1206.5933v2, Proposition 9.3 and Lemma 9.5; Kang–Kashiwara, arXiv:1102.4677v4,
Lemma 4.19), over an arbitrary ring `B` with a ring endomorphism `σ`.

The polynomial window `V₀ = ⊕_l t^l B` of the boundary is modelled by `ℕ →₀ B`: the
coefficient of `t^l` sits at `l`, coefficients act on the right, and the moving dot acts on
the right semilinearly, `(t^l b) t = t^(l+1) σ(b)` (`tShift`); for an odd colour `σ` is the
parity involution of `B`, for an even colour `σ = id`. The product `p ⋆ q` (`skewMul`) is
the product of the skew polynomial ring with `b t = t σ(b)`.

`boundary_division` is the conclusion (12) of §5: if `φ_k = A_∂(w_k)` satisfies the first-order
recurrence (8), `deg(φ_(k+1) − φ_k t) < 1`, and the norm identity (7),
`Σ_j φ_(k+j) b_j = c F t^k` with `S = Σ_j t^j b_j` monic of degree `D`, `F` monic of degree
`N` and `c` a `σ`-fixed unit, then `φ_k = 0` when `N + k < D` and `c⁻¹ φ_k` is monic of degree
`N + k − D` otherwise. In the source notation `N = a + D` with `a = ⟨h_i, Λ − β⟩` and
`γ = c⁻¹`.

No commutativity of `B`, no centrality of the coefficients of `S`, no freeness and no inverse
beyond `c` is used; `B` may have zero divisors and may be the zero ring. The injectivity of `σ`
is used once, to read off a leading coefficient.
-/

noncomputable section
open Finsupp
namespace OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

variable {B : Type*} [Ring B] (σ : B →+* B)

/-! ### Operations on the window -/

/-- Right multiplication of every coefficient by `b`. -/
def rsmul (b : B) : (ℕ →₀ B) →+ (ℕ →₀ B) where
  toFun p := p.mapRange (· * b) (zero_mul b)
  map_zero' := by ext; simp
  map_add' p q := by ext; simp [add_mul]

@[simp] theorem rsmul_apply (b : B) (p : ℕ →₀ B) (l : ℕ) : rsmul b p l = p l * b := by
  simp [rsmul]

/-- Left multiplication of every coefficient by `c` (a scalar such as `γ`). -/
def lsmul (c : B) : (ℕ →₀ B) →+ (ℕ →₀ B) where
  toFun p := p.mapRange (c * ·) (mul_zero c)
  map_zero' := by ext; simp
  map_add' p q := by ext; simp [mul_add]

@[simp] theorem lsmul_apply (c : B) (p : ℕ →₀ B) (l : ℕ) : lsmul c p l = c * p l := by
  simp [lsmul]

/-- Right multiplication by the moving dot: `(t^l b) t = t^(l+1) σ(b)`. -/
def tShift : (ℕ →₀ B) →+ (ℕ →₀ B) :=
  (Finsupp.mapDomain.addMonoidHom Nat.succ).comp (Finsupp.mapRange.addMonoidHom σ.toAddMonoidHom)

@[simp] theorem tShift_succ (p : ℕ →₀ B) (l : ℕ) : tShift σ p (l + 1) = σ (p l) := by
  simp only [tShift, AddMonoidHom.comp_apply, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.mapRange.addMonoidHom_apply]
  exact (Finsupp.mapDomain_apply_of_injective Nat.succ_injective _ l).trans (by simp)

@[simp] theorem tShift_zero (p : ℕ →₀ B) : tShift σ p 0 = 0 := by
  simp only [tShift, AddMonoidHom.comp_apply, Finsupp.mapDomain.addMonoidHom_apply]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)

/-- Right multiplication by `t^j`. -/
def tPow : ℕ → (ℕ →₀ B) →+ (ℕ →₀ B)
  | 0 => AddMonoidHom.id _
  | j + 1 => (tShift σ).comp (tPow j)

theorem tPow_succ (j : ℕ) (p : ℕ →₀ B) : tPow σ (j + 1) p = tShift σ (tPow σ j p) := rfl

@[simp] theorem tPow_zero (p : ℕ →₀ B) : tPow σ 0 p = p := rfl

theorem tPow_add_apply (j : ℕ) (p : ℕ →₀ B) (l : ℕ) : tPow σ j p (l + j) = σ^[j] (p l) := by
  induction j generalizing l with
  | zero => simp
  | succ j ih =>
    rw [tPow_succ, show l + (j + 1) = l + j + 1 by omega, tShift_succ, ih,
      Function.iterate_succ_apply']

theorem tPow_apply_of_lt (j : ℕ) (p : ℕ →₀ B) {l : ℕ} (hl : l < j) : tPow σ j p l = 0 := by
  induction j generalizing l with
  | zero => omega
  | succ j ih =>
    rw [tPow_succ]
    rcases l with _ | l
    · exact tShift_zero σ _
    · rw [tShift_succ, ih (by omega), map_zero]

/-- The skew product `p ⋆ q = Σ_j (p t^j) q_j` of the skew polynomial ring `b t = t σ(b)`. -/
def skewMul (p q : ℕ →₀ B) : ℕ →₀ B := q.sum fun j b => rsmul b (tPow σ j p)

/-! ### Degree bounds -/

/-- All coefficients in degrees `≥ n` vanish: `deg p < n`. -/
def DegLT (p : ℕ →₀ B) (n : ℕ) : Prop := ∀ l, n ≤ l → p l = 0

/-- `p` is monic of degree `n`: leading coefficient `1` in degree `n`, nothing above. -/
def MonicDeg (p : ℕ →₀ B) (n : ℕ) : Prop := p n = 1 ∧ DegLT p (n + 1)

namespace DegLT

variable {σ}

theorem mono {p : ℕ →₀ B} {n m : ℕ} (h : DegLT p n) (hnm : n ≤ m) : DegLT p m :=
  fun l hl => h l (hnm.trans hl)

theorem zero (n : ℕ) : DegLT (0 : ℕ →₀ B) n := fun _ _ => rfl

theorem add {p q : ℕ →₀ B} {n : ℕ} (hp : DegLT p n) (hq : DegLT q n) : DegLT (p + q) n :=
  fun l hl => by simp [hp l hl, hq l hl]

theorem sub {p q : ℕ →₀ B} {n : ℕ} (hp : DegLT p n) (hq : DegLT q n) : DegLT (p - q) n :=
  fun l hl => by simp [hp l hl, hq l hl]

theorem rsmul {p : ℕ →₀ B} {n : ℕ} (hp : DegLT p n) (b : B) : DegLT (rsmul b p) n :=
  fun l hl => by simp [hp l hl]

theorem lsmul {p : ℕ →₀ B} {n : ℕ} (hp : DegLT p n) (c : B) : DegLT (lsmul c p) n :=
  fun l hl => by simp [hp l hl]

theorem tShift {p : ℕ →₀ B} {n : ℕ} (hp : DegLT p n) : DegLT (tShift σ p) (n + 1) := by
  intro l hl
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  rw [tShift_succ, hp l (by omega), map_zero]

theorem sum {ι : Type*} (s : Finset ι) {f : ι → ℕ →₀ B} {n : ℕ}
    (h : ∀ x ∈ s, DegLT (f x) n) : DegLT (∑ x ∈ s, f x) n := by
  intro l hl
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun x hx => h x hx l hl

end DegLT

theorem degLT_zero_iff (p : ℕ →₀ B) : DegLT p 0 ↔ p = 0 :=
  ⟨fun h => Finsupp.ext fun l => h l (Nat.zero_le l), fun h => h ▸ DegLT.zero 0⟩

/-- Writing `skewMul` over a range containing the support of `q`. -/
theorem skewMul_eq_sum_range (p q : ℕ →₀ B) {D : ℕ} (hq : DegLT q (D + 1)) :
    skewMul σ p q = ∑ j ∈ Finset.range (D + 1), rsmul (q j) (tPow σ j p) := by
  unfold skewMul
  refine Finsupp.sum_of_support_subset q (fun j hj => ?_) _ (fun j _ => by ext; simp)
  rw [Finsupp.mem_support_iff] at hj
  rw [Finset.mem_range]
  by_contra h
  exact hj (hq j (by omega))

/-! ### Telescoping the first-order recurrence, (9) and (10) -/

/-- (9): if `deg(φ_(k+1) − φ_k t) < 1` for all `k`, then `deg(φ_(k+j) − φ_k t^j) < j`. -/
theorem degLT_sub_tPow (φ : ℕ → ℕ →₀ B) (hφ : ∀ k, DegLT (φ (k + 1) - tShift σ (φ k)) 1)
    (k j : ℕ) : DegLT (φ (k + j) - tPow σ j (φ k)) j := by
  induction j with
  | zero => simpa using DegLT.zero (B := B) 0
  | succ j ih =>
    have h : φ (k + (j + 1)) - tPow σ (j + 1) (φ k) =
        (φ (k + j + 1) - tShift σ (φ (k + j))) +
          tShift σ (φ (k + j) - tPow σ j (φ k)) := by
      rw [tPow_succ, map_sub, sub_add_sub_cancel]
      rfl
    rw [h]
    exact ((hφ (k + j)).mono (by omega)).add (DegLT.tShift ih)

/-- (10): the norm of the corrected iterates agrees with `φ_k ⋆ S` below degree `D`. -/
theorem degLT_norm_sub_skewMul (φ : ℕ → ℕ →₀ B)
    (hφ : ∀ k, DegLT (φ (k + 1) - tShift σ (φ k)) 1) (S : ℕ →₀ B) {D : ℕ}
    (hS : DegLT S (D + 1)) (k : ℕ) :
    DegLT ((∑ j ∈ Finset.range (D + 1), rsmul (S j) (φ (k + j))) - skewMul σ (φ k) S) D := by
  rw [skewMul_eq_sum_range σ _ _ hS, ← Finset.sum_sub_distrib]
  refine DegLT.sum _ fun j hj => ?_
  rw [← map_sub]
  exact ((degLT_sub_tPow σ φ hφ k j).rsmul _).mono (by simp at hj; omega)

/-! ### Leading terms of `ψ ⋆ S` -/

theorem skewMul_apply (p q : ℕ →₀ B) {D : ℕ} (hq : DegLT q (D + 1)) (l : ℕ) :
    skewMul σ p q l = ∑ j ∈ Finset.range (D + 1), tPow σ j p l * q j := by
  rw [skewMul_eq_sum_range σ _ _ hq, Finsupp.finsetSum_apply]
  simp

/-- If `deg ψ ≤ e` and `S` is monic of degree `D`, the coefficient of `ψ ⋆ S` in degree
`e + D` is `σ^D(ψ_e)` and nothing lies above. -/
theorem skewMul_top (ψ S : ℕ →₀ B) {D e : ℕ} (hS : MonicDeg S D) (hψ : DegLT ψ (e + 1)) :
    skewMul σ ψ S (e + D) = σ^[D] (ψ e) ∧ DegLT (skewMul σ ψ S) (e + D + 1) := by
  have hcoef : ∀ l j, e + D ≤ l → j < D + 1 → tPow σ j ψ l * S j =
      if l = e + D ∧ j = D then σ^[D] (ψ e) else 0 := by
    intro l j hl hj
    by_cases hlj : j ≤ l
    · obtain ⟨m, rfl⟩ : ∃ m, l = m + j := ⟨l - j, by omega⟩
      rw [tPow_add_apply]
      by_cases hm : m ≤ e
      · have hjD : j = D := by omega
        subst hjD
        have hme : m = e := by omega
        subst hme
        simp [hS.1]
      · rw [hψ m (by omega)]
        simp only [iterate_map_zero, zero_mul]
        exact (ite_eq_right_iff.mpr fun h => absurd h (by omega)).symm
    · rw [tPow_apply_of_lt σ j ψ (by omega), zero_mul]
      exact (ite_eq_right_iff.mpr fun h => absurd h (by omega)).symm
  refine ⟨?_, fun l hl => ?_⟩
  · rw [skewMul_apply σ _ _ hS.2, Finset.sum_congr rfl fun j hj =>
      hcoef (e + D) j le_rfl (Finset.mem_range.mp hj)]
    simp
  · rw [skewMul_apply σ _ _ hS.2, Finset.sum_congr rfl fun j hj =>
      hcoef l j (by omega) (Finset.mem_range.mp hj)]
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_zero]
    intro j hj
    simp at hj
    omega

/-- **Monic quotient.** If `G = ψ ⋆ S + h` with `S` monic of degree `D`, `deg h < D` and `G`
monic of degree `n`, then `ψ = 0` when `n < D`, and `ψ` is monic of degree `n − D` when
`D ≤ n` (the ordered right-division identity (11) ⇒ (12)). -/
theorem monic_quotient (hσ : Function.Injective σ) {ψ S h G : ℕ →₀ B} {D n : ℕ}
    (hS : MonicDeg S D) (hh : DegLT h D) (hG : MonicDeg G n) (hGeq : G = skewMul σ ψ S + h) :
    (n < D → ψ = 0) ∧ (D ≤ n → MonicDeg ψ (n - D)) := by
  by_cases hψ : ψ = 0
  · refine ⟨fun _ => hψ, fun hn => ⟨?_, by rw [hψ]; exact DegLT.zero _⟩⟩
    have h1 := hG.1
    rw [hGeq, hψ] at h1
    simp only [Finsupp.add_apply, hh n hn, add_zero] at h1
    rw [skewMul_apply σ _ _ hS.2] at h1
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero] at h1
    rw [hψ, Finsupp.coe_zero, Pi.zero_apply]
    exact h1
  -- the top degree `e` of `ψ`
  have hne : ψ.support.Nonempty := Finsupp.support_nonempty_iff.mpr hψ
  set e := ψ.support.max' hne with he
  have hψe : ψ e ≠ 0 := Finsupp.mem_support_iff.mp (ψ.support.max'_mem hne)
  have hdeg : DegLT ψ (e + 1) := by
    intro l hl
    by_contra hl'
    have := ψ.support.le_max' l (Finsupp.mem_support_iff.mpr hl')
    omega
  obtain ⟨htop, habove⟩ := skewMul_top σ ψ S hS hdeg
  have hGat : ∀ l, D ≤ l → G l = skewMul σ ψ S l := by
    intro l hl
    rw [hGeq, Finsupp.add_apply, hh l hl, add_zero]
  -- `e + D ≤ n`
  have hle : e + D ≤ n := by
    by_contra hlt
    have h0 := hG.2 (e + D) (by omega)
    rw [hGat _ (by omega), htop] at h0
    exact hψe (Function.Injective.iterate hσ D (by rw [h0, iterate_map_zero]))
  -- `n ≤ e + D`
  have hge : n ≤ e + D := by
    by_contra hlt
    have h1 := hG.1
    rw [hGat _ (by omega), habove n (by omega)] at h1
    exact hψe (by rw [← one_mul (ψ e), ← h1, zero_mul])
  have hn : n = e + D := le_antisymm hge hle
  refine ⟨fun hlt => by omega, fun _ => ⟨?_, ?_⟩⟩
  · have h1 := hG.1
    rw [hGat _ (by omega), hn, htop] at h1
    have hn' : n - D = e := by omega
    rw [hn']
    exact Function.Injective.iterate hσ D (by rw [h1, iterate_map_one])
  · rw [show n - D + 1 = e + 1 by omega]
    exact hdeg

/-! ### The division theorem -/

theorem lsmul_rsmul (c b : B) (p : ℕ →₀ B) : lsmul c (rsmul b p) = rsmul b (lsmul c p) := by
  ext l; simp [mul_assoc]

theorem lsmul_tShift {c : B} (hc : σ c = c) (p : ℕ →₀ B) :
    lsmul c (tShift σ p) = tShift σ (lsmul c p) := by
  ext l
  rcases l with _ | l
  · simp
  · simp [hc]

theorem lsmul_tPow {c : B} (hc : σ c = c) (j : ℕ) (p : ℕ →₀ B) :
    lsmul c (tPow σ j p) = tPow σ j (lsmul c p) := by
  induction j with
  | zero => simp
  | succ j ih => rw [tPow_succ, lsmul_tShift σ hc, ih, tPow_succ]

theorem lsmul_skewMul {c : B} (hc : σ c = c) (p q : ℕ →₀ B) :
    lsmul c (skewMul σ p q) = skewMul σ (lsmul c p) q := by
  unfold skewMul Finsupp.sum
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [lsmul_rsmul, lsmul_tPow σ hc]

theorem lsmul_mul (c d : B) (p : ℕ →₀ B) : lsmul c (lsmul d p) = lsmul (c * d) p := by
  ext l; simp [mul_assoc]

theorem lsmul_one (p : ℕ →₀ B) : lsmul 1 p = p := by ext l; simp

theorem monicDeg_tPow {F : ℕ →₀ B} {N : ℕ} (hF : MonicDeg F N) (k : ℕ) :
    MonicDeg (tPow σ k F) (N + k) := by
  refine ⟨by rw [tPow_add_apply, hF.1, iterate_map_one], fun l hl => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, l = m + k := ⟨l - k, by omega⟩
  rw [tPow_add_apply, hF.2 m (by omega), iterate_map_zero]

/-- **Boundary division** (`DeformedBoundaryDivision.md` §5, conclusion (12)). Let
`φ_k ∈ ⊕_l t^l B` satisfy the first-order recurrence `deg(φ_(k+1) − φ_k t) < 1` (8) and the
norm identity `Σ_(j ≤ D) φ_(k+j) b_j = c F t^k` (7), where `S = Σ_j t^j b_j` is monic of
degree `D`, `F` is monic of degree `N`, and `c` is a unit fixed by `σ`. Then `φ_k = 0` if
`N + k < D`, and `c⁻¹ φ_k` is monic of degree `N + k − D` if `D ≤ N + k`. -/
theorem boundary_division (hσ : Function.Injective σ) (φ : ℕ → ℕ →₀ B)
    (hφ : ∀ k, DegLT (φ (k + 1) - tShift σ (φ k)) 1) {S F : ℕ →₀ B} {D N : ℕ}
    (hS : MonicDeg S D) (hF : MonicDeg F N) (c : Bˣ) (hc : σ c = c)
    (hnorm : ∀ k, ∑ j ∈ Finset.range (D + 1), rsmul (S j) (φ (k + j)) =
      lsmul (c : B) (tPow σ k F)) (k : ℕ) :
    (N + k < D → φ k = 0) ∧ (D ≤ N + k → MonicDeg (lsmul (↑c⁻¹ : B) (φ k)) (N + k - D)) := by
  have hc' : σ (↑c⁻¹ : B) = ↑c⁻¹ := by
    rw [← mul_one (σ (↑c⁻¹ : B)), ← c.mul_inv, ← mul_assoc, ← hc, ← map_mul, c.inv_mul,
      map_one, one_mul]
  set h := (∑ j ∈ Finset.range (D + 1), rsmul (S j) (φ (k + j))) - skewMul σ (φ k) S
  have hh : DegLT h D := degLT_norm_sub_skewMul σ φ hφ S hS.2 k
  have hG : tPow σ k F = skewMul σ (lsmul (↑c⁻¹ : B) (φ k)) S + lsmul (↑c⁻¹ : B) h := by
    have : lsmul (↑c⁻¹ : B) (lsmul (c : B) (tPow σ k F)) = tPow σ k F := by
      rw [lsmul_mul, c.inv_mul, lsmul_one]
    rw [← this, ← hnorm k, ← lsmul_skewMul σ hc', ← map_add]
    congr 1
    simp [h]
  obtain ⟨hlt, hge⟩ := monic_quotient σ hσ hS (hh.lsmul _) (monicDeg_tPow σ hF k) hG
  refine ⟨fun hk => ?_, hge⟩
  have h0 := hlt hk
  have : φ k = lsmul (c : B) (lsmul (↑c⁻¹ : B) (φ k)) := by
    rw [lsmul_mul, c.mul_inv, lsmul_one]
  rw [this, h0, map_zero]

end OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial
