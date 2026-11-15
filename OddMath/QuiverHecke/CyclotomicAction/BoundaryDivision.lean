import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Boundary division

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
end

end

section

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
end

end

section

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
end

end

section

/-!
# The Mackey boundary from the short-coset decomposition

`MackeyBoundary` (`BoundaryAssembly.lean`) takes the extraction `B₁` and the boundary `A_∂`
as data. In `docs/Nondegeneracy/DeformedMackeyBoundary.md` §§2–3 and
`docs/Nondegeneracy/DeformedCyclotomicTopRow.md` both are *derived*: the source `L₁` is the
sum of the short span `L₁'` and the compatible lifts `ℓ(w_k b)`, the lifts are independent
modulo `L₁'`, and `C₀ P(L₁') = 0`. Then `B₁` is the coordinate of `z` along the lifts modulo
`L₁'`, `C₀` is the polynomial component of the decomposition `L₀ = F(L₀') ⊕ j(V₀)`, and
`A_∂ = C₀ P ℓ`.

`MackeyCosets` records exactly these claims:

* the target decomposition `L₀ = F(L₀') ⊕ j(V₀)` (`direct`, `span`), the dot slides
  (`Rt_F`, `Rt_j`) and `P ρ = R_t P` (`P_ρ`), as in `MackeyBoundary`;
* the short subgroup `L₁'` with `ρ(L₁') ⊆ L₁'` (`ρ_short`) and `C₀ P(L₁') = 0` (`P_short`);
* the lift `ℓ : V₁ → L₁`, covering `L₁` modulo `L₁'` (`cover`), independent modulo `L₁'`
  (`ℓ_short`), with `ρ ℓ ≡ ℓ ρ̄` (`ρ_ℓ`) and right `B`-linear modulo `L₁'` (`ℓ_r`);
* right `B`-actions on `L₁` and `L₀` with `P` right linear (`P_r`), `F(L₀')` stable
  (`F_r`) and `j` right linear (`j_r`).

`MackeyCosets.toMackeyBoundary` builds the `MackeyBoundary`; `MackeyCosets.B₁_ℓ` and
`MackeyCosets.A_apply` identify its `B₁` and `A_∂`. `MackeyCosets.norm_of_short` restates the
norm hypothesis `hz₁` as `z₀ ≡ ℓ(S) mod L₁'`, the form in which the reverse norm identity (5)
of `DeformedBoundaryDivision.md` is proved.
-/

noncomputable section
open Finsupp
namespace OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

variable {B : Type*} [Ring B] (σ : B →+* B)

/-- The short-coset form of the first-order Mackey boundary. -/
structure MackeyCosets (L₁ L₀ L₀' : Type*) [AddCommGroup L₁] [AddCommGroup L₀]
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
  /-- The short span `L₁'`. -/
  short : AddSubgroup L₁
  /-- The compatible lifts `ℓ(w_k b)`. -/
  ℓ : (ℕ →₀ B) →+ L₁
  /-- The right `B`-action on the source. -/
  r₁ : B → L₁ →+ L₁
  /-- The right `B`-action on the target. -/
  r₀ : B → L₀ →+ L₀
  P_ρ : ∀ z, P (ρ z) = Rt (P z)
  Rt_F : ∀ u, Rt (F u) = F (X u) + j (single 0 (E u))
  Rt_j : ∀ f, Rt (j f) = j (tShift σ f)
  direct : ∀ u f, F u + j f = 0 → u = 0 ∧ f = 0
  span : ∀ y, ∃ u f, y = F u + j f
  ρ_short : ∀ z ∈ short, ρ z ∈ short
  P_short : ∀ z ∈ short, ∃ u, P z = F u
  cover : ∀ z, ∃ v, z - ℓ v ∈ short
  ℓ_short : ∀ v, ℓ v ∈ short → v = 0
  ρ_ℓ : ∀ v, ρ (ℓ v) - ℓ (tShift σ v) ∈ short
  ℓ_r : ∀ (b : B) v, ℓ (rsmul b v) - r₁ b (ℓ v) ∈ short
  P_r : ∀ (b : B) z, P (r₁ b z) = r₀ b (P z)
  F_r : ∀ (b : B) u, ∃ u', r₀ b (F u) = F u'
  j_r : ∀ (b : B) f, r₀ b (j f) = j (rsmul b f)

namespace MackeyCosets

variable {σ} {L₁ L₀ L₀' : Type*} [AddCommGroup L₁] [AddCommGroup L₀] [AddCommGroup L₀']
  (M : MackeyCosets σ L₁ L₀ L₀')

theorem eq_of_direct {u u' : L₀'} {f f' : ℕ →₀ B} (h : M.F u + M.j f = M.F u' + M.j f') :
    u = u' ∧ f = f' := by
  have := M.direct (u - u') (f - f') (by
    rw [map_sub, map_sub, sub_add_sub_comm, h, sub_self])
  exact ⟨sub_eq_zero.mp this.1, sub_eq_zero.mp this.2⟩

theorem eq_of_short {v v' : ℕ →₀ B} {z : L₁} (h : z - M.ℓ v ∈ M.short)
    (h' : z - M.ℓ v' ∈ M.short) : v = v' := by
  have : M.ℓ (v' - v) ∈ M.short := by
    rw [map_sub, show M.ℓ v' - M.ℓ v = (z - M.ℓ v) - (z - M.ℓ v') by abel]
    exact M.short.sub_mem h h'
  exact (sub_eq_zero.mp (M.ℓ_short _ this)).symm

/-- The polynomial component `C₀ : L₀ → V₀` of `L₀ = F(L₀') ⊕ j(V₀)`. -/
def C₀ : L₀ →+ (ℕ →₀ B) where
  toFun y := Classical.choose (Classical.choose_spec (M.span y))
  map_zero' := by
    have h := Classical.choose_spec (Classical.choose_spec (M.span 0))
    exact ((M.eq_of_direct (u' := 0) (f' := 0) (by rw [← h, map_zero, map_zero, add_zero])).2)
  map_add' y y' := by
    have h := Classical.choose_spec (Classical.choose_spec (M.span (y + y')))
    have h₁ := Classical.choose_spec (Classical.choose_spec (M.span y))
    have h₂ := Classical.choose_spec (Classical.choose_spec (M.span y'))
    refine (M.eq_of_direct (u' := Classical.choose (M.span y) + Classical.choose (M.span y'))
      (h.symm.trans ?_)).2
    rw [map_add, map_add]
    nth_rw 1 [h₁, h₂]
    abel

theorem exists_eq_F_add_j_C₀ (y : L₀) : ∃ u, y = M.F u + M.j (M.C₀ y) :=
  ⟨_, Classical.choose_spec (Classical.choose_spec (M.span y))⟩

theorem C₀_eq {y : L₀} {u : L₀'} {f : ℕ →₀ B} (h : y = M.F u + M.j f) : M.C₀ y = f := by
  obtain ⟨u', hu'⟩ := M.exists_eq_F_add_j_C₀ y
  exact (M.eq_of_direct (hu'.symm.trans h)).2

theorem C₀_P_short {z : L₁} (hz : z ∈ M.short) : M.C₀ (M.P z) = 0 := by
  obtain ⟨u, hu⟩ := M.P_short z hz
  exact M.C₀_eq (u := u) (f := 0) (by rw [hu, map_zero, add_zero])

/-- The extraction `B₁`: the coordinate of `z` along the lifts, modulo `L₁'`. -/
def B₁ : L₁ →+ (ℕ →₀ B) where
  toFun z := Classical.choose (M.cover z)
  map_zero' := M.eq_of_short (Classical.choose_spec (M.cover 0))
    (by rw [map_zero, sub_zero]; exact M.short.zero_mem)
  map_add' z z' := M.eq_of_short (Classical.choose_spec (M.cover (z + z'))) (by
    rw [map_add, show z + z' - (M.ℓ (Classical.choose (M.cover z)) +
        M.ℓ (Classical.choose (M.cover z'))) = (z - M.ℓ (Classical.choose (M.cover z))) +
        (z' - M.ℓ (Classical.choose (M.cover z'))) by abel]
    exact M.short.add_mem (Classical.choose_spec (M.cover z))
      (Classical.choose_spec (M.cover z')))

theorem sub_ℓ_B₁_mem (z : L₁) : z - M.ℓ (M.B₁ z) ∈ M.short :=
  Classical.choose_spec (M.cover z)

theorem B₁_eq {z : L₁} {v : ℕ →₀ B} (h : z - M.ℓ v ∈ M.short) : M.B₁ z = v :=
  M.eq_of_short (M.sub_ℓ_B₁_mem z) h

theorem B₁_ℓ (v : ℕ →₀ B) : M.B₁ (M.ℓ v) = v :=
  M.B₁_eq (by rw [sub_self]; exact M.short.zero_mem)

/-- The boundary `A_∂ = C₀ P ℓ`. -/
def A : (ℕ →₀ B) →+ (ℕ →₀ B) := M.C₀.comp (M.P.comp M.ℓ)

theorem A_apply (v : ℕ →₀ B) : M.A v = M.C₀ (M.P (M.ℓ v)) := rfl

theorem B₁_ρ (z : L₁) : M.B₁ (M.ρ z) = tShift σ (M.B₁ z) := by
  refine M.B₁_eq ?_
  rw [show M.ρ z - M.ℓ (tShift σ (M.B₁ z)) = M.ρ (z - M.ℓ (M.B₁ z)) +
      (M.ρ (M.ℓ (M.B₁ z)) - M.ℓ (tShift σ (M.B₁ z))) by rw [map_sub]; abel]
  exact M.short.add_mem (M.ρ_short _ (M.sub_ℓ_B₁_mem z)) (M.ρ_ℓ _)

theorem P_split (z : L₁) : ∃ u, M.P z = M.F u + M.j (M.A (M.B₁ z)) := by
  obtain ⟨u, hu⟩ := M.exists_eq_F_add_j_C₀ (M.P (M.ℓ (M.B₁ z)))
  obtain ⟨u', hu'⟩ := M.P_short _ (M.sub_ℓ_B₁_mem z)
  refine ⟨u + u', ?_⟩
  rw [A_apply, map_add, add_right_comm, ← hu, ← hu', ← map_add, add_sub_cancel]

theorem A_rsmul (b : B) (v : ℕ →₀ B) : M.A (rsmul b v) = rsmul b (M.A v) := by
  obtain ⟨u, hu⟩ := M.exists_eq_F_add_j_C₀ (M.P (M.ℓ v))
  obtain ⟨u', hu'⟩ := M.F_r b u
  rw [A_apply, show M.ℓ (rsmul b v) = M.r₁ b (M.ℓ v) + (M.ℓ (rsmul b v) - M.r₁ b (M.ℓ v)) by
      abel, map_add, map_add, M.C₀_P_short (M.ℓ_r b v), add_zero]
  refine M.C₀_eq (u := u') ?_
  rw [M.P_r, hu, map_add, hu', M.j_r, A_apply]

/-- The `MackeyBoundary` of the short-coset decomposition. -/
def toMackeyBoundary : MackeyBoundary σ L₁ L₀ L₀' where
  P := M.P
  ρ := M.ρ
  Rt := M.Rt
  F := M.F
  j := M.j
  X := M.X
  E := M.E
  B₁ := M.B₁
  A := M.A
  P_ρ := M.P_ρ
  Rt_F := M.Rt_F
  Rt_j := M.Rt_j
  direct := M.direct
  B₁_ρ := M.B₁_ρ
  B₁_surjective v := ⟨M.ℓ v, M.B₁_ℓ v⟩
  P_split := M.P_split
  A_rsmul := M.A_rsmul

@[simp] theorem toMackeyBoundary_A : M.toMackeyBoundary.A = M.A := rfl

@[simp] theorem toMackeyBoundary_B₁ : M.toMackeyBoundary.B₁ = M.B₁ := rfl

end MackeyCosets

end OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial
end

end
