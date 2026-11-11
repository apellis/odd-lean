/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Basic

/-!
# Pure monomials of the polynomials `Qᵢⱼ`

The scalars `sᵢⱼ^{pq}` enter the polynomials `Qᵢⱼ(u, v)` of Brundan–Ellis (1.4) for
`0 ≤ p < dᵢⱼ`, `0 ≤ q < dⱼᵢ`. Brundan–Ellis (arXiv:1701.04133v2, §1) use only the interior
monomials `0 < p`, `0 < q`; the monomials with `p = 0` or `q = 0` (the *pure* monomials) are the
generalization of Brundan–Wang–Webster. The condition `ScalarData.NoPure` says that they vanish;
under it every double sum over the box `[0, dᵢⱼ) × [0, dⱼᵢ)` is the double sum over the interior
`(0, dᵢⱼ) × (0, dⱼᵢ)`, which recovers the printed relations of Brundan–Ellis.

## Main results

* `sum_range_range_eq_sum_Ioo_Ioo`, `sum_range_range_eq_edges_add`: a box sum whose terms vanish on the two edges
  `p = 0`, `q = 0` is the interior sum.
* `ScalarData.NoPure`, `ScalarData.NoPure.sum_range_range`.
-/

namespace OddMath.SKM

universe u v

/-- A double sum over `[0, a) × [0, b)` whose terms vanish when `p = 0` or `q = 0` equals the
double sum over `(0, a) × (0, b)`. -/
theorem sum_range_range_eq_sum_Ioo_Ioo {M : Type*} [AddCommMonoid M] (a b : ℕ)
    (g : ℕ → ℕ → M) (hg : ∀ p q, p < a → q < b → (p = 0 ∨ q = 0) → g p q = 0) :
    ∑ p ∈ Finset.range a, ∑ q ∈ Finset.range b, g p q =
      ∑ p ∈ Finset.Ioo 0 a, ∑ q ∈ Finset.Ioo 0 b, g p q := by
  calc ∑ p ∈ Finset.range a, ∑ q ∈ Finset.range b, g p q
      = ∑ p ∈ Finset.range a, ∑ q ∈ Finset.Ioo 0 b, g p q := by
        refine Finset.sum_congr rfl fun p hp => (Finset.sum_subset ?_ ?_).symm
        · intro q hq
          rw [Finset.mem_Ioo] at hq
          rw [Finset.mem_range]
          omega
        · intro q hq hq'
          rw [Finset.mem_range] at hp hq
          rw [Finset.mem_Ioo] at hq'
          exact hg p q hp hq (Or.inr (by omega))
    _ = ∑ p ∈ Finset.Ioo 0 a, ∑ q ∈ Finset.Ioo 0 b, g p q := by
        refine (Finset.sum_subset ?_ ?_).symm
        · intro p hp
          rw [Finset.mem_Ioo] at hp
          rw [Finset.mem_range]
          omega
        · intro p hp hp'
          rw [Finset.mem_range] at hp
          rw [Finset.mem_Ioo] at hp'
          refine Finset.sum_eq_zero fun q hq => ?_
          rw [Finset.mem_Ioo] at hq
          exact hg p q hp (by omega) (Or.inl (by omega))

/-- A double sum over `[0, a) × [0, b)` with `a, b > 0` splits into the edge `q = 0`, the edge
`p = 0` (without the corner) and the interior. -/
theorem sum_range_range_eq_edges_add {M : Type*} [AddCommMonoid M] {a b : ℕ} (ha : 0 < a)
    (hb : 0 < b) (g : ℕ → ℕ → M) :
    ∑ p ∈ Finset.range a, ∑ q ∈ Finset.range b, g p q =
      (∑ p ∈ Finset.range a, g p 0 + ∑ q ∈ Finset.Ioo 0 b, g 0 q) +
        ∑ p ∈ Finset.Ioo 0 a, ∑ q ∈ Finset.Ioo 0 b, g p q := by
  have h0a : (0 : ℕ) ∉ Finset.Ioo 0 a := by simp
  have h0b : (0 : ℕ) ∉ Finset.Ioo 0 b := by simp
  have hra : Finset.range a = insert 0 (Finset.Ioo 0 a) := by
    rw [Finset.range_eq_Ico, Finset.Ioo_insert_left ha]
  have hrb : Finset.range b = insert 0 (Finset.Ioo 0 b) := by
    rw [Finset.range_eq_Ico, Finset.Ioo_insert_left hb]
  rw [hra, hrb]
  simp only [Finset.sum_insert h0a, Finset.sum_insert h0b, Finset.sum_add_distrib]
  abel

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type*} [CommRing k]
  {Ptwo : Prop}

/-- The pure monomials vanish: `sᵢⱼ^{pq} = 0` for `i ≠ j`, `p < dᵢⱼ`, `q < dⱼᵢ` and `p = 0` or
`q = 0`. These are the parameters of Brundan–Ellis (1.4). -/
def ScalarData.NoPure (Sc : ScalarData D k Ptwo) : Prop :=
  ∀ i j (p q : ℕ), i ≠ j → p < D.dn i j → q < D.dn j i → (p = 0 ∨ q = 0) → Sc.s i j p q = 0

/-- Without pure monomials, a box sum of terms that vanish with `sᵢⱼ^{pq}` is the interior
sum. -/
theorem ScalarData.NoPure.sum_range_range {Sc : ScalarData D k Ptwo} (hn : Sc.NoPure) {i j : I}
    (hij : i ≠ j) {M : Type*} [AddCommMonoid M] (g : ℕ → ℕ → M)
    (hg : ∀ p q, Sc.s i j p q = 0 → g p q = 0) :
    ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i), g p q =
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), g p q :=
  sum_range_range_eq_sum_Ioo_Ioo _ _ g fun p q hp hq h0 => hg p q (hn i j p q hij hp hq h0)

end OddMath.SKM
