/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BWWScalars

/-!
# Sums over the coefficient box of Brundan–Wang–Webster parameters

J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.2, compared with J. Brundan,
A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, (1.3), (1.4).

The polynomial `Qᵢⱼ(u, v)` of parameters `Sc : BWWScalars D k` is a sum over the box
`[0, dᵢⱼ] × [0, dⱼᵢ]`. For `dᵢⱼ ≠ 0` this file splits such a sum into the two corners
`tᵢⱼ u^{dᵢⱼ}`, `tⱼᵢ v^{dⱼᵢ}`, the pure monomials (`p = 0` or `q = 0` below the corners) and
the interior monomials of Brundan–Ellis.

* `BWWScalars.sum_box_eq`: the decomposition for arbitrary parameters.
* `BWWScalars.NoPure`: the boxes without pure monomials, i.e. the Brundan–Ellis parameters
  (`NoPure.toScalars`, `ScalarData.NoPure.toBWW`); homogeneous parameters have no pure
  monomials (`Homogeneous.noPure`).
* `sum_box_toBWW`: the box sum of `Sc.toBWW` is the two corners plus the sum over
  `[0, dᵢⱼ) × [0, dⱼᵢ)`.
-/

noncomputable section

namespace OddMath.SKM

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
variable {k : Type w} [CommRing k]

/-- Splitting `range (a + 1)` into `0`, the open interval and `a`. -/
theorem sum_range_succ_eq {M : Type*} [AddCommMonoid M] {a : ℕ} (ha : 0 < a) (g : ℕ → M) :
    ∑ p ∈ Finset.range (a + 1), g p = g a + (g 0 + ∑ p ∈ Finset.Ioo 0 a, g p) := by
  rw [Finset.sum_range_succ, add_comm, Finset.range_eq_Ico, ← Finset.Ioo_insert_left ha,
    Finset.sum_insert (by simp)]

theorem dn_pos_of_d_ne_zero {i j : I} (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    0 < D.dn i j ∧ 0 < D.dn j i := by
  have h1 := D.d_nonneg hij
  have h1' := D.d_nonneg (Ne.symm hij)
  have h2 := (D.d_eq_zero_iff i j).not.mp hd
  unfold Datum.dn
  omega

namespace BWWScalars

/-- Parameters without pure monomials: `c i j p q = 0` whenever `p < dᵢⱼ`, `q < dⱼᵢ` and
`p = 0` or `q = 0`. This is the shape of the Brundan–Ellis polynomials (1.4). -/
def NoPure (Sc : BWWScalars D k) : Prop :=
  ∀ i j (p q : ℕ), i ≠ j → p < D.dn i j → q < D.dn j i → (p = 0 ∨ q = 0) → Sc.c i j p q = 0

/-- Homogeneous parameters have no pure monomials. -/
theorem Homogeneous.noPure {Sc : BWWScalars D k} (hh : Sc.Homogeneous) : Sc.NoPure := by
  intro i j p q hij hp hq hpq
  have hdn : (D.dn i j : ℤ) = D.d i j := D.dn_cast hij
  have hdn' : (D.dn j i : ℤ) = D.d j i := D.dn_cast (Ne.symm hij)
  exact hh.c_eq_zero hij (by omega) (by omega) hpq

/-- The underlying parameters have no pure monomials exactly when the box has none. -/
theorem NoPure.toScalars {Sc : BWWScalars D k} (hn : Sc.NoPure) : Sc.toScalars.NoPure := hn

/-- **The box decomposition.** For `dᵢⱼ ≠ 0`, a sum over the box `[0, dᵢⱼ] × [0, dⱼᵢ]` is the
two corners, the pure monomials `u^p` (`p < dᵢⱼ`) and `v^q` (`0 < q < dⱼᵢ`), and the interior. -/
theorem sum_box_eq {M : Type*} [AddCommGroup M] [Module k M] (Sc : BWWScalars D k)
    {i j : I} (hij : i ≠ j) (hd : D.d i j ≠ 0) (f : ℕ → ℕ → M) :
    ∑ p ∈ Finset.range (D.dn i j + 1), ∑ q ∈ Finset.range (D.dn j i + 1), Sc.c i j p q • f p q =
      (Sc.t i j : k) • f (D.dn i j) 0 + (Sc.t j i : k) • f 0 (D.dn j i) +
        (∑ p ∈ Finset.range (D.dn i j), Sc.c i j p 0 • f p 0 +
          ∑ q ∈ Finset.Ioo 0 (D.dn j i), Sc.c i j 0 q • f 0 q) +
        ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), Sc.c i j p q • f p q := by
  obtain ⟨ha, hb⟩ := dn_pos_of_d_ne_zero hij hd
  have hR : ∀ p ∈ Finset.Ioo 0 (D.dn i j),
      Sc.c i j p (D.dn j i) • f p (D.dn j i) + (Sc.c i j p 0 • f p 0 +
        ∑ q ∈ Finset.Ioo 0 (D.dn j i), Sc.c i j p q • f p q) =
      Sc.c i j p 0 • f p 0 + ∑ q ∈ Finset.Ioo 0 (D.dn j i), Sc.c i j p q • f p q := by
    intro p hp
    rw [Sc.c_right i j (Finset.mem_Ioo.mp hp).1, zero_smul, zero_add]
  have hT : ∑ q ∈ Finset.Ioo 0 (D.dn j i), Sc.c i j (D.dn i j) q • f (D.dn i j) q = 0 :=
    Finset.sum_eq_zero fun q hq => by rw [Sc.c_top i j _ (Finset.mem_Ioo.mp hq).1, zero_smul]
  rw [sum_range_succ_eq ha]
  simp only [sum_range_succ_eq hb]
  rw [Finset.sum_congr rfl hR, Finset.sum_add_distrib, hT, Sc.c_top i j _ hb,
    Sc.c_corner i j hij, Sc.c_corner' hij, Finset.range_eq_Ico, ← Finset.Ioo_insert_left ha,
    Finset.sum_insert (by simp)]
  simp only [zero_smul, zero_add, add_zero]
  abel

end BWWScalars

namespace ScalarData

/-- Parameters without pure monomials give a box without pure monomials. -/
theorem NoPure.toBWW {Sc : Scalars D k} (hn : Sc.NoPure) : Sc.toBWW.NoPure :=
  fun _ _ _ _ hij hp hq hpq => by rw [Sc.toBWW_c_of_lt hij hp hq]; exact hn _ _ _ _ hij hp hq hpq

end ScalarData

/-- For `dᵢⱼ ≠ 0`, a sum over the box of `Sc.toBWW` is the two corner terms plus the sum over
`[0, dᵢⱼ) × [0, dⱼᵢ)` with the scalars `sᵢⱼ^{pq}`. -/
theorem sum_box_toBWW {M : Type*} [AddCommGroup M] [Module k M] (Sc : Scalars D k)
    {i j : I} (hij : i ≠ j) (hd : D.d i j ≠ 0) (f : ℕ → ℕ → M) :
    ∑ p ∈ Finset.range (D.dn i j + 1), ∑ q ∈ Finset.range (D.dn j i + 1),
        Sc.toBWW.c i j p q • f p q =
      (Sc.t i j : k) • f (D.dn i j) 0 + (Sc.t j i : k) • f 0 (D.dn j i) +
        ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i), Sc.s i j p q • f p q := by
  obtain ⟨ha, hb⟩ := dn_pos_of_d_ne_zero hij hd
  rw [BWWScalars.sum_box_eq Sc.toBWW hij hd, sum_range_range_eq_edges_add ha hb]
  have e1 : ∑ p ∈ Finset.range (D.dn i j), Sc.toBWW.c i j p 0 • f p 0 =
      ∑ p ∈ Finset.range (D.dn i j), Sc.s i j p 0 • f p 0 :=
    Finset.sum_congr rfl fun p hp => by
      rw [Sc.toBWW_c_of_lt hij (Finset.mem_range.mp hp) hb]
  have e2 : ∑ q ∈ Finset.Ioo 0 (D.dn j i), Sc.toBWW.c i j 0 q • f 0 q =
      ∑ q ∈ Finset.Ioo 0 (D.dn j i), Sc.s i j 0 q • f 0 q :=
    Finset.sum_congr rfl fun q hq => by
      rw [Sc.toBWW_c_of_lt hij ha (Finset.mem_Ioo.mp hq).2]
  have e3 : ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
      Sc.toBWW.c i j p q • f p q =
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), Sc.s i j p q • f p q :=
    Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => by
      rw [Sc.toBWW_c_of_lt hij (Finset.mem_Ioo.mp hp).2 (Finset.mem_Ioo.mp hq).2]
  rw [e1, e2, e3, ScalarData.toBWW_t]
  abel

end OddMath.SKM
