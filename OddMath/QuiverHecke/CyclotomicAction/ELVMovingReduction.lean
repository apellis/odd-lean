/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMonicAnnihilator
import OddMath.QuiverHecke.CyclotomicAction.ELVMonicOldCoefficients

/-! # Bounded moving powers in the full ELV cyclotomic quotient

The actual monic annihilator and its explicitly old coefficients give a bounded
last-dot spanning result at every old word. The recurrence multiplies on the
right and never commutes arbitrary old coefficients across an odd dot. This
is the moving-exponent input for content induction; the all-content integer
support bound still requires finite-shuffle spanning and homogeneous projection.
-/

noncomputable section
open CategoryTheory Polynomial

namespace OddMath.QuiverHecke.ELVOld

private theorem powers_mem_ideal_sup_span
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (J : Submodule R A) (B : Subring A) (x : A) (p : Polynomial A)
    (hm : p.Monic) (hc : ∀ r, p.coeff r ∈ B)
    (he : p.eval₂ (RingHom.id A) x ∈ J)
    (hl : ∀ a b, b ∈ J → a * b ∈ J)
    (hr : ∀ a b, a ∈ J → a * b ∈ J) (n : ℕ) :
    x ^ n ∈ J ⊔ Submodule.span R {z | ∃ a ∈ B, ∃ j < p.natDegree, z = a * x ^ j} := by
  let S := Submodule.span R {z | ∃ a ∈ B, ∃ j < p.natDegree, z = a * x ^ j}
  have hleft (a : A) (ha : a ∈ B) (z : A) (hz : z ∈ S) : a * z ∈ S := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb, j, hj, rfl⟩ := hz
      exact Submodule.subset_span ⟨a * b, B.mul_mem ha hb, j, hj, (mul_assoc _ _ _).symm⟩
    | zero => simp
    | add b c _ _ hb hc => simpa only [mul_add] using S.add_mem hb hc
    | smul r b _ hb => simpa only [mul_smul_comm] using S.smul_mem r hb
  have hleft' (a : A) (ha : a ∈ B) (z : A) (hz : z ∈ J ⊔ S) : a * z ∈ J ⊔ S := by
    obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp hz
    rw [mul_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hl a b hb))
      (Submodule.mem_sup_right (hleft a ha c hc))
  change x ^ n ∈ J ⊔ S
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < p.natDegree
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨1, B.one_mem, n, hn, by simp⟩)
    · have hN : p.natDegree ≤ n := Nat.le_of_not_gt hn
      have hrec : p.eval₂ (RingHom.id A) x =
          (∑ r ∈ Finset.range p.natDegree, p.coeff r * x ^ r) + x ^ p.natDegree := by
        rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ]
        simp only [RingHom.id_apply, hm.coeff_natDegree, one_mul]
      have heq : x ^ n = p.eval₂ (RingHom.id A) x * x ^ (n - p.natDegree) -
          ∑ r ∈ Finset.range p.natDegree, p.coeff r * x ^ (r + (n - p.natDegree)) := by
        rw [hrec, add_mul, Finset.sum_mul]
        simp only [mul_assoc, ← pow_add, Nat.add_sub_of_le hN, add_sub_cancel_left]
      rw [heq]
      apply Submodule.sub_mem
      · exact Submodule.mem_sup_left (hr _ _ he)
      · apply Submodule.sum_mem
        intro r hr
        exact hleft' _ (hc r) _ (ih (r + (n - p.natDegree))
          (by have := Finset.mem_range.mp hr; omega))

universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Every power of the moving dot reduces, in the full cyclotomic quotient,
 to powers strictly below the concrete monic endpoint degree with old coefficients
 on the left. No commutation between those coefficients and the moving dot is used. -/
theorem movingDot_pow_mem_bounded_old_span (i : I) (v : List I) (n : ℕ) :
    (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
      ((affineUnitEndHom D Sc cutoff (v ++ [i])
        (dotE D Sc (v ++ [i]) v.length)) ^ n) ∈
    Submodule.span k {z | ∃ a : End (obj D Sc cutoff v),
      ∃ j < (monicELVEndpointProduct D Sc cutoff i v).natDegree,
        z = (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
          (rightContextEndHom D Sc cutoff i v a *
            (affineUnitEndHom D Sc cutoff (v ++ [i])
              (dotE D Sc (v ++ [i]) v.length)) ^ j)} := by
  let J := ideal D Sc cutoff (v ++ [i]) (v ++ [i])
  let x := affineUnitEndHom D Sc cutoff (v ++ [i])
    (dotE D Sc (v ++ [i]) v.length)
  let p := monicELVEndpointProduct D Sc cutoff i v
  let B := (rightContextEndHom D Sc cutoff i v).range
  have h := powers_mem_ideal_sup_span J B x p
    (monicELVEndpointProduct_monic D Sc cutoff i v)
    (monicELVEndpointProduct_coeff_mem_range D Sc cutoff i v)
    (monicELVEndpointProduct_eval_mem_ideal D Sc cutoff i v)
    (fun a b hb => ideal_comp D Sc cutoff hb a)
    (fun a b ha => comp_ideal D Sc cutoff b ha) n
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
  have hqa : (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ a = 0 :=
    (Submodule.Quotient.mk_eq_zero J).mpr ha
  rw [← hab, map_add, hqa, zero_add]
  clear hab
  induction hb using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, j, hj, rfl⟩ := hz
    obtain ⟨d, rfl⟩ := hc
    exact Submodule.subset_span ⟨d, j, hj, rfl⟩
  | zero => simp
  | add b c _ _ hb hc => simpa only [map_add] using Submodule.add_mem _ hb hc
  | smul r b _ hb => simpa only [map_smul] using Submodule.smul_mem _ r hb


end OddMath.QuiverHecke.ELVOld
