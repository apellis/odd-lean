/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPolynomial
import OddMath.QuiverHecke.SwappedAssembly.SlideNe

/-! # Repeated-outer Q-polynomial correction

Algebraic support for the two sums in `ProbeReservoir.CrossBraid.braidEq_diag`.
The endomorphism product reverses chronological composition: the ordered term
`x^(b-1-a) * y^c * z^a` is `z^a ≫ y^c ≫ x^(b-1-a)`.
This module does not assume or prove a crossing braid relation.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly.RepeatedOuterQCorrection
open CategoryTheory OddMath.SKM Finset
open RepeatedOuterPolynomial

universe u
variable {k : Type u} {R : Type*} [CommRing k] [Ring R] [Algebra k R]

lemma supported_correction (A x z : R) (pi : ZMod 2)
    (hxz : x*z = zsign k pi • (z*x))
    (hA0 : pi = 0 → A*(x-z) = 1)
    (hA1 : pi = 1 → A*(x*x-z*z) = x-z)
    (n : ℕ) (hn : pi = 1 → Even n) :
    A*(x^n-z^n) = ∑ a ∈ range n,
      zsign k (pi*a) • (x^(n-1-a)*z^a) := by
  have hp : pi = 0 ∨ pi = 1 := by fin_cases pi <;> simp
  rcases hp with rfl | rfl
  · simpa only [zero_mul, zsign_zero, one_smul] using
      even_correction A x z (by simpa [Commute, SemiconjBy, zsign] using hxz) (hA0 rfl) n
  · obtain ⟨m, hm⟩ := hn rfl
    have he : n = 2*m := by omega
    rw [he]
    have hz (a : ℕ) : zsign k ((1 : ZMod 2)*a) = (-1:k)^a := by
      rw [zsign_natCast_mul]
      simp [zsign]
    simpa only [hz] using
      odd_correction_smul (k := k) A x z (by simpa [zsign] using hxz) (hA1 rfl) m

lemma supported_middle_commute (z y : R) (pi pj : ZMod 2)
    (hzy : z*y = zsign k (pi*pj) • (y*z))
    (c : ℕ) (hc : pj = 1 → Even c) : Commute z (y^c) := by
  fin_cases pi <;> fin_cases pj
  · exact (show Commute z y by simpa [Commute, SemiconjBy, zsign] using hzy).pow_right c
  · exact (show Commute z y by simpa [Commute, SemiconjBy, zsign] using hzy).pow_right c
  · exact (show Commute z y by simpa [Commute, SemiconjBy, zsign] using hzy).pow_right c
  · have hz : z*y = -(y*z) := by simpa [zsign] using hzy
    have hy : y*z = -(z*y) := by rw [hz, neg_neg]
    obtain ⟨m, hm⟩ := hc rfl
    have he : c = 2*m := by omega
    rw [he, pow_mul]
    exact ((square_commute y z hy).pow_left m).symm

lemma weighted_middle (A x y z : R) (pi pj : ZMod 2)
    (hxz : x*z = zsign k pi • (z*x))
    (hzy : z*y = zsign k (pi*pj) • (y*z))
    (hA0 : pi = 0 → A*(x-z) = 1)
    (hA1 : pi = 1 → A*(x*x-z*z) = x-z)
    (n c : ℕ) (hn : pi = 1 → Even n) (hc : pj = 1 → Even c) (w : k) :
    zsign k (pi*pj) • (A*(w • ((x^n-z^n)*y^c))) =
      ∑ a ∈ range n, (zsign k (pi*(pj+a))*w) • (x^(n-1-a)*y^c*z^a) := by
  rw [mul_smul_comm, ← mul_assoc, supported_correction A x z pi hxz hA0 hA1 n hn,
    sum_mul, smul_sum, smul_sum]
  apply sum_congr rfl
  intro a _
  have hm := (supported_middle_commute z y pi pj hzy c hc).pow_left a
  rw [smul_mul_assoc, mul_assoc, hm.eq, ← mul_assoc]
  simp only [smul_smul, mul_add, zsign_add]
  congr 1
  ring

variable {I X : Type u} [AddCommGroup X] {D : Datum I X} (Sc : Scalars D k)

lemma supported_outer_even (i j : I) (b c : ℕ) (hs : Sc.s i j b c ≠ 0)
    (hi : D.parity i = 1) : Even b := by
  apply Nat.not_odd_iff_even.mp
  intro ho
  apply hs
  apply Sc.s_eq_zero
  rw [hi, mul_one]
  exact ZMod.natCast_eq_one_iff_odd.mpr ho

lemma supported_inner_even (i j : I) (b c : ℕ) (hs : Sc.s i j b c ≠ 0)
    (hj : D.parity j = 1) : Even c := by
  apply supported_outer_even Sc j i c b _ hj
  rwa [← Sc.s_symm]

lemma outer_degree_even (i j : I) (hi : D.parity i = 1) : Even (D.dn i j) := by
  obtain ⟨m, hm⟩ := D.even_d_of_odd hi j
  have he : D.dn i j = m.toNat + m.toNat := by
    change (D.d i j).toNat = _
    rw [hm]
    omega
  exact ⟨m.toNat, he⟩

variable {C : Type*} [Category C] [Preadditive C] [Linear k C] {V : C}

/-- A disconnected polynomial has zero outer difference, with no denominator hypothesis. -/
lemma qExpr_disconnected_difference (x y z : End V) (i j : I) (hd : D.d i j = 0) :
    ProbeReservoir.qExpr Sc x y i j - ProbeReservoir.qExpr Sc z y i j = 0 := by
  simp [ProbeReservoir.qExpr, hd]

/-- Expansion of the outer difference for a connected pair. -/
lemma qExpr_difference (x y z : End V) (i j : I) (hd : D.d i j ≠ 0) :
    ProbeReservoir.qExpr Sc x y i j - ProbeReservoir.qExpr Sc z y i j =
      (Sc.t i j : k) • (x^(D.dn i j)-z^(D.dn i j)) +
        ∑ b ∈ Ioo 0 (D.dn i j), ∑ c ∈ Ioo 0 (D.dn j i),
          Sc.s i j b c • ((x^b-z^b)*y^c) := by
  simp only [ProbeReservoir.qExpr, hd, ite_false, sub_mul, smul_sub,
    sum_sub_distrib]
  abel

/-- The two literal coefficient sums of the repeated-outer diagonal correction.
Only the outer/right and middle/right signed dot relations are needed; no
commutativity of the endomorphism ring or braid relation is assumed. -/
theorem qExpr_correction (A x y z : End V) (i j : I)
    (hxz : x*z = zsign k (D.parity i) • (z*x))
    (hzy : z*y = zsign k (D.parity i*D.parity j) • (y*z))
    (hA0 : D.parity i = 0 → A*(x-z) = 1)
    (hA1 : D.parity i = 1 → A*(x*x-z*z) = x-z) :
    zsign k (D.parity i*D.parity j) •
        (A*(ProbeReservoir.qExpr Sc x y i j - ProbeReservoir.qExpr Sc z y i j)) =
      (∑ a ∈ range (D.dn i j),
        (zsign k (D.parity i*(D.parity j+a))*(Sc.t i j : k)) •
          (x^(D.dn i j-1-a)*z^a)) +
      ∑ b ∈ Ioo 0 (D.dn i j), ∑ c ∈ Ioo 0 (D.dn j i), ∑ a ∈ range b,
        (zsign k (D.parity i*(D.parity j+a))*Sc.s i j b c) •
          (x^(b-1-a)*y^c*z^a) := by
  classical
  by_cases hd : D.d i j = 0
  · simp [ProbeReservoir.qExpr, hd, Datum.dn]
  · rw [qExpr_difference Sc x y z i j hd, mul_add, smul_add]
    congr 1
    · simpa only [pow_zero, mul_one] using
        weighted_middle A x y z (D.parity i) (D.parity j) hxz hzy hA0 hA1
          (D.dn i j) 0 (outer_degree_even i j) (fun _ => ⟨0, rfl⟩) (Sc.t i j : k)
    · simp only [mul_sum, smul_sum]
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro c _
      by_cases hs : Sc.s i j b c = 0
      · simp [hs]
      · exact weighted_middle A x y z (D.parity i) (D.parity j) hxz hzy hA0 hA1
          b c (supported_outer_even Sc i j b c hs) (supported_inner_even Sc i j b c hs)
          (Sc.s i j b c)

omit [Preadditive C] [Linear k C] in
/-- Independently check the chronological order of the correction monomial. -/
lemma correction_order (x y z : End V) (a b c : ℕ) :
    x^b*y^c*z^a = ((z^a : End V) ≫ (y^c : End V) ≫ (x^b : End V)) := by
  simp only [End.mul_def]

end OddMath.QuiverHecke.SwappedAssembly.RepeatedOuterQCorrection
