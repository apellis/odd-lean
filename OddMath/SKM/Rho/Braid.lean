import OddMath.SKM.Rho.BraidImages

/-!
# Braid for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.SKM.RhoCoefficients
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem parity_pair_zero (a : ZMod 2) (n s : ℕ) (hs : s < n)
    (ha : a * (n : ZMod 2) = 0) :
    ((s : ZMod 2)*a) * (((n-1-s : ℕ) : ZMod 2)*a) = 0 := by
  have he : n = s + (n-1-s) + 1 := by omega
  rw [he, Nat.cast_add, Nat.cast_add, Nat.cast_one] at ha
  have H : ∀ a r s : ZMod 2, a*(s+r+1) = 0 → (s*a)*(r*a) = 0 := by decide
  exact H a _ _ ha

def braidMonomial (t : k) (ν : X) (i j : I) (r q s : ℕ) :
    (pres D Sc).obj (ob D ν [dn i,dn j,dn i]) ⟶ (pres D Sc).obj (ob D ν [dn i,dn j,dn i]) :=
  (psiCoeff t (D.parity i)^s * psiCoeff t (D.parity j)^q * psiCoeff t (D.parity i)^r) •
    cl D Sc ν [dn i,dn j,dn i] [dn i,dn j,dn i] (reversedDots3 i j s q r)

theorem correction_term (t : k) (ht : t^2 = -1) (ν : X) (i j : I)
    (n q s : ℕ) (hs : s < n) (ha : D.parity i * (n : ZMod 2) = 0)
    (hb : D.parity j * (q : ZMod 2) = 0) :
    braidCoeff (D := D) t i j i •
      (zsign k (D.parity i * ((n/2 : ℕ)+s+1) + D.parity j * (q/2 : ℕ)) •
        cl D Sc ν [dn i,dn j,dn i] [dn i,dn j,dn i] (dots3 i j s q (n-1-s))) =
    zsign k (D.parity i * (D.parity j+s)) •
      braidMonomial (Sc := Sc) t ν i j (n-1-s) q s := by
  rw [braidMonomial, dots3_reverse ν i j (n-1-s) q s
    (by simpa [mul_comm] using hb) (parity_pair_zero _ n s hs ha)]
  simp only [smul_smul, braidCoeff]
  rw [braid_coefficient t ht _ _ n q s hs ha hb]

theorem crossing_braid_ne (t : k) (ν μ : X) (i j a : I)
    (h : wt D μ (ups [i,j,a]) = ν) (hia : ¬(i = a ∧ i ≠ j)) :
    crossLeft3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h ≫
      crossRight3 t ν μ j i a ((wt_swap_left3 μ i j a).trans h) ≫
      crossLeft3 t ν μ j a i ((wt_swap_right3 μ j i a).trans ((wt_swap_left3 μ i j a).trans h)) =
    crossRight3 t ν μ i j a h ≫
      crossLeft3 t ν μ i a j ((wt_swap_right3 μ i j a).trans h) ≫
      crossRight3 t ν μ a i j ((wt_swap_left3 μ i a j).trans ((wt_swap_right3 μ i j a).trans h)) := by
  rw [crossLeft3_comp, crossRight3_comp, lemma33_eq9 Sc i j a ν hia]

theorem crossing_braid_eq_raw (t : k) (ht : t^2 = -1) (ν : X) (i j : I) (hij : i ≠ j) :
    braidCoeff (D := D) t i j i •
      (cl D Sc ν [dn i,dn j,dn i] [dn i,dn j,dn i] (lemma33_eq9_lhs i j i) -
        cl D Sc ν [dn i,dn j,dn i] [dn i,dn j,dn i] (lemma33_eq9_rhs i j i)) =
      (Sc.t i j : k) • ∑ s ∈ Finset.range (D.dn i j),
        zsign k (D.parity i * (D.parity j+s)) •
          braidMonomial (Sc := Sc) t ν i j (D.dn i j-1-s) 0 s +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j p q • ∑ s ∈ Finset.range p,
          zsign k (D.parity i * (D.parity j+s)) •
            braidMonomial (Sc := Sc) t ν i j (p-1-s) q s := by
  rw [lemma33_eq9_eq Sc i j ν hij, smul_add]
  congr 1
  · simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have H := correction_term (Sc := Sc) t ht ν i j (D.dn i j) 0 s
      (Finset.mem_range.mp hs) (parity_mul_dn D i j) (by simp)
    have H' := congrArg ((Sc.t i j : k) • ·) H
    simpa only [Nat.zero_div, Nat.cast_zero, mul_zero, zero_mul, add_zero, smul_smul,
      mul_assoc, mul_comm, mul_left_comm] using H'
  · simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hsc : Sc.s i j p q = 0
    · simp [hsc]
    obtain ⟨hpi,hqj⟩ := Sc.parity_of_ne_zero hsc
    apply Finset.sum_congr rfl
    intro s hs
    have H := correction_term (Sc := Sc) t ht ν i j p q s (Finset.mem_range.mp hs)
      (by simpa [mul_comm] using hpi) (by simpa [mul_comm] using hqj)
    have H' := congrArg (Sc.s i j p q • ·) H
    simpa only [smul_smul, mul_assoc, mul_comm, mul_left_comm] using H'

end OddMath.SKM.RhoCoefficients
