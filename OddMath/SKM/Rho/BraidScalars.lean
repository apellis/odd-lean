import OddMath.SKM.Rho.Powers

/-!
# Braid Scalars for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.SKM.RhoCoefficients
universe w
variable {k : Type w} [CommRing k]

theorem coeff_pow_pred (t : k) (ht : t ^ 2 = -1) (a : ZMod 2) (n : ℕ)
    (hn : 0 < n) (ha : a * (n : ZMod 2) = 0) :
    psiCoeff t a ^ (n-1) = psiCoeff t a * zsign k (a * ((n/2 : ℕ) + 1)) := by
  rcases parity_eq_zero_or_one a with rfl | rfl
  · simp [psiCoeff, zsign]
  · simp only [one_mul] at ha ⊢
    have heven : n % 2 = 0 := by
      have H := congrArg ZMod.val ha
      simpa using H
    obtain ⟨m,hm⟩ : ∃ m, n = 2*m+2 := ⟨n/2-1, by omega⟩
    subst n
    have he : (2*m+2-1) = 2*m+1 := by omega
    rw [psiCoeff_one, he, pow_add, pow_mul, ht]
    rw [show (2*m+2)/2 = m+1 by omega]
    simp only [Nat.cast_add, Nat.cast_one, zsign_add, pow_one]
    have H := zsign_natCast_mul (k := k) m (1 : ZMod 2)
    simp only [one_mul] at H
    rw [H]
    simp [zsign, mul_comm]

theorem braid_coefficient (t : k) (ht : t^2 = -1) (a b : ZMod 2)
    (n q s : ℕ) (hs : s < n) (ha : a * (n : ZMod 2) = 0)
    (hb : b * (q : ZMod 2) = 0) :
    (psiCoeff t (a*b) * psiCoeff t (a*a) * psiCoeff t (b*a)) *
      zsign k (a * ((n/2 : ℕ) + s + 1) + b * (q/2 : ℕ)) =
    zsign k (a*(b+s)) *
      (psiCoeff t a ^ s * psiCoeff t b ^ q * psiCoeff t a ^ (n-1-s)) := by
  have hpow : psiCoeff t a ^ s * psiCoeff t a ^ (n-1-s) = psiCoeff t a ^ (n-1) := by
    rw [← pow_add, Nat.add_sub_of_le (by omega)]
  have hsq : psiCoeff t (a*b) * psiCoeff t (b*a) = zsign k (a*b) := by
    rw [mul_comm b a]
    rcases parity_eq_zero_or_one (a*b) with h | h <;> simp [h, psiCoeff, zsign, ← pow_two, ht]
  rw [show psiCoeff t a ^ s * psiCoeff t b ^ q * psiCoeff t a ^ (n-1-s) =
      (psiCoeff t a ^ s * psiCoeff t a ^ (n-1-s)) * psiCoeff t b ^ q by ring,
    hpow, coeff_pow_pred t ht a n (by omega) ha, coeff_pow_even t ht b q hb,
    zmod2_mul_self']
  rw [show psiCoeff t (a*b) * psiCoeff t a * psiCoeff t (b*a) =
      (psiCoeff t (a*b) * psiCoeff t (b*a)) * psiCoeff t a by ring, hsq]
  simp only [mul_add, zsign_add]
  ring

end OddMath.SKM.RhoCoefficients
