/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ProbePairDots
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! A common polynomial for the two Q factors. Odd variables are replaced by squares.
The adapter uses the ordinary End ring: its product is reverse categorical composition.
No centrality assertion is made before the crossing slides are supplied.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
open CategoryTheory StringDiagrams OddMath.SKM
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : Datum I X} (Sc : Scalars D k)

/-- Exponent in the ordinary polynomial variable: halve exactly at odd colours. -/
def qExponent (i : I) (n : ℕ) : ℕ := if D.parity i = 1 then n / 2 else n

/-- Compressing an odd dot to its square preserves exactly the parity-allowed powers. -/
theorem qExponent_allowed_pow {R : Type*} [Monoid R] (i : I) (z : R) (n : ℕ)
    (hn : (n : ZMod 2) * D.parity i = 0) :
    (if D.parity i = 1 then z ^ 2 else z) ^ qExponent (D := D) i n = z ^ n := by
  by_cases hi : D.parity i = 1
  · rw [hi, mul_one] at hn
    obtain ⟨m, rfl⟩ := (ZMod.natCast_eq_zero_iff n 2).1 hn
    simp only [qExponent, hi, ↓reduceIte, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    rw [← pow_mul]
  · simp only [qExponent, hi, ↓reduceIte]

/-- Q as a polynomial in the probe variable, with spectator powers in its coefficients. -/
def qCoefficientPolynomial {K : Type*} [CommRing K] [Algebra k K]
    (i r : I) (v : K) : Polynomial K :=
  if D.d i r = 0 then Polynomial.C (algebraMap k K (Sc.t i r : k)) else
    Polynomial.C (algebraMap k K (Sc.t i r : k)) * Polynomial.X ^ qExponent (D := D) i (D.dn i r) +
    Polynomial.C (algebraMap k K (Sc.t r i : k) * v ^ qExponent (D := D) r (D.dn r i)) +
    ∑ p ∈ Finset.Ioo 0 (D.dn i r), ∑ q ∈ Finset.Ioo 0 (D.dn r i),
      Polynomial.C (algebraMap k K (Sc.s i r p q) * v ^ qExponent (D := D) r q) *
        Polynomial.X ^ qExponent (D := D) i p

/-- Evaluation first takes place in a commutative ring, so the order of the two powers is fixed. -/
theorem qCoefficientPolynomial_eval {K S : Type*} [CommRing K] [Algebra k K]
    [CommRing S] [Algebra k S] (c : K →ₐ[k] S) (i r : I) (v : K) (a : S) :
    (qCoefficientPolynomial Sc i r v).eval₂ c.toRingHom a =
      if D.d i r = 0 then (Sc.t i r : k) • (1 : S) else
        (Sc.t i r : k) • a ^ qExponent (D := D) i (D.dn i r) +
        (Sc.t r i : k) • c v ^ qExponent (D := D) r (D.dn r i) +
        ∑ p ∈ Finset.Ioo 0 (D.dn i r), ∑ q ∈ Finset.Ioo 0 (D.dn r i),
          Sc.s i r p q • (a ^ qExponent (D := D) i p * c v ^ qExponent (D := D) r q) := by
  have hc (t : k) : c.toRingHom (algebraMap k K t) = algebraMap k S t := c.commutes t
  unfold qCoefficientPolynomial
  split_ifs <;> simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finsetSum, map_mul, map_pow,
    hc, Algebra.smul_def, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  change algebraMap k S (Sc.s i r p q) * c v ^ qExponent (D := D) r q *
    a ^ qExponent (D := D) i p = _
  ring

/-- The existing Q expression is evaluation of this polynomial. The power hypotheses
are the adapter interface, not a centrality hypothesis. They only concern allowed exponents. -/
theorem qExpr_eq_qCoefficientPolynomial_eval
    {C : Type*} [Category C] [Preadditive C] [Linear k C] {A : C}
    {K S : Type*} [CommRing K] [Algebra k K] [CommRing S] [Algebra k S]
    (c : K →ₐ[k] S) (φ : S →ₐ[k] End A) (i r : I) (v : K) (a : S) (x y : End A)
    (hx : ∀ n : ℕ, (n : ZMod 2) * D.parity i = 0 →
      φ a ^ qExponent (D := D) i n = x ^ n)
    (hy : ∀ n : ℕ, (n : ZMod 2) * D.parity r = 0 →
      φ (c v) ^ qExponent (D := D) r n = y ^ n) :
    qExpr Sc x y i r = φ ((qCoefficientPolynomial Sc i r v).eval₂ c.toRingHom a) := by
  rw [qCoefficientPolynomial_eval]
  unfold qExpr
  split_ifs
  · simp only [map_smul, map_one]
  · simp only [map_add, map_smul, map_pow, map_sum, map_mul]
    rw [hx _ (by simpa [mul_comm] using parity_mul_dn D i r),
      hy _ (by simpa [mul_comm] using parity_mul_dn D r i)]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    by_cases hs : Sc.s i r p q = 0
    · simp only [hs, zero_smul]
    · obtain ⟨hp, hq⟩ := Sc.parity_of_ne_zero hs
      rw [hx p hp, hy q hq]

/-- The power interface is discharged by taking the odd variables to be squares. -/
theorem qExpr_eq_eval_of_compressed
    {C : Type*} [Category C] [Preadditive C] [Linear k C] {A : C}
    {K S : Type*} [CommRing K] [Algebra k K] [CommRing S] [Algebra k S]
    (c : K →ₐ[k] S) (φ : S →ₐ[k] End A) (i r : I) (v : K) (a : S) (x y : End A)
    (hx : φ a = if D.parity i = 1 then x ^ 2 else x)
    (hy : φ (c v) = if D.parity r = 1 then y ^ 2 else y) :
    qExpr Sc x y i r = φ ((qCoefficientPolynomial Sc i r v).eval₂ c.toRingHom a) :=
  qExpr_eq_qCoefficientPolynomial_eval Sc c φ i r v a x y
    (fun n hn => by rw [hx]; exact qExponent_allowed_pow i x n hn)
    (fun n hn => by rw [hy]; exact qExponent_allowed_pow r y n hn)

/-- Both Q factors evaluate the SAME polynomial with the SAME coefficient map.
The reversed product on the right is essential: End multiplication reverses composition.
The remaining centrality proof must construct the commutative ring and establish its slides. -/
theorem qExpr_pair_eq_eval_product
    {C : Type*} [Category C] [Preadditive C] [Linear k C] {A : C}
    {K S : Type*} [CommRing K] [Algebra k K] [CommRing S] [Algebra k S]
    (c : K →ₐ[k] S) (φ : S →ₐ[k] End A) (i r : I) (v : K) (a b : S)
    (x₁ x₂ y : End A)
    (ha : φ a = if D.parity i = 1 then x₁ ^ 2 else x₁)
    (hb : φ b = if D.parity i = 1 then x₂ ^ 2 else x₂)
    (hv : φ (c v) = if D.parity r = 1 then y ^ 2 else y) :
    qExpr Sc x₁ y i r ≫ qExpr Sc x₂ y i r =
      φ ((qCoefficientPolynomial Sc i r v).eval₂ c.toRingHom b *
        (qCoefficientPolynomial Sc i r v).eval₂ c.toRingHom a) := by
  rw [qExpr_eq_eval_of_compressed Sc c φ i r v a x₁ y ha hv,
    qExpr_eq_eval_of_compressed Sc c φ i r v b x₂ y hb hv, map_mul, End.mul_def]

section ActualProbePair
variable {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  (P : ProbeReservoir k B D Sc) (i r : I) (s : Sector I)
  (hR : StepValid (true, r) false s)
  (Z : P.H (nextSector (true, r) false
    (nextSector (true, i) true (nextSector (true, i) true s))))

/-- Actual transported Q product, with a supplied commutative realization of the compressed dots.
This does not assume centrality or a braid equation. Constructing this realization and its
crossing-slide data is the remaining application obligation. -/
theorem probePairQProduct_eq_eval_product
    {K S : Type*} [CommRing K] [Algebra k K] [CommRing S] [Algebra k S]
    (c : K →ₐ[k] S)
    (φ : S →ₐ[k] End ((P.step (true, i) true s trivial).obj
      (P.prObj i r (nextSector (true, i) true s) hR Z)))
    (v : K) (a b : S)
    (ha : φ a = if D.parity i = 1 then
      (P.ppLeftDot i s ((P.step (true, r) false
        (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z)) ^ 2 else
      P.ppLeftDot i s ((P.step (true, r) false
        (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z))
    (hb : φ b = if D.parity i = 1 then
      (P.ppRightDot i s ((P.step (true, r) false
        (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z)) ^ 2 else
      P.ppRightDot i s ((P.step (true, r) false
        (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z))
    (hv : φ (c v) = if D.parity r = 1 then
      (P.probePairSpectatorDot i r s hR Z) ^ 2 else P.probePairSpectatorDot i r s hR Z) :
    ((P.probePairFirstIso i r s hR Z).hom ≫
      P.mixedQ i r s hR ((P.step (true, i) true
        (nextSector (true, r) false (nextSector (true, i) true s)) trivial).obj Z) ≫
      (P.probePairFirstIso i r s hR Z).inv) ≫
      (P.step (true, i) true s trivial).map
        (P.mixedQ i r (nextSector (true, i) true s) hR Z) =
      φ ((qCoefficientPolynomial Sc i r v).eval₂ c.toRingHom b *
        (qCoefficientPolynomial Sc i r v).eval₂ c.toRingHom a) := by
  rw [P.probePairFirstIso_conj_mixedQ, P.probePair_map_mixedQ]
  exact qExpr_pair_eq_eval_product Sc c φ i r v a b _ _ _ ha hb hv
end ActualProbePair

end OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
