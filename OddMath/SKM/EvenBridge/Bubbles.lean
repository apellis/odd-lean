/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleGrading
import OddMath.SKM.EvenBridge.Datum

/-!
# The bubble algebra of an even datum

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, (1.21): the
coefficient algebra `SYM` is a polynomial algebra on the even generators `e_{n+1}` of each
colour, tensored with an exterior algebra on one odd generator for each odd colour. When every
colour is even (`IsEven D`) there are no odd generators, so `SYM` is the polynomial algebra on
`I × ℕ`. This file proves this (`symEquivMvPolynomial`), gives the resulting monomial basis
of `SYM` (`symMonomialBasis`), and computes the integer degree of the image of a monomial under
the bubble homomorphism `betaSYM` of (1.22) (`betaSYM_symMonomial_mem_gdeg`): the generator
`e_{n+1}` of colour `i` has degree `2 dᵢ (n + 1)`.

These are used to count the degree pieces of the Hom spaces of `𝔘(𝔤)` for even data.
-/

noncomputable section

namespace OddMath.SKM.EvenBridge

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  (k : Type w) [CommRing k]

/-- The map from `SYM` to the polynomial algebra, killing the odd generators. -/
def symToMvPolynomial : SYM D k →ₐ[k] MvPolynomial (I × ℕ) k :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (Sum.elim MvPolynomial.X 0), by
    intro x y h
    cases h with
    | polynomial a b =>
        simp only [map_mul, FreeAlgebra.lift_ι_apply, Sum.elim_inl, mul_comm]
    | mixed a i => simp
    | exterior i j => simp
    | square i => simp⟩

@[simp] theorem symToMvPolynomial_e (i : I) (n : ℕ) :
    symToMvPolynomial k (SYM.e D k i n) = MvPolynomial.X (i, n) := by
  simp [symToMvPolynomial, SYM.e, SYM.ι, SYM.mk]

variable {k}

/-- For an even datum, any two elements of `SYM` commute. -/
theorem SYM.commute_of_isEven (hD : IsEven D) (x y : SYM D k) : Commute x y := by
  have hgen : ∀ g h : SYMGen D, Commute (SYM.ι D k g) (SYM.ι D k h) := by
    rintro (⟨i, m⟩ | ⟨i, hi⟩) (⟨j, n⟩ | ⟨j, hj⟩)
    · exact SYM.e_commute D k i j m n
    · exact absurd hj (by rw [hD j]; decide)
    · exact absurd hi (by rw [hD i]; decide)
    · exact absurd hi (by rw [hD i]; decide)
  have hmk : ∀ (P : SYM D k → Prop), (∀ r, P (algebraMap k _ r)) → (∀ g, P (SYM.ι D k g)) →
      (∀ a b, P a → P b → P (a * b)) → (∀ a b, P a → P b → P (a + b)) → ∀ y, P y := by
    intro P h0 h1 hm ha y
    obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective k (SYMRel D k) y
    induction p using FreeAlgebra.induction with
    | grade0 r => rw [AlgHom.commutes]; exact h0 r
    | grade1 g => exact h1 g
    | mul p q hp hq => rw [map_mul]; exact hm _ _ hp hq
    | add p q hp hq => rw [map_add]; exact ha _ _ hp hq
  have key : ∀ g (y : SYM D k), Commute (SYM.ι D k g) y := fun g =>
    hmk _ (fun r => Algebra.commute_algebraMap_right r _) (hgen g)
      (fun _ _ ha hb => ha.mul_right hb) (fun _ _ ha hb => ha.add_right hb)
  exact hmk (fun x => Commute x y) (fun r => Algebra.commute_algebraMap_left r _)
    (fun g => key g y) (fun _ _ ha hb => ha.mul_left hb) (fun _ _ ha hb => ha.add_left hb) x

/-- The commutative ring structure of `SYM` for an even datum. -/
abbrev SYM.commRingOfIsEven (hD : IsEven D) : CommRing (SYM D k) :=
  { (inferInstance : Ring (SYM D k)) with
    mul_comm := fun x y => (SYM.commute_of_isEven hD x y).eq }

/-- The map from the polynomial algebra to `SYM` for an even datum. -/
def mvPolynomialToSYM (hD : IsEven D) : MvPolynomial (I × ℕ) k →ₐ[k] SYM D k :=
  letI := SYM.commRingOfIsEven (k := k) hD
  MvPolynomial.aeval fun a => SYM.e D k a.1 a.2

@[simp] theorem mvPolynomialToSYM_X (hD : IsEven D) (a : I × ℕ) :
    mvPolynomialToSYM hD (MvPolynomial.X a) = SYM.e D k a.1 a.2 := by
  let _ := SYM.commRingOfIsEven (k := k) hD
  exact MvPolynomial.aeval_X _ _

/-- For an even datum, the coefficient algebra (1.21) is the polynomial algebra on the
generators `e_{n+1}` of every colour. -/
def symEquivMvPolynomial (hD : IsEven D) : SYM D k ≃ₐ[k] MvPolynomial (I × ℕ) k :=
  AlgEquiv.ofAlgHom (symToMvPolynomial k) (mvPolynomialToSYM hD)
    (MvPolynomial.algHom_ext fun a => by simp)
    (SYM.hom_ext D k fun g => by
      rcases g with ⟨i, n⟩ | ⟨i, hi⟩
      · change mvPolynomialToSYM hD (symToMvPolynomial k (SYM.e D k i n)) = SYM.e D k i n
        simp
      · exact absurd hi (by rw [hD i]; decide))

/-- The monomial `∏ e_{n+1}(i)^{m(i,n)}` of `SYM`, for an even datum. -/
def symMonomial (hD : IsEven D) (m : (I × ℕ) →₀ ℕ) : SYM D k :=
  mvPolynomialToSYM hD (MvPolynomial.monomial m 1)

/-- The monomial basis of `SYM` for an even datum. -/
def symMonomialBasis (hD : IsEven D) : Module.Basis ((I × ℕ) →₀ ℕ) k (SYM D k) :=
  (MvPolynomial.basisMonomials (I × ℕ) k).map (symEquivMvPolynomial hD).symm.toLinearEquiv

@[simp] theorem symMonomialBasis_apply (hD : IsEven D) (m : (I × ℕ) →₀ ℕ) :
    symMonomialBasis hD m = symMonomial (k := k) hD m := by
  simp [symMonomialBasis, symMonomial, MvPolynomial.coe_basisMonomials, symEquivMvPolynomial]

variable (sy : Symmetrizer D) {Sc : Scalars D k} (cs : CScalars Sc)

/-- The integer degree of the bubble monomial `∏ e_{n+1}(i)^{m(i,n)}`: the generator
`e_{n+1}` of colour `i` has degree `2 dᵢ (n + 1)`. -/
def bubbleDegree (m : (I × ℕ) →₀ ℕ) : ℤ :=
  Finsupp.weight (fun a : I × ℕ => 2 * sy.d a.1 * ((a.2 : ℤ) + 1)) m

theorem bubbleDegree_single (a : I × ℕ) (n : ℕ) :
    bubbleDegree sy (Finsupp.single a n) = n * (2 * sy.d a.1 * ((a.2 : ℤ) + 1)) := by
  rw [bubbleDegree, Finsupp.weight_single, nsmul_eq_mul]

/-- Products of homogeneous endomorphisms add degrees. -/
theorem mul_mem_gdeg {μ : X} {f g : End ((pres D Sc).obj (ob D μ []))} {d e : ℤ}
    (hf : f ∈ (pres D Sc).homDeg (gdeg D sy) (ob D μ []) (ob D μ []) d)
    (hg : g ∈ (pres D Sc).homDeg (gdeg D sy) (ob D μ []) (ob D μ []) e) :
    f * g ∈ (pres D Sc).homDeg (gdeg D sy) (ob D μ []) (ob D μ []) (d + e) := by
  rw [End.mul_def, add_comm]
  exact comp_mem_homDeg hg hf

theorem pow_mem_gdeg {μ : X} {f : End ((pres D Sc).obj (ob D μ []))} {d : ℤ}
    (hf : f ∈ (pres D Sc).homDeg (gdeg D sy) (ob D μ []) (ob D μ []) d) (n : ℕ) :
    f ^ n ∈ (pres D Sc).homDeg (gdeg D sy) (ob D μ []) (ob D μ []) (n * d) := by
  induction n with
  | zero => simpa using id_mem_homDeg (P := pres D Sc) (gdeg D sy) (ob D μ [])
  | succ n ih =>
      rw [pow_succ, show ((n + 1 : ℕ) : ℤ) * d = n * d + d by push_cast; ring]
      exact mul_mem_gdeg sy ih hf

/-- The image of a bubble monomial under the bubble homomorphism (1.22) is homogeneous of
degree `bubbleDegree`. -/
theorem betaSYM_symMonomial_mem_gdeg (hD : IsEven D) (μ : X) (m : (I × ℕ) →₀ ℕ) :
    betaSYM cs μ (symMonomial hD m) ∈
      (pres D Sc).homDeg (gdeg D sy) (ob D μ []) (ob D μ []) (bubbleDegree sy m) := by
  induction m using Finsupp.induction_linear with
  | zero =>
      simpa [symMonomial, bubbleDegree] using
        id_mem_homDeg (P := pres D Sc) (gdeg D sy) (ob D μ [])
  | add f g hf hg =>
      rw [symMonomial, ← mul_one (1 : k), ← MvPolynomial.monomial_mul_monomial, map_mul, map_mul,
        bubbleDegree, map_add]
      exact mul_mem_gdeg sy hf hg
  | single a n =>
      rw [symMonomial, ← MvPolynomial.X_pow_eq_monomial, map_pow, map_pow, bubbleDegree_single]
      refine pow_mem_gdeg sy ?_ n
      have h := betaSYMGen_mem_gdeg sy cs μ (.inl a)
      rw [← betaSYM_ι] at h
      simpa [symGenDegree, hD a.1, SYM.e] using h

end OddMath.SKM.EvenBridge
