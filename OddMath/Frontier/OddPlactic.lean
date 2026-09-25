import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# The signed plactic ring and its universal property

Ellis, arXiv:1111.3932v1, §3.1, equation (3.1):
`yzx = -yxz` for `x < y ≤ z`, and `xzy = -zxy` for `x ≤ y < z`.
We use `Fin n` with its usual order (paper label = Lean label + 1).
The coefficient ring is ℤ. This is the free associative unital algebra
modulo the TWO-SIDED ideal of exactly these signed relations. It is not
the unsigned plactic monoid, nor an exterior algebra. No square-zero
relation is imposed. Word order is literal left-to-right product.

This module proves the presentation and its unique universal factorization,
not the tableau normal-form/basis theorem (Ellis Theorem 3.1), nor Schur
comparison. No tableau hypothesis is needed to construct this ring.
-/

namespace OddMath.Frontier.OddPlactic

/-- The two signed Knuth relation polynomials, with the source inequalities. -/
def relSet (n : ℕ) : Set (FreeAlgebra ℤ (Fin n)) :=
  {p | (∃ x y z : Fin n, x < y ∧ y ≤ z ∧
      p = FreeAlgebra.ι ℤ y * FreeAlgebra.ι ℤ z * FreeAlgebra.ι ℤ x +
        FreeAlgebra.ι ℤ y * FreeAlgebra.ι ℤ x * FreeAlgebra.ι ℤ z) ∨
    (∃ x y z : Fin n, x ≤ y ∧ y < z ∧
      p = FreeAlgebra.ι ℤ x * FreeAlgebra.ι ℤ z * FreeAlgebra.ι ℤ y +
        FreeAlgebra.ι ℤ z * FreeAlgebra.ι ℤ x * FreeAlgebra.ι ℤ y)}

/-- Two-sided generation is essential: relations may occur inside any word. -/
def relIdeal (n : ℕ) : Ideal (FreeAlgebra ℤ (Fin n)) :=
  (TwoSidedIdeal.span (relSet n)).asIdeal

instance relIdealTwoSided (n : ℕ) : (relIdeal n).IsTwoSided :=
  inferInstanceAs ((TwoSidedIdeal.span (relSet n)).asIdeal.IsTwoSided)

/-- Ellis's integer odd plactic ring on the alphabet with `n` letters. -/
def Plactic (n : ℕ) : Type := FreeAlgebra ℤ (Fin n) ⧸ relIdeal n

instance placticRing (n : ℕ) : Ring (Plactic n) :=
  Ideal.Quotient.ring (relIdeal n)

/-- The canonical quotient map from the integer free word algebra. -/
def quotientMap (n : ℕ) : FreeAlgebra ℤ (Fin n) →+* Plactic n :=
  Ideal.Quotient.mk (relIdeal n)

/-- A letter in the odd plactic ring. -/
def q (n : ℕ) (i : Fin n) : Plactic n := quotientMap n (FreeAlgebra.ι ℤ i)

/-- Literal word evaluation, including the empty word and repetitions. -/
def word (n : ℕ) (w : List (Fin n)) : Plactic n := (w.map (q n)).prod

@[simp] theorem word_nil (n : ℕ) : word n [] = 1 := rfl

@[simp] theorem word_cons (n : ℕ) (i : Fin n) (w : List (Fin n)) :
    word n (i :: w) = q n i * word n w := rfl

@[simp] theorem word_append (n : ℕ) (u v : List (Fin n)) :
    word n (u ++ v) = word n u * word n v := by
  simp [word]

/-- The exact source relations a map on letters must respect. -/
def RespectsKnuth {n : ℕ} {R : Type*} [Ring R] (f : Fin n → R) : Prop :=
  (∀ x y z, x < y → y ≤ z → f y * f z * f x = -(f y * f x * f z)) ∧
  (∀ x y z, x ≤ y → y < z → f x * f z * f y = -(f z * f x * f y))

/-- Every relation polynomial vanishes in the quotient. -/
theorem quotientMap_rel {n : ℕ} {p : FreeAlgebra ℤ (Fin n)} (hp : p ∈ relSet n) :
    quotientMap n p = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact TwoSidedIdeal.subset_span hp

/-- Ellis (3.1), K′, including the allowed equality `y = z`. -/
theorem knuth_left (n : ℕ) (x y z : Fin n) (hxy : x < y) (hyz : y ≤ z) :
    q n y * q n z * q n x = -(q n y * q n x * q n z) := by
  apply add_eq_zero_iff_eq_neg.mp
  have h := quotientMap_rel (n := n) (Or.inl ⟨x, y, z, hxy, hyz, rfl⟩)
  simpa only [map_add, map_mul, q] using h

/-- Ellis (3.1), K′′, including the allowed equality `x = y`. -/
theorem knuth_right (n : ℕ) (x y z : Fin n) (hxy : x ≤ y) (hyz : y < z) :
    q n x * q n z * q n y = -(q n z * q n x * q n y) := by
  apply add_eq_zero_iff_eq_neg.mp
  have h := quotientMap_rel (n := n) (Or.inr ⟨x, y, z, hxy, hyz, rfl⟩)
  simpa only [map_add, map_mul, q] using h

theorem q_respects (n : ℕ) : RespectsKnuth (q n) :=
  ⟨knuth_left n, knuth_right n⟩

/-- Signed K′ inside arbitrary prefix/suffix words. -/
theorem word_knuth_left (n : ℕ) (u v : List (Fin n)) (x y z : Fin n)
    (hxy : x < y) (hyz : y ≤ z) :
    word n (u ++ [y, z, x] ++ v) = -word n (u ++ [y, x, z] ++ v) := by
  have h := knuth_left n x y z hxy hyz
  simp only [word_append, word_cons, word_nil, mul_one]
  simp only [← mul_assoc] at h ⊢
  calc
    word n u * q n y * q n z * q n x * word n v =
        word n u * (q n y * q n z * q n x) * word n v := by simp only [mul_assoc]
    _ = word n u * (-(q n y * q n x * q n z)) * word n v := by rw [h]
    _ = -(word n u * q n y * q n x * q n z * word n v) := by
      simp only [mul_neg, neg_mul, mul_assoc]

/-- Signed K′′ inside arbitrary prefix/suffix words. -/
theorem word_knuth_right (n : ℕ) (u v : List (Fin n)) (x y z : Fin n)
    (hxy : x ≤ y) (hyz : y < z) :
    word n (u ++ [x, z, y] ++ v) = -word n (u ++ [z, x, y] ++ v) := by
  have h := knuth_right n x y z hxy hyz
  simp only [word_append, word_cons, word_nil, mul_one]
  simp only [← mul_assoc] at h ⊢
  calc
    word n u * q n x * q n z * q n y * word n v =
        word n u * (q n x * q n z * q n y) * word n v := by simp only [mul_assoc]
    _ = word n u * (-(q n z * q n x * q n y)) * word n v := by rw [h]
    _ = -(word n u * q n z * q n x * q n y * word n v) := by
      simp only [mul_neg, neg_mul, mul_assoc]

section UniversalProperty
variable {n : ℕ} {R : Type*} [Ring R]

/-- The free-algebra extension of an arbitrary letter assignment. -/
def freeEval (f : Fin n → R) : FreeAlgebra ℤ (Fin n) →+* R :=
  (FreeAlgebra.lift ℤ f).toRingHom

@[simp] theorem freeEval_ι (f : Fin n → R) (i : Fin n) :
    freeEval f (FreeAlgebra.ι ℤ i) = f i := FreeAlgebra.lift_ι_apply f i

/-- The defining signed relations suffice to kill the entire two-sided ideal. -/
theorem freeEval_kills (f : Fin n → R) (hf : RespectsKnuth f)
    (p : FreeAlgebra ℤ (Fin n)) (hp : p ∈ relIdeal n) : freeEval f p = 0 := by
  rw [relIdeal, TwoSidedIdeal.mem_asIdeal] at hp
  induction hp using TwoSidedIdeal.span_induction with
  | mem p hp =>
      rcases hp with ⟨x, y, z, hxy, hyz, rfl⟩ | ⟨x, y, z, hxy, hyz, rfl⟩
      · simpa only [map_add, map_mul, freeEval_ι] using
          (add_eq_zero_iff_eq_neg.mpr (hf.1 x y z hxy hyz))
      · simpa only [map_add, map_mul, freeEval_ι] using
          (add_eq_zero_iff_eq_neg.mpr (hf.2 x y z hxy hyz))
  | zero => exact map_zero _
  | add a b ha hb ia ib => rw [map_add, ia, ib, add_zero]
  | neg a ha ia => rw [map_neg, ia, neg_zero]
  | left_absorb a b hb ib => rw [map_mul, ib, mul_zero]
  | right_absorb a b hb ib => rw [map_mul, ib, zero_mul]

/-- Universal factorization of a signed-Knuth-respecting letter map. -/
def lift (f : Fin n → R) (hf : RespectsKnuth f) : Plactic n →+* R :=
  Ideal.Quotient.lift (relIdeal n) (freeEval f) (freeEval_kills f hf)

@[simp] theorem lift_quotientMap (f : Fin n → R) (hf : RespectsKnuth f)
    (p : FreeAlgebra ℤ (Fin n)) : lift f hf (quotientMap n p) = freeEval f p := rfl

@[simp] theorem lift_q (f : Fin n → R) (hf : RespectsKnuth f) (i : Fin n) :
    lift f hf (q n i) = f i := by
  exact freeEval_ι f i

/-- The factorization evaluates every word, not just cubic relation words. -/
theorem lift_word (f : Fin n → R) (hf : RespectsKnuth f) (w : List (Fin n)) :
    lift f hf (word n w) = (w.map f).prod := by
  induction w with
  | nil => exact map_one _
  | cons i w ih => simp only [word_cons, map_mul, lift_q, List.map_cons, List.prod_cons, ih]

/-- Maps from the quotient are determined by their values on letters. -/
@[ext] theorem hom_ext {g h : Plactic n →+* R} (he : ∀ i, g (q n i) = h (q n i)) :
    g = h := by
  apply RingHom.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective (I := relIdeal n) a
  change g (quotientMap n p) = h (quotientMap n p)
  induction p using FreeAlgebra.induction with
  | grade0 r => simp
  | grade1 i => exact he i
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Existence AND uniqueness, uniformly in the alphabet size and target ring. -/
theorem existsUnique_lift (f : Fin n → R) (hf : RespectsKnuth f) :
    ∃! g : Plactic n →+* R, ∀ i, g (q n i) = f i := by
  refine ⟨lift f hf, lift_q f hf, ?_⟩
  intro g hg
  exact hom_ext (fun i => (hg i).trans (lift_q f hf i).symm)

/-- Necessity of the signed relations: every quotient map satisfies them. -/
theorem hom_respects (g : Plactic n →+* R) : RespectsKnuth (fun i => g (q n i)) := by
  constructor
  · intro x y z hxy hyz
    simpa only [map_mul, map_neg] using congrArg g (knuth_left n x y z hxy hyz)
  · intro x y z hxy hyz
    simpa only [map_mul, map_neg] using congrArg g (knuth_right n x y z hxy hyz)

/-- No extra assumptions on a letter assignment are hidden in the universal property. -/
theorem exists_lift_iff (f : Fin n → R) :
    (∃ g : Plactic n →+* R, ∀ i, g (q n i) = f i) ↔ RespectsKnuth f := by
  constructor
  · rintro ⟨g, hg⟩
    have h := hom_respects g
    simpa only [hg] using h
  · intro hf
    exact ⟨lift f hf, lift_q f hf⟩

end UniversalProperty
end OddMath.Frontier.OddPlactic
