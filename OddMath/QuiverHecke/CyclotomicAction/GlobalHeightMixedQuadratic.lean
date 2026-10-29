/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightMixedSlides
import OddMath.QuiverHecke.CyclotomicAction.MixedComparison
import OddMath.QuiverHecke.CyclotomicAction.AppendCoordinates
import OddMath.QuiverHecke.CyclotomicAction.MoveHomSnoc

/-!
# The distinct-colour quadratic relation on two inductions from every height

The algebra half of the quadratic relations (1.7) of Brundan–Ellis, arXiv:1701.04133v2,
Definition 1.5, for distinct colours, at every height of the extended tower. On the words
`w j i`, the square of the last-pair crossing is the explicit two-colour polynomial
`Q_{ji}` (`affineLastCrossing_mixed`). Writing `A = φᵢ(y_j)` for the appended dot,
`B = y_i` for the new last dot and `e = φᵢφⱼ(1)` for the two-colour idempotent,

  `c_{ij} c_{ji} = e · Q_{ji}(A, B)`

in the affine algebra (`affineLastCrossing_mul_mixed`) and at every height
(`heightLastCrossing_mul_mixed`), where `Q_{ji}(A, B) = t_{ji} 1` if `d_{ji} = 0` and otherwise

  `Q_{ji}(A, B) = ∑_{0<p<d_{ji}, 0<q<d_{ij}} s_{ji}^{pq} A^p B^q + t_{ji} A^{d_{ji}} + t_{ij} B^{d_{ij}}`.

This is an identity of algebra elements; no parameter change is made here.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- The explicit two-colour quadratic polynomial in two elements of a `k`-algebra. -/
def pairQuadPoly {R : Type*} [Ring R] [Algebra k R] (i j : I) (A B : R) : R :=
  if D.d i j = 0 then (Sc.t i j : k) • 1 else
    ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
      Sc.s i j p q • (A ^ p * B ^ q) +
      ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i)

theorem map_pairQuadPoly {R S : Type*} [Ring R] [Algebra k R] [Ring S] [Algebra k S]
    (f : R →ₐ[k] S) (i j : I) (A B : R) :
    f (pairQuadPoly D Sc i j A B) = pairQuadPoly D Sc i j (f A) (f B) := by
  unfold pairQuadPoly
  split_ifs <;> simp [map_add, map_sum, map_smul, map_mul, map_pow]

/-- `wordQuadratic` is the polynomial in the two positioned dots. -/
theorem wordQuadratic_eq_pairQuadPoly (i j : I) (t : List I) (r : ℕ) :
    wordQuadratic D Sc i j t r = pairQuadPoly D Sc i j (dotE D Sc t r) (dotE D Sc t (r + 1)) :=
  rfl

variable [Fintype I]

section PairDiag
variable (i j : I) (n : ℕ)

/-- Diagonal matrices supported on the words `w j i`. -/
def pairDiag : (∀ w : Word I n, End (wordObj D Sc (appendWord i (appendWord j w)))) →ₗ[k]
    Hn D Sc (n + 1 + 1) where
  toFun F := ∑ w : Word I n, FiniteHomMatrix.single (appendWord i (appendWord j w))
    (appendWord i (appendWord j w)) (F w)
  map_add' F G := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => FiniteHomMatrix.single_add _ _ _ _
  map_smul' c F := by
    rw [RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun w _ => by
      rw [Pi.smul_apply]; exact FiniteHomMatrix.single_smul _ _ _ _

theorem pairDiag_apply (F : ∀ w : Word I n, End (wordObj D Sc (appendWord i (appendWord j w)))) :
    pairDiag D Sc i j n F = ∑ w : Word I n, FiniteHomMatrix.single
      (appendWord i (appendWord j w)) (appendWord i (appendWord j w)) (F w) := rfl

variable {i j n}

omit [Fintype I] in
private theorem pairWord_injective {w v : Word I n}
    (h : appendWord i (appendWord j w) = appendWord i (appendWord j v)) : w = v :=
  appendWord_injective j n (appendWord_injective i (n + 1) h)

theorem pairDiag_mul (F G : ∀ w : Word I n, End (wordObj D Sc (appendWord i (appendWord j w)))) :
    pairDiag D Sc i j n F * pairDiag D Sc i j n G = pairDiag D Sc i j n (F * G) := by
  simp only [pairDiag_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_eq_single w]
  · rw [FiniteHomMatrix.single_mul_single]
    rfl
  · intro b _ hb
    apply FiniteHomMatrix.single_mul_single_of_ne
    intro h
    exact hb (pairWord_injective h)
  · simp

theorem pairDiag_mul_affineLastDot
    (F : ∀ w : Word I n, End (wordObj D Sc (appendWord i (appendWord j w)))) :
    pairDiag D Sc i j n F * affineLastDot D Sc i (n + 1) =
      pairDiag D Sc i j n (fun w => F w * inductionLastDot D Sc i (appendWord j w)) := by
  simp only [pairDiag_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [affineLastDot, Finset.mul_sum, Finset.sum_eq_single (appendWord j w)]
  · rw [FiniteHomMatrix.single_mul_single]
    rfl
  · intro b _ hb
    apply FiniteHomMatrix.single_mul_single_of_ne
    intro h
    exact hb (appendWord_injective i (n + 1) h).symm
  · simp

variable (i j n)

/-- The two-colour idempotent `φᵢφⱼ(1)` is the diagonal identity on the words `w j i`. -/
theorem appendAlgebra_appendAlgebra_one_eq_pairDiag :
    appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc j n 1) = pairDiag D Sc i j n 1 := by
  change appendLinear D Sc i (n + 1)
    (appendLinear D Sc j n (FiniteHomMatrix.localUnit Finset.univ)) = _
  rw [FiniteHomMatrix.localUnit, map_sum, map_sum, pairDiag_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  change appendLinear D Sc i (n + 1)
    (appendLinear D Sc j n (FiniteHomMatrix.single w w (𝟙 _))) = _
  rw [appendLinear_single, appendLinear_single]
  change FiniteHomMatrix.single _ _ (appendEnd D Sc i _ (appendEnd D Sc j w 1)) = _
  rw [map_one, map_one]
  rfl

/-- The appended dot `φᵢ(y_j)` is diagonal on the words `w j i`. -/
theorem appendAlgebra_affineLastDot_eq_pairDiag :
    appendAlgebra D Sc i (n + 1) (affineLastDot D Sc j n) =
      pairDiag D Sc i j n (fun w => appendHom D Sc i _ _ (inductionLastDot D Sc j w)) := by
  change appendLinear D Sc i (n + 1) (affineLastDot D Sc j n) = _
  rw [affineLastDot, map_sum, pairDiag_apply]
  exact Finset.sum_congr rfl fun w _ => appendLinear_single D Sc i _ _ _

omit [Fintype I] in
/-- The appended dot is the positioned dot on the strand of colour `j`. -/
theorem appendHom_inductionLastDot_eq_dotE (w : Word I n) :
    appendHom D Sc i _ _ (inductionLastDot D Sc j w) =
      dotE D Sc (appendWord i (appendWord j w)).1 w.1.length := by
  change inductionLastDot D Sc j w ▷ (pres D Sc).obj (ob D [i]) = _
  rw [inductionLastDot_eq_dotE]
  exact dotE_whiskerRight D Sc _ [i] _ (by simp)

omit [Fintype I] in
/-- The new last dot is the positioned dot on the strand of colour `i`. -/
theorem inductionLastDot_appendWord_eq_dotE (w : Word I n) :
    inductionLastDot D Sc i (appendWord j w) =
      dotE D Sc (appendWord i (appendWord j w)).1 (w.1.length + 1) := by
  rw [inductionLastDot_eq_dotE]
  congr 1
  simp [appendWord]

/-- The two dot families on the words `w j i`. -/
private abbrev pairA (w : Word I n) : End (wordObj D Sc (appendWord i (appendWord j w))) :=
  dotE D Sc (appendWord i (appendWord j w)).1 w.1.length

private abbrev pairB (w : Word I n) : End (wordObj D Sc (appendWord i (appendWord j w))) :=
  dotE D Sc (appendWord i (appendWord j w)).1 (w.1.length + 1)

private theorem pairDiag_monomial (p q : ℕ) :
    appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc j n 1) *
        (appendAlgebra D Sc i (n + 1) (affineLastDot D Sc j n) ^ p *
          affineLastDot D Sc i (n + 1) ^ q) =
      pairDiag D Sc i j n (fun w => pairA D Sc i j n w ^ p * pairB D Sc i j n w ^ q) := by
  have hA : ∀ p : ℕ, appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc j n 1) *
      appendAlgebra D Sc i (n + 1) (affineLastDot D Sc j n) ^ p =
        pairDiag D Sc i j n (fun w => pairA D Sc i j n w ^ p) := by
    intro p
    induction p with
    | zero =>
      rw [pow_zero, mul_one, appendAlgebra_appendAlgebra_one_eq_pairDiag]
      congr 1
    | succ p ih =>
      rw [pow_succ, ← mul_assoc, ih, appendAlgebra_affineLastDot_eq_pairDiag, pairDiag_mul]
      congr 1
      funext w
      rw [Pi.mul_apply, appendHom_inductionLastDot_eq_dotE, pow_succ]
  rw [← mul_assoc, hA]
  induction q with
  | zero => simp only [pow_zero, mul_one]
  | succ q ih =>
    rw [pow_succ, ← mul_assoc, ih, pairDiag_mul_affineLastDot]
    congr 1
    funext w
    rw [inductionLastDot_appendWord_eq_dotE, pow_succ, mul_assoc]

variable {i j}

/-- **The mixed crossing square in the affine algebra** as a polynomial in the two dots:
`c_{ij} c_{ji} = φᵢφⱼ(1) Q_{ji}(φᵢ(y_j), y_i)`. -/
theorem affineLastCrossing_mul_mixed (hij : i ≠ j) :
    affineLastCrossing D Sc i j n * affineLastCrossing D Sc j i n =
      appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc j n 1) *
        pairQuadPoly D Sc j i (appendAlgebra D Sc i (n + 1) (affineLastDot D Sc j n))
          (affineLastDot D Sc i (n + 1)) := by
  rw [affineLastCrossing_mixed D Sc j i hij.symm n]
  have hQ : affinePairQuadratic D Sc j i n = pairDiag D Sc i j n
      (fun w => pairQuadPoly D Sc j i (pairA D Sc i j n w) (pairB D Sc i j n w)) := rfl
  rw [hQ]
  by_cases hd : D.d j i = 0
  · simp only [pairQuadPoly, hd, ↓reduceIte]
    rw [mul_smul_comm, mul_one, appendAlgebra_appendAlgebra_one_eq_pairDiag, ← map_smul]
    rfl
  · have h1 : ∀ p q : ℕ, appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc j n 1) *
        (appendAlgebra D Sc i (n + 1) (affineLastDot D Sc j n) ^ p *
          affineLastDot D Sc i (n + 1) ^ q) =
        pairDiag D Sc i j n (fun w => pairA D Sc i j n w ^ p * pairB D Sc i j n w ^ q) :=
      pairDiag_monomial D Sc i j n
    have h2 := h1 (D.dn j i) 0
    have h3 := h1 0 (D.dn i j)
    simp only [pow_zero, mul_one, one_mul] at h2 h3
    simp only [pairQuadPoly, hd, ↓reduceIte, mul_add, Finset.mul_sum, mul_smul_comm, h1, h2, h3]
    simp only [← map_smul, ← map_sum, ← map_add]
    congr 1
    funext w
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply]

end PairDiag

section Height
open CyclotomicAction
variable (a : I → _root_.Polynomial k) {i j : I}

/-- **The mixed crossing square at every height** of the extended tower:
`c_{ij} c_{ji} = φᵢφⱼ(1) Q_{ji}(φᵢ(y_j), y_i)`. -/
theorem heightLastCrossing_mul_mixed (hij : i ≠ j) (n : ℕ) :
    heightLastCrossing D Sc a i j n * heightLastCrossing D Sc a j i n =
      heightAppend D Sc a i (n + 1) (heightAppend D Sc a j n 1) *
        pairQuadPoly D Sc j i (heightAppend D Sc a i (n + 1) (heightLastDot D Sc a j n))
          (heightLastDot D Sc a i (n + 1)) := by
  cases n with
  | zero =>
    change cyclotomicMk D Sc a 1 (affineLastCrossing D Sc i j 0) *
        cyclotomicMk D Sc a 1 (affineLastCrossing D Sc j i 0) =
      cyclotomicMk D Sc a 1 (appendAlgebra D Sc i 1 (appendAlgebra D Sc j 0 1)) *
        pairQuadPoly D Sc j i
          (cyclotomicMk D Sc a 1 (appendAlgebra D Sc i 1 (affineLastDot D Sc j 0)))
          (cyclotomicMk D Sc a 1 (affineLastDot D Sc i 1))
    rw [← map_pairQuadPoly, ← map_mul, ← map_mul, affineLastCrossing_mul_mixed D Sc 0 hij]
  | succ n =>
    have h1 : heightAppend D Sc a j (n + 1) 1 =
        cyclotomicMk D Sc a (n + 1) (appendAlgebra D Sc j (n + 1) 1) := by
      rw [← map_one (cyclotomicMk D Sc a n)]
      rfl
    rw [h1]
    change cyclotomicMk D Sc a (n + 1 + 1) (affineLastCrossing D Sc i j (n + 1)) *
        cyclotomicMk D Sc a (n + 1 + 1) (affineLastCrossing D Sc j i (n + 1)) =
      cyclotomicMk D Sc a (n + 1 + 1)
          (appendAlgebra D Sc i (n + 1 + 1) (appendAlgebra D Sc j (n + 1) 1)) *
        pairQuadPoly D Sc j i
          (cyclotomicMk D Sc a (n + 1 + 1)
            (appendAlgebra D Sc i (n + 1 + 1) (affineLastDot D Sc j (n + 1))))
          (cyclotomicMk D Sc a (n + 1 + 1) (affineLastDot D Sc i (n + 1 + 1)))
    rw [← map_pairQuadPoly, ← map_mul, ← map_mul,
      affineLastCrossing_mul_mixed D Sc (n + 1) hij]

end Height

end OddMath.QuiverHecke
