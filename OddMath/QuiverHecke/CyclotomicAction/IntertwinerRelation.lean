/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerError

/-!
# Moving-strand annihilation of old cyclotomic relations

`append_relation_move_tmul_zero` is the relation-killing input to the
repeated-colour QP induction. It allows arbitrary old factors on both
sides of the first-position relation, and arbitrary ambient left factors.
Naturality transports the entire old expression, including its parity
involution, before the old relation is killed in the prescribed balanced
coefficient target. No polynomial is commuted through bare crossings.

The coefficients here are ordinary polynomials over the even ground ring.
This does not assert the coefficient-superalgebra extension or the QP formula.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification MulOpposite MonoidalCategory
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Every old quotient-kernel element vanishes after balancing, not just a generator. -/
theorem prepend_kernel_tmul_zero (i : I) (β : Multiset I)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (z : Hn D Sc (n + 1)) (hz : cyclotomicMk D Sc a n z = 0)
    (r : Hn D Sc (n + 1 + 1))
    (b : (qCoefficient D Sc i β a ha n).toSVec) :
    InductionAlong.Ind.tmul
      ((r * prependAlgebra D Sc i (n + 1) z) •
        InductionAlong.unitGen (prependAlgebra D Sc i (n + 1) :
          Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) b = 0 := by
  let φ := (prependAlgebra D Sc i (n + 1) :
    Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
  have he : (r * φ z) • InductionAlong.unitGen φ =
      op z • (r • InductionAlong.unitGen φ) := by
    apply Subtype.ext
    change (r * φ z) * φ 1 = (r * φ 1) * φ z
    rw [mul_assoc, ← map_mul, mul_one, mul_assoc, ← map_mul, one_mul]
  change InductionAlong.Ind.tmul ((r * φ z) • InductionAlong.unitGen φ) b = 0
  rw [he, InductionAlong.Ind.op_smul_tmul]
  have hb : z • b = 0 := by
    change (qCoefficient D Sc i β a ha n).lact (cyclotomicMk D Sc a n z) b = 0
    rw [hz, map_zero]
    rfl
  rw [hb, InductionAlong.Ind.tmul_zero]

/-- Twisting an old first-position relation still gives zero in the old quotient.
Odd polynomial degrees are allowed. -/
theorem cyclotomicMk_twist_generator (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (p : ZMod 2)
    (w : Word I (n + 1)) :
    cyclotomicMk D Sc a n
      (homMatrixTwist D Sc (n + 1) p (cyclotomicGenerator D Sc a w)) = 0 := by
  obtain ⟨q, hq⟩ := cyclotomicGenerator_parity D Sc a ha w
  rw [homMatrixTwist_of_affineParity D Sc _ p q _ hq, map_smul,
    cyclotomicMk_generator, smul_zero]

/-- Both old multipliers are transported by the involution, without homogeneity assumptions. -/
theorem cyclotomicMk_twist_relation (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (p : ZMod 2)
    (w : Word I (n + 1)) (x y : Hn D Sc (n + 1)) :
    cyclotomicMk D Sc a n (homMatrixTwist D Sc (n + 1) p
      (x * cyclotomicGenerator D Sc a w * y)) = 0 := by
  change cyclotomicMk D Sc a n ((homMatrixTwistAlgebra D Sc (n + 1) p)
    (x * cyclotomicGenerator D Sc a w * y)) = 0
  rw [map_mul, map_mul, map_mul, map_mul]
  change cyclotomicMk D Sc a n (homMatrixTwist D Sc (n + 1) p x) *
    cyclotomicMk D Sc a n (homMatrixTwist D Sc (n + 1) p
      (cyclotomicGenerator D Sc a w)) *
    cyclotomicMk D Sc a n (homMatrixTwist D Sc (n + 1) p y) = 0
  rw [cyclotomicMk_twist_generator D Sc a ha, mul_zero, zero_mul]

/-- Affine factorization through the shifted old expression, retaining the entire twist. -/
theorem append_move_factor (i : I) (n : ℕ) (β : Multiset I)
    (z : Hn D Sc n) :
    appendAlgebra D Sc i n z * contentMove D Sc i n β =
      contentMove D Sc i n β * prependAlgebra D Sc i n
        (homMatrixTwist D Sc n (D.parity i * contentSumParity D β) z) := by
  have h := contentMove_balance D Sc i n β
    (homMatrixTwist D Sc n (D.parity i * contentSumParity D β) z)
  rw [homMatrixTwist_twice] at h
  exact h

/-- All-prefix relation killing in the target of `parityCyclotomicContentQ`.
The old right factor can be any crossing prefix (or an arbitrary inhomogeneous element).
The polynomial is the first-position relation of the intermediate old word `w`,
so its prepend image acts at old position two, not on the moving first strand. -/
theorem append_relation_move_tmul_zero (i : I) (β : Multiset I)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (w : Word I (n + 1)) (x y : Hn D Sc (n + 1))
    (r : Hn D Sc (n + 1 + 1))
    (b : (qCoefficient D Sc i β a ha n).toSVec) :
    InductionAlong.Ind.tmul
      ((r * (appendAlgebra D Sc i (n + 1)
          (x * cyclotomicGenerator D Sc a w * y) * contentMove D Sc i (n + 1) β)) •
        InductionAlong.unitGen (prependAlgebra D Sc i (n + 1) :
          Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) b = 0 := by
  rw [append_move_factor, ← mul_assoc]
  exact prepend_kernel_tmul_zero D Sc i β a ha n _
    (cyclotomicMk_twist_relation D Sc a ha n _ w x y) _ b

/-- Selecting a source word in the moving-strand sum gives its typed representative. -/
theorem append_entry_mul_contentMove (i : I) {n : ℕ} (β : Multiset I)
    (s t : Word I n) (hs : wordContent s = β)
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    appendAlgebra D Sc i n (FiniteHomMatrix.single t s f) * contentMove D Sc i n β =
      FiniteHomMatrix.single (appendWord i t) (prependWord i s)
        (moveHom D Sc i [] s.1 ≫ appendHom D Sc i s t f) := by
  change appendLinear D Sc i n (FiniteHomMatrix.single t s f) * contentMove D Sc i n β =
    FiniteHomMatrix.single (appendWord i t) (prependWord i s)
      (moveHom D Sc i [] s.1 ≫ appendHom D Sc i s t f)
  rw [appendLinear_single, contentMove, Finset.mul_sum, Finset.sum_eq_single s]
  · simp
  · intro w _ hw
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hw (appendWord_injective i n h.symm)) _ _
  · simp [hs]

/-- The typed all-prefix relation-killing representative. The morphism `f` may be
any old crossing prefix, including the empty prefix, or any inhomogeneous old
morphism. For the repeated-colour step take `s = ν` and `t = i :: ν.dropLast`:
`f` brings the final old `i` to the first old position. The left generator is
then precisely `f_i(x₁)`, while the proof kills its transported old relation at
position two in the balanced target. -/
theorem prefix_relation_move_tmul_zero (i : I) (β : Multiset I)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (s t : Word I (n + 1)) (hs : wordContent s = β)
    (f : wordObj D Sc s ⟶ wordObj D Sc t)
    (r : Hn D Sc (n + 1 + 1))
    (b : (qCoefficient D Sc i β a ha n).toSVec) :
    InductionAlong.Ind.tmul
      ((r * (cyclotomicGenerator D Sc a (appendWord i t) *
          FiniteHomMatrix.single (appendWord i t) (prependWord i s)
            (moveHom D Sc i [] s.1 ≫ appendHom D Sc i s t f))) •
        InductionAlong.unitGen (prependAlgebra D Sc i (n + 1) :
          Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) b = 0 := by
  have h := append_relation_move_tmul_zero D Sc i β a ha n t 1
    (FiniteHomMatrix.single t s f) r b
  rw [one_mul, map_mul, appendAlgebra_generator, mul_assoc,
    append_entry_mul_contentMove D Sc i β s t hs f] at h
  exact h

/-- The bare crossing prefix taking the last strand to the first position.
Its execution order is rightmost crossing first, so algebraically it is
`τ₁ ⋯ τₙ` on a word of length `n + 1`. -/
def lastToFirstHom (i : I) : (ν : List I) →
    (pres D Sc).obj (ob D (ν ++ [i])) ⟶ (pres D Sc).obj (ob D (i :: ν))
  | [] => 𝟙 _
  | j :: ν =>
      ((pres D Sc).obj (ob D [j]) ◁ lastToFirstHom i ν) ≫
        cl D Sc (j :: i :: ν) (i :: j :: ν) [.cross 0]
          (by simpa using sChain_crossAt [] ν j i)

/-- The repeated-colour all-prefix identity (K): `f_i(x₁) Tₙ Vₙ₊₁`
vanishes in the prescribed balanced target, for every finite prefix `ν`.
There are no restrictions on repetitions or spectator parities; `ν = []`
is the minimal prefix. -/
theorem allPrefix_relation_tmul_zero (i : I) (ν : List I)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)
    (r : Hn D Sc (ν.length + 1 + 1))
    (b : (qCoefficient D Sc i (↑(ν ++ [i]) : Multiset I) a ha ν.length).toSVec) :
    let s : Word I (ν.length + 1) := ⟨ν ++ [i], by simp⟩
    let t : Word I (ν.length + 1) := ⟨i :: ν, by simp⟩
    InductionAlong.Ind.tmul
      ((r * (cyclotomicGenerator D Sc a (appendWord i t) *
          FiniteHomMatrix.single (appendWord i t) (prependWord i s)
            (moveHom D Sc i [] s.1 ≫ appendHom D Sc i s t (lastToFirstHom D Sc i ν)))) •
        InductionAlong.unitGen (prependAlgebra D Sc i (ν.length + 1) :
          Hn D Sc (ν.length + 1) →ₙ+* Hn D Sc (ν.length + 1 + 1))) b = 0 := by
  dsimp only
  exact prefix_relation_move_tmul_zero D Sc i _ a ha ν.length
    ⟨ν ++ [i], by simp⟩ ⟨i :: ν, by simp⟩ rfl (lastToFirstHom D Sc i ν) r b

end OddMath.QuiverHecke
