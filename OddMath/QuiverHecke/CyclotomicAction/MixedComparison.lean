/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Comparison
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

/-!
# Mixed quadratic comparison on cyclotomic composition corners

Ports the algebraic comparison input of
`Categorification/KLR/CyclotomicAction/MixedComparison.lean` and the quadratic
calculation of `Categorification/KLR/CyclotomicAction/Square.lean`.
The quotient element on the right is the explicit polynomial in the two
positioned dots, not a freely specified square. Signed right multiplication
introduces the super-opposite sign. This is an upward quadratic comparison;
it does not assert the mixed induction–restriction Mackey isomorphism.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- The explicit two-colour quadratic polynomial evaluated in a word endomorphism ring. -/
def wordQuadratic (i j : I) (t : List I) (r : ℕ) : End ((pres D Sc).obj (ob D t)) :=
  if D.d i j = 0 then (Sc.t i j : k) • 1 else
    ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
      Sc.s i j p q • (dotE D Sc t r ^ p * dotE D Sc t (r + 1) ^ q) +
      ((Sc.t i j : k) • dotE D Sc t r ^ D.dn i j +
        (Sc.t j i : k) • dotE D Sc t (r + 1) ^ D.dn j i)

/-- The double crossing equals the actual polynomial on each last-pair word. -/
theorem inductionLastCrossing_mixed (i j : I) (hij : i ≠ j) {n : ℕ} (w : Word I n) :
    inductionLastCrossing D Sc i j w ≫ inductionLastCrossing D Sc j i w =
      wordQuadratic D Sc i j (appendWord j (appendWord i w)).1 w.1.length := by
  rw [inductionLastCrossing_eq_cl, inductionLastCrossing_eq_cl, cl_comp]
  have aux {t : List I} (ht : t = w.1 ++ [i,j] ++ [])
      (h : SChain t (pl t [.cross w.1.length, .cross w.1.length]) t) :
      cl D Sc t t [.cross w.1.length, .cross w.1.length] h =
        wordQuadratic D Sc i j t w.1.length := by
    subst t
    unfold wordQuadratic
    split_ifs with hd
    · exact cross_cross_ne_zero D Sc w.1 [] hij hd h
    · exact cross_cross_ne D Sc w.1 [] hij hd h
  exact aux (by simp [appendWord, List.append_assoc]) _

variable [Fintype I]

/-- Sum the displayed quadratic polynomial over the old-word corners. -/
def affinePairQuadratic (i j : I) (n : ℕ) : Hn D Sc (n + 1 + 1) :=
  ∑ w : Word I n, FiniteHomMatrix.single (appendWord j (appendWord i w))
    (appendWord j (appendWord i w))
    (wordQuadratic D Sc i j (appendWord j (appendWord i w)).1 w.1.length)

/-- Mixed crossing square in the affine algebra, with no change of parameters yet. -/
theorem affineLastCrossing_mixed (i j : I) (hij : i ≠ j) (n : ℕ) :
    affineLastCrossing D Sc j i n * affineLastCrossing D Sc i j n =
      affinePairQuadratic D Sc i j n := by
  simp only [affineLastCrossing, affinePairQuadratic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_mul, Finset.sum_eq_single w]
  · rw [FiniteHomMatrix.single_mul_single, inductionLastCrossing_mixed D Sc i j hij]
  · intro b _ hb
    apply FiniteHomMatrix.single_mul_single_of_ne
    intro h
    exact hb (appendWord_injective j n (appendWord_injective i (n + 1) h))
  · simp

/-- The explicit quadratic element in the specified cyclotomic quotient. -/
def cyclotomicPairQuadratic (i j : I) (a : I → _root_.Polynomial k) (n : ℕ) :
    CyclotomicAlgebra D Sc a (n + 1 + 1) :=
  cyclotomicMk D Sc a (n + 1 + 1) (affinePairQuadratic D Sc i j (n + 1))

/-- Mixed crossing square in the concrete cyclotomic quotient. -/
theorem cyclotomicLastCrossing_mixed (i j : I) (hij : i ≠ j)
    (a : I → _root_.Polynomial k) (n : ℕ) :
    cyclotomicLastCrossing D Sc j i a n * cyclotomicLastCrossing D Sc i j a n =
      cyclotomicPairQuadratic D Sc i j a n := by
  simp only [cyclotomicLastCrossing, cyclotomicPairQuadratic, ← map_mul]
  rw [affineLastCrossing_mixed D Sc i j hij]

/-- The sign of two homogeneous right multipliers is independent of their input parity. -/
theorem crossing_square_sign (p d : ZMod 2) :
    koszulSign (p + d) d * koszulSign p d = koszulSign d d := by
  rw [koszulSign_add_left, mul_right_comm, koszulSign_mul_self, one_mul]

/-- On the actual corner superbimodules the mixed square has the super-opposite sign. -/
theorem compositionSuperCrossing_mixed_apply (i j : I) (hij : i ≠ j)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    {p : ZMod 2} (x : (compositionCorner D Sc i j a ha n).toSVec)
    (hx : x ∈ (compositionCorner D Sc i j a ha n).toSVec.part p) :
    ((compositionSuperCrossing D Sc j i a ha n).1
      ((compositionSuperCrossing D Sc i j a ha n).1 x)).val =
      koszulSign (D.parity i * D.parity j) (D.parity i * D.parity j) •
        (x.val * cyclotomicPairQuadratic D Sc j i a n) := by
  have hf : (compositionSuperCrossing D Sc i j a ha n).1 x ∈
      (compositionCorner D Sc j i a ha n).toSVec.part (p + D.parity i * D.parity j) :=
    SVec.apply_mem_part (compositionCrossingLinear_parity D Sc i j a ha n) hx
  erw [compositionSuperCrossing_apply D Sc j i a ha n _ hf,
    compositionSuperCrossing_apply D Sc i j a ha n x hx]
  rw [smul_mul_assoc, smul_smul, mul_comm (D.parity j) (D.parity i), crossing_square_sign,
    mul_assoc, cyclotomicLastCrossing_mixed D Sc j i hij.symm]

end OddMath.QuiverHecke
