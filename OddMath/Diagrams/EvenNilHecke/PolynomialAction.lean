import OddMath.Diagrams.EvenNilHecke.Polynomial
import OddMath.Diagrams.EvenNilHecke.Demazure

/-!
# The even nilHecke action on ordinary polynomials

BE2, arXiv:1701.04133v2, §11 before Lemma 11.1. The integral presented
nilHecke algebra acts on polynomials over any commutative ring. The longest
Demazure idempotent fixes the constant polynomial and is consequently nonzero
in every rank. No faithfulness or factorial splitting is asserted here.
-/

namespace OddMath.EvenNilHecke

open MvPolynomial Equiv OddMath.EvenNilHecke.Polynomial

noncomputable section
variable {k : Type*} [CommRing k] {n : ℕ}

private theorem adjacent_ne (i : Fin (n + 1)) : i.castSucc ≠ i.succ := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ] at this
  omega

/-- Multiplication by a polynomial variable. -/
def polynomialDot (k : Type*) [CommRing k] (n : ℕ) (j : Fin (n + 2)) :
    Module.End k (MvPolynomial (Fin (n + 2)) k) := LinearMap.mulLeft k (X j)

/-- The ordinary divided difference for adjacent variables. -/
def polynomialCrossing (k : Type*) [CommRing k] (n : ℕ) (i : Fin (n + 1)) :
    Module.End k (MvPolynomial (Fin (n + 2)) k) := ddiff i.castSucc i.succ

private theorem square_operator (i : Fin (n + 1)) :
    polynomialCrossing k n i * polynomialCrossing k n i = 0 := by
  apply LinearMap.ext; intro f
  exact ddiff_ddiff (adjacent_ne i) f

private theorem braid_operator (i j : Fin (n + 1)) (h : j.val = i.val + 1) :
    polynomialCrossing k n i * polynomialCrossing k n j * polynomialCrossing k n i =
      polynomialCrossing k n j * polynomialCrossing k n i * polynomialCrossing k n j := by
  have hij : j.castSucc = i.succ := Fin.ext (by simpa using h)
  have hac : i.castSucc ≠ j.succ := by
    intro e
    have := congrArg Fin.val e
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  apply LinearMap.ext; intro f
  change ddiff i.castSucc i.succ (ddiff j.castSucc j.succ (ddiff i.castSucc i.succ f)) =
    ddiff j.castSucc j.succ (ddiff i.castSucc i.succ (ddiff j.castSucc j.succ f))
  rw [hij]
  exact ddiff_braid (adjacent_ne i) (hij ▸ adjacent_ne j) hac f

private theorem dots_operator (i j : Fin (n + 2)) :
    polynomialDot k n i * polynomialDot k n j = polynomialDot k n j * polynomialDot k n i := by
  apply LinearMap.ext; intro f
  exact mul_left_comm _ _ _

private theorem distant_operator (i j : Fin (n + 1))
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    polynomialCrossing k n i * polynomialCrossing k n j =
      polynomialCrossing k n j * polynomialCrossing k n i := by
  have ne (a b : Fin (n + 2)) (hab : a.val ≠ b.val) : a ≠ b :=
    fun e => hab (congrArg Fin.val e)
  apply LinearMap.ext; intro f
  exact ddiff_ddiff_comm (adjacent_ne i) (adjacent_ne j)
    (ne _ _ (by simp only [Fin.val_castSucc]; omega))
    (ne _ _ (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
    (ne _ _ (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
    (ne _ _ (by simp only [Fin.val_succ]; omega)) f

private theorem mixedRight_operator (i : Fin (n + 1)) :
    polynomialDot k n i.castSucc * polynomialCrossing k n i -
      polynomialCrossing k n i * polynomialDot k n i.succ = 1 := by
  apply LinearMap.ext; intro f
  change X i.castSucc * ddiff i.castSucc i.succ f -
    ddiff i.castSucc i.succ (X i.succ * f) = f
  rw [ddiff_mul (adjacent_ne i), ddiff_X_right (adjacent_ne i), rename_X, swap_apply_right]
  ring

private theorem mixedLeft_operator (i : Fin (n + 1)) :
    polynomialCrossing k n i * polynomialDot k n i.castSucc -
      polynomialDot k n i.succ * polynomialCrossing k n i = 1 := by
  apply LinearMap.ext; intro f
  change ddiff i.castSucc i.succ (X i.castSucc * f) -
    X i.succ * ddiff i.castSucc i.succ f = f
  rw [ddiff_mul (adjacent_ne i), ddiff_X_left (adjacent_ne i), rename_X, swap_apply_left]
  ring

private theorem spectator_operator (i : Fin (n + 1)) (j : Fin (n + 2))
    (hl : j ≠ i.castSucc) (hr : j ≠ i.succ) :
    polynomialCrossing k n i * polynomialDot k n j =
      polynomialDot k n j * polynomialCrossing k n i := by
  apply LinearMap.ext; intro f
  exact ddiff_mul_of_rename_eq (adjacent_ne i) (g := X j)
    (by rw [rename_X, swap_apply_of_ne_of_ne hl hr]) f

/-- Dot and crossing operators with the integral presentation's conventions. -/
def polynomialFamily (k : Type*) [CommRing k] (n : ℕ) :
    Family n (Module.End k (MvPolynomial (Fin (n + 2)) k)) where
  x := polynomialDot k n
  t := polynomialCrossing k n
  square := square_operator
  braid := braid_operator
  dots := dots_operator
  distant := distant_operator
  mixedRight := mixedRight_operator
  mixedLeft := mixedLeft_operator
  spectator := spectator_operator

/-- The action is induced from the seven presentation relations, over any coefficients. -/
def polynomialAction (k : Type*) [CommRing k] (n : ℕ) :
    Presented n →+* Module.End k (MvPolynomial (Fin (n + 2)) k) :=
  (polynomialFamily k n).lift

@[simp] theorem polynomialAction_dot (j : Fin (n + 2)) (f : MvPolynomial (Fin (n + 2)) k) :
    polynomialAction k n (dot n j) f = X j * f := by
  simp only [polynomialAction, Family.lift_dot, polynomialFamily, polynomialDot,
    LinearMap.mulLeft_apply]

@[simp] theorem polynomialAction_crossing (i : Fin (n + 1))
    (f : MvPolynomial (Fin (n + 2)) k) :
    polynomialAction k n (crossing n i) f = ddiff i.castSucc i.succ f := by
  simp only [polynomialAction, Family.lift_crossing, polynomialFamily, polynomialCrossing]

/-- BE2's negative even generator fixes constants. -/
@[simp] theorem polynomialAction_demazure_one (i : Fin (n + 1)) :
    polynomialAction k n (demazure n i) 1 = 1 := by
  simp only [demazure, map_neg, map_mul, LinearMap.neg_apply, Module.End.mul_apply,
    polynomialAction_dot, mul_one, polynomialAction_crossing,
    ddiff_X_right (adjacent_ne i), neg_neg]

@[simp] theorem polynomialAction_product_one (w : Frontier.NilCoxeterWords.Word n) :
    polynomialAction k n (demazureProduct w) 1 = 1 := by
  induction w with
  | nil => simp [demazureProduct, Frontier.EKLGaps.wordProd]
  | cons i w ih =>
    change polynomialAction k n (demazure n i * demazureProduct w) 1 = 1
    rw [map_mul, Module.End.mul_apply, ih, polynomialAction_demazure_one]

@[simp] theorem polynomialAction_projector_one :
    polynomialAction k n (projector n) 1 = 1 := polynomialAction_product_one _

/-- The longest idempotent is nonzero in every rank, as detected over the integers. -/
theorem projector_ne_zero (n : ℕ) : projector n ≠ 0 := by
  intro h
  have he := polynomialAction_projector_one (k := ℤ) (n := n)
  rw [h, map_zero, LinearMap.zero_apply] at he
  exact zero_ne_one he

instance presentedNontrivial (n : ℕ) : Nontrivial (Presented n) :=
  ⟨⟨projector n, 0, projector_ne_zero n⟩⟩

#print axioms polynomialAction
#print axioms projector_ne_zero

end
end OddMath.EvenNilHecke
