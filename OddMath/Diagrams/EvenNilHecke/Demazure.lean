import OddMath.Diagrams.EvenNilHecke.Presented
import OddMath.Frontier.EKLGapsZeroHecke

/-!
# Even Demazure products and divided-power idempotents

BE2, arXiv:1701.04133v2, §11, the idempotents preceding Lemma 11.1.
We use the classical nilHecke presentation within OddMath. Its Demazure
generator is `-T X_right`, with no odd correction. Reduced-word independence
uses the same monoid-valued Matsumoto theorem as the odd nilHecke algebra.
This module constructs idempotents, not the factorial decomposition.
-/

namespace OddMath.EvenNilHecke
open Frontier NilCoxeterWords
noncomputable section
variable {n : ℕ}

/-- The complementary Demazure generator `X_left T`. -/
def zeroHecke (n : ℕ) (i : Fin (n + 1)) : Presented n := dot n i.castSucc * crossing n i

theorem crossing_mul_zeroHecke (i : Fin (n + 1)) :
    crossing n i * zeroHecke n i = crossing n i := by
  rw [zeroHecke, ← mul_assoc, crossing_dot_left, add_mul, one_mul, mul_assoc,
    crossing_square, mul_zero, zero_add]

theorem zeroHecke_sq (i : Fin (n + 1)) : zeroHecke n i * zeroHecke n i = zeroHecke n i := by
  change dot n i.castSucc * crossing n i * zeroHecke n i = _
  rw [mul_assoc, crossing_mul_zeroHecke]
  rfl

theorem zeroHecke_distant (i j : Fin (n + 1))
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    zeroHecke n i * zeroHecke n j = zeroHecke n j * zeroHecke n i := by
  have ne (a b : Fin (n + 1)) (hab : a.val + 1 < b.val ∨ b.val + 1 < a.val) :
      b.castSucc ≠ a.castSucc ∧ b.castSucc ≠ a.succ := by
    constructor <;> intro e <;> have hv := congrArg Fin.val e <;>
      simp only [Fin.val_castSucc, Fin.val_succ] at hv <;> omega
  have key (a b : Fin (n + 1)) (hab : a.val + 1 < b.val ∨ b.val + 1 < a.val) :
      zeroHecke n a * zeroHecke n b =
        dot n a.castSucc * dot n b.castSucc * (crossing n a * crossing n b) := by
    simp only [zeroHecke, mul_assoc]
    rw [← mul_assoc (crossing n a), crossing_dot_other a b.castSucc (ne a b hab).1
      (ne a b hab).2, mul_assoc]
  rw [key i j h, key j i (by omega), dots_commute i.castSucc j.castSucc,
    crossing_distant i j h]

theorem zeroHecke_braid (i j : Fin (n + 1)) (h : j.val = i.val + 1) :
    zeroHecke n i * zeroHecke n j * zeroHecke n i =
      zeroHecke n j * zeroHecke n i * zeroHecke n j := by
  have hij : j.castSucc = i.succ := Fin.ext (by simp [h])
  have h1 : ∀ x, crossing n j * (dot n i.castSucc * x) =
      dot n i.castSucc * (crossing n j * x) := by
    intro x
    have hl : i.castSucc ≠ j.castSucc := by
      intro e; have hv := congrArg Fin.val e; simp only [Fin.val_castSucc] at hv; omega
    have hr : i.castSucc ≠ j.succ := by
      intro e; have hv := congrArg Fin.val e
      simp only [Fin.val_castSucc, Fin.val_succ] at hv; omega
    rw [← mul_assoc, crossing_dot_other j _ hl hr, mul_assoc]
  have h2 : ∀ x, crossing n i * (dot n i.castSucc * x) =
      dot n i.succ * (crossing n i * x) + x := by
    intro x; rw [← mul_assoc, crossing_dot_left, add_mul, one_mul, mul_assoc]
  have h3 : ∀ x, crossing n i * (dot n i.succ * x) =
      dot n i.castSucc * (crossing n i * x) - x := by
    intro x; rw [← mul_assoc, crossing_dot_right, sub_mul, one_mul, mul_assoc]
  have h4 : ∀ x, dot n i.succ * (dot n i.castSucc * x) =
      dot n i.castSucc * (dot n i.succ * x) := by
    intro x; rw [← mul_assoc, dots_commute i.succ i.castSucc, mul_assoc]
  have h6 : crossing n j * (crossing n i * crossing n j) =
      crossing n i * (crossing n j * crossing n i) := by
    simpa only [mul_assoc] using (crossing_braid i j h).symm
  simp only [zeroHecke, hij, mul_assoc, h1, h2, h3, h4, h6, mul_sub, sub_mul,
    mul_add, add_mul, mul_zero, crossing_square]
  abel

/-- BE2's even-colour Demazure generator, with the source's sign. -/
def demazure (n : ℕ) (i : Fin (n + 1)) : Presented n := -(crossing n i * dot n i.succ)

theorem demazure_eq_complement (i : Fin (n + 1)) :
    demazure n i = 1 - zeroHecke n i := by
  rw [demazure, crossing_dot_right, zeroHecke]
  abel

theorem demazure_sq (i : Fin (n + 1)) : demazure n i * demazure n i = demazure n i := by
  rw [demazure_eq_complement]
  noncomm_ring [zeroHecke_sq i]

theorem demazure_braid (i j : Fin (n + 1)) (h : j.val = i.val + 1) :
    demazure n i * demazure n j * demazure n i =
      demazure n j * demazure n i * demazure n j := by
  simp only [demazure_eq_complement]
  noncomm_ring [zeroHecke_sq i, zeroHecke_sq j, zeroHecke_braid i j h]

theorem demazure_distant (i j : Fin (n + 1))
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    demazure n i * demazure n j = demazure n j * demazure n i := by
  simp only [demazure_eq_complement]
  noncomm_ring [zeroHecke_distant i j h]

/-- The written product along a word. -/
def demazureProduct (w : Word n) : Presented n := EKLGaps.wordProd (demazure n) w

theorem demazureProduct_reduced_eq (w v : Word n) (hw : Reduced w) (hv : Reduced v)
    (hp : permutation w = permutation v) : demazureProduct w = demazureProduct v :=
  EKLGaps.wordProd_reduced_eq demazure_braid demazure_distant w v hw hv hp

/-- The longest Demazure product. -/
def projector (n : ℕ) : Presented n :=
  demazureProduct (LongestDivided.wordIn n (n + 2) le_rfl)

theorem projector_eq_of_reduced (w : Word n) (hw : Reduced w)
    (hp : permutation w = LongestElementary.longest (n + 2)) :
    projector n = demazureProduct w :=
  demazureProduct_reduced_eq _ w (sourceWord_reduced n) hw
    ((sourceWord_permutation n).trans hp.symm)

theorem projector_mul_demazure (i : Fin (n + 1)) :
    projector n * demazure n i = projector n := by
  obtain ⟨w, hr, hp⟩ := ZeroHecke.exists_reduced_ending' i
  rw [projector_eq_of_reduced _ hr hp, demazureProduct, EKLGaps.wordProd_append,
    EKLGaps.wordProd_singleton, mul_assoc, demazure_sq]

theorem demazure_mul_projector (i : Fin (n + 1)) :
    demazure n i * projector n = projector n := by
  obtain ⟨w, hr, hp⟩ := ZeroHecke.exists_reduced_starting i
  rw [projector_eq_of_reduced _ hr hp, demazureProduct, EKLGaps.wordProd_cons,
    ← mul_assoc, demazure_sq]

theorem projector_mul_product (w : Word n) :
    projector n * demazureProduct w = projector n := by
  induction w with
  | nil => exact mul_one _
  | cons i w ih =>
    change projector n * (demazure n i * demazureProduct w) = _
    rw [← mul_assoc, projector_mul_demazure, ih]

/-- BE2 §11: the even longest Demazure element is idempotent in every rank ≥ 2. -/
theorem projector_idempotent (n : ℕ) : projector n * projector n = projector n :=
  projector_mul_product _

/-- Universality transports the actual projector, rather than assuming a target idempotent. -/
theorem map_projector_idempotent {A : Type*} [Ring A] (f : Presented n →+* A) :
    f (projector n) * f (projector n) = f (projector n) := by
  rw [← map_mul, projector_idempotent]

end
end OddMath.EvenNilHecke
