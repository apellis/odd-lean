import OddMath.Frontier.DividedDistant
import OddMath.Frontier.DividedBraid

/-! # The genuine presented odd nilHecke ring and its natural action
EKL arXiv:1111.1320v1, Proposition 2.1 (2.7)–(2.10), §2.2.
Rank is n+2. Endomorphism multiplication is composition: the left factor acts last.
No faithfulness, nilHecke basis, or grading theorem is asserted here.
-/
namespace OddMath.Frontier.NilHeckeAction
open OddMath.SkewPolynomial (SkewPolynomial generator)
open PbwL3 AllRankDivided

abbrev Gen (n : ℕ) := Sum (Fin (n+2)) (Fin (n+1))
abbrev Free (n : ℕ) := FreeAlgebra ℤ (Gen n)

def dotFree (n : ℕ) (j : Fin (n+2)) : Free n := FreeAlgebra.ι ℤ (Sum.inl j)
def crossingFree (n : ℕ) (i : Fin (n+1)) : Free n := FreeAlgebra.ι ℤ (Sum.inr i)

/-- Exactly seven source families; only the displayed index conditions occur. -/
inductive Relator (n : ℕ) : Free n → Prop
  | square (i : Fin (n+1)) : Relator n (crossingFree n i * crossingFree n i)
  | braid (i j : Fin (n+1)) (h : j.val = i.val+1) :
      Relator n (crossingFree n i * crossingFree n j * crossingFree n i -
        crossingFree n j * crossingFree n i * crossingFree n j)
  | dots (i j : Fin (n+2)) (h : i ≠ j) :
      Relator n (dotFree n i * dotFree n j + dotFree n j * dotFree n i)
  | distant (i j : Fin (n+1)) (h : i.val+1<j.val ∨ j.val+1<i.val) :
      Relator n (crossingFree n i * crossingFree n j + crossingFree n j * crossingFree n i)
  | mixedRight (i : Fin (n+1)) :
      Relator n (dotFree n i.castSucc * crossingFree n i +
        crossingFree n i * dotFree n i.succ - 1)
  | mixedLeft (i : Fin (n+1)) :
      Relator n (crossingFree n i * dotFree n i.castSucc +
        dotFree n i.succ * crossingFree n i - 1)
  | spectator (i : Fin (n+1)) (j : Fin (n+2))
      (hl : j ≠ i.castSucc) (hr : j ≠ i.succ) :
      Relator n (dotFree n j * crossingFree n i + crossingFree n i * dotFree n j)

def relSet (n : ℕ) : Set (Free n) := {w | Relator n w}
def relTwoSided (n : ℕ) : TwoSidedIdeal (Free n) := TwoSidedIdeal.span (relSet n)
def relIdeal (n : ℕ) : Ideal (Free n) := (relTwoSided n).asIdeal
instance relIdealTwoSided (n : ℕ) : (relIdeal n).IsTwoSided :=
  inferInstanceAs ((relTwoSided n).asIdeal.IsTwoSided)

def Presented (n : ℕ) : Type := Free n ⧸ relIdeal n
instance presentedRing (n : ℕ) : Ring (Presented n) := Ideal.Quotient.ring (relIdeal n)

def dot (n : ℕ) (j : Fin (n+2)) : Presented n := Ideal.Quotient.mk (relIdeal n) (dotFree n j)
def crossing (n : ℕ) (i : Fin (n+1)) : Presented n :=
  Ideal.Quotient.mk (relIdeal n) (crossingFree n i)

noncomputable def dotOperator (n : ℕ) (j : Fin (n+2)) : Module.End ℤ (SkewPolynomial (n+2)) :=
  LinearMap.mulLeft ℤ (generator j)

noncomputable def freeAction (n : ℕ) : Free n →ₐ[ℤ] Module.End ℤ (SkewPolynomial (n+2)) :=
  FreeAlgebra.lift ℤ (Sum.elim (dotOperator n) (fun i => divided i))

@[simp] theorem freeAction_dot (n : ℕ) (j : Fin (n+2)) :
    freeAction n (dotFree n j) = dotOperator n j := by
  simp [freeAction, dotFree]

@[simp] theorem freeAction_crossing (n : ℕ) (i : Fin (n+1)) :
    freeAction n (crossingFree n i) = divided i := by
  simp [freeAction, crossingFree]

@[simp] theorem dotOperator_apply (n : ℕ) (j : Fin (n+2)) (f : SkewPolynomial (n+2)) :
    dotOperator n j f = generator j * f := rfl

/-- Multiplication is composition: v acts first, u acts last. -/
theorem end_mul_apply (n : ℕ) (u v : Module.End ℤ (SkewPolynomial (n+2)))
    (f : SkewPolynomial (n+2)) : (u*v) f = u (v f) := rfl

/-- Re-index the genuine parent braid, including the empty rank-two case. -/
theorem divided_braid_adjacent (n : ℕ) (i j : Fin (n+1)) (h : j.val = i.val+1)
    (f : SkewPolynomial (n+2)) :
    divided i (divided j (divided i f)) = divided j (divided i (divided j f)) := by
  cases n with
  | zero => have hi := i.isLt; have hj := j.isLt; omega
  | succ m =>
      let k : Fin (m+1) := ⟨i.val, by have hj := j.isLt; omega⟩
      have hi : k.castSucc = i := Fin.ext rfl
      have hj : k.succ = j := Fin.ext (by simpa [k] using h.symm)
      rw [← hi, ← hj]
      exact DividedBraid.divided_braid k f

/-- Every source relator is killed on every actual skew polynomial. -/
theorem relation_killed (n : ℕ) (w : Free n) (hw : w ∈ relSet n) :
    freeAction n w = 0 := by
  change Relator n w at hw
  cases hw with
  | square i =>
      simp only [map_mul, freeAction_crossing]
      exact DividedSquareZero.divided_comp_self i
  | braid i j h =>
      simp only [map_sub, map_mul, freeAction_crossing, sub_eq_zero]
      apply LinearMap.ext
      intro f
      exact divided_braid_adjacent n i j h f
  | dots i j h =>
      simp only [map_add, map_mul, freeAction_dot]
      apply LinearMap.ext
      intro f
      change generator i * (generator j * f) + generator j * (generator i * f) = 0
      rw [← mul_assoc, ← mul_assoc, ← add_mul]
      rw [show generator i * generator j + generator j * generator i = 0 from
        PbwL1.rel_sum i j h, zero_mul]
  | distant i j h =>
      simp only [map_add, map_mul, freeAction_crossing]
      exact DividedDistant.divided_distant_comp i j h
  | mixedRight i =>
      simp only [map_sub, map_add, map_mul, map_one, freeAction_dot, freeAction_crossing]
      apply LinearMap.ext
      intro f
      change generator i.castSucc * divided i f + divided i (generator i.succ * f) - f = 0
      rw [divided_right_mul]
      abel
  | mixedLeft i =>
      simp only [map_sub, map_add, map_mul, map_one, freeAction_dot, freeAction_crossing]
      apply LinearMap.ext
      intro f
      change divided i (generator i.castSucc * f) + generator i.succ * divided i f - f = 0
      rw [divided_left_mul]
      abel
  | spectator i j hl hr =>
      simp only [map_add, map_mul, freeAction_dot, freeAction_crossing]
      apply LinearMap.ext
      intro f
      change generator j * divided i f + divided i (generator j * f) = 0
      rw [divided_spectator_mul i j hl hr, neg_mul, add_neg_cancel]

/-- Killing generators extends to the entire actual two-sided ideal, by induction. -/
theorem ideal_killed (n : ℕ) (w : Free n) (hw : w ∈ relIdeal n) :
    freeAction n w = 0 := by
  rw [relIdeal, relTwoSided, TwoSidedIdeal.mem_asIdeal] at hw
  induction hw using TwoSidedIdeal.span_induction with
  | mem x h => exact relation_killed n x h
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | neg x hx ih => rw [map_neg, ih, neg_zero]
  | left_absorb a x hx ih => rw [map_mul, ih, mul_zero]
  | right_absorb b x hx ih => rw [map_mul, ih, zero_mul]

noncomputable def action (n : ℕ) : Presented n →+* Module.End ℤ (SkewPolynomial (n+2)) :=
  Ideal.Quotient.lift (relIdeal n) (freeAction n).toRingHom (ideal_killed n)

/-- Exact descent equality for every element of the free algebra, not just letters. -/
@[simp] theorem action_mk (n : ℕ) (w : Free n) :
    action n (Ideal.Quotient.mk (relIdeal n) w) = freeAction n w := rfl

@[simp] theorem action_dot (n : ℕ) (j : Fin (n+2)) :
    action n (dot n j) = dotOperator n j := freeAction_dot n j

@[simp] theorem action_crossing (n : ℕ) (i : Fin (n+1)) :
    action n (crossing n i) = divided i := freeAction_crossing n i

theorem action_dot_apply (n : ℕ) (j : Fin (n+2)) (f : SkewPolynomial (n+2)) :
    action n (dot n j) f = generator j * f := by rw [action_dot, dotOperator_apply]

theorem action_crossing_apply (n : ℕ) (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    action n (crossing n i) f = divided i f := by rw [action_crossing]

/-- Arbitrary quotient products act in the same checked orientation. -/
theorem action_mul_apply (n : ℕ) (a b : Presented n) (f : SkewPolynomial (n+2)) :
    action n (a*b) f = action n a (action n b f) := by rw [map_mul]; rfl

/-- Arbitrary free-word products, on arbitrary inputs. -/
theorem action_word_product (n : ℕ) (u v : Free n) (f : SkewPolynomial (n+2)) :
    action n (Ideal.Quotient.mk (relIdeal n) (u*v)) f = freeAction n u (freeAction n v f) := by
  rw [action_mk, map_mul]
  rfl

theorem action_dot_one (n : ℕ) (j : Fin (n+2)) :
    action n (dot n j) 1 = generator j := by rw [action_dot_apply, mul_one]

theorem generator_ne_zero (n : ℕ) (j : Fin (n+2)) : (generator j : SkewPolynomial (n+2)) ≠ 0 := by
  intro h
  have hs := OddMath.SkewPolynomial.generator_square_ne_zero j
  change (generator j * generator j : SkewPolynomial (n+2)) ≠ 0 at hs
  exact hs (by rw [h, zero_mul])

/-- A zero quotient would make this concrete nonzero image vanish. -/
theorem dot_ne_zero (n : ℕ) (j : Fin (n+2)) : dot n j ≠ 0 := by
  intro h
  have he := action_dot_one n j
  rw [h, map_zero, LinearMap.zero_apply] at he
  exact generator_ne_zero n j he.symm

noncomputable instance presentedNontrivial (n : ℕ) : Nontrivial (Presented n) :=
  ⟨⟨dot n 0, 0, dot_ne_zero n 0⟩⟩

end OddMath.Frontier.NilHeckeAction
